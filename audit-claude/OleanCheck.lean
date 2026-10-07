import Lean

/-!
What do the compiled modules of the supplement add to Lean itself? (Auditor's script; not
part of the archive, and not part of the supplement library.)

    lake env lean -DautoImplicit=false -DwarningAsError=true audit-claude/OleanCheck.lean

This file does not import the supplement. It reads the compiled modules `R56Audit` and
`R56Audit.*` as data (`Lean.readModuleData`) and checks that the only environment extensions
that received entries from them are those on the list below: declarations and their
documentation, the recorded axioms, compiled code, the automatic entries of an inductive type,
of `match` and of `abbrev`, instances, simp lemmas, and statistics. In particular no module
adds a parser, a macro, an elaborator, a notation, a coercion, a class, an alias, an
`implemented_by`/`extern` entry or an initializer. So importing the supplement cannot change
how the other check scripts are parsed or elaborated, except through its instances, simp
lemmas and reducibility attributes, and through the names it declares;
`SupplementAudit.lean` lists the first three and compares them with the expected ones, and
checks that the names cannot be confused with other names that the scripts use.
-/

open Lean Elab Command

namespace AuditScripts.Olean

/-- Environment extensions that may receive entries from a supplement module. -/
def allowed : List String := [
  -- declarations: source ranges, documentation, namespaces, `protected`, `noncomputable`
  "Lean.declRangeExt", "Lean.docStringExt", "_private.Lean.DocString.Extension.0.Lean.moduleDocExt",
  "_private.Lean.Namespace.0.Lean.namespacesExt", "Lean.protectedExt", "Lean.noncomputableExt",
  "Lean.Meta.completionBlackListExt", "Lean.deprecatedModuleExt",
  "_private.Lean.Compiler.ModPkgExt.0.Lean.modPkgExt", "_private.Lean.ExtraModUses.0.Lean.extraModUses",
  -- the axioms of each declaration, recorded when the module was compiled
  "_private.Lean.Util.CollectAxioms.0.Lean.exportedAxiomsExt",
  -- compiled code of definitions (not used by the kernel)
  "Lean.Compiler.LCNF.UnreachableBranches.functionSummariesExt", "Lean.Compiler.LCNF.baseExt",
  "Lean.Compiler.LCNF.impureSigExt", "Lean.Compiler.LCNF.monoExt", "Lean.Compiler.LCNF.monoTypeExt",
  "Lean.Compiler.inlineAttrs", "Lean.IR.declMapExt",
  "_private.Lean.Compiler.LCNF.MonoTypes.0.Lean.Compiler.LCNF.trivialStructureInfoExt",
  "_private.Lean.Compiler.LCNF.Specialize.0.Lean.Compiler.LCNF.Specialize.specCacheExt",
  "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.ctorLayoutExt",
  "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTrivialStructureInfoExt",
  "_private.Lean.Compiler.LCNF.ToImpureType.0.Lean.Compiler.LCNF.impureTypeExt",
  -- automatic entries of an inductive type, of `match`, of `abbrev`, and of `rfl` theorems
  "Lean.auxRecExt", "Lean.noConfusionExt", "_private.Lean.AuxRecursor.0.Lean.sparseCasesOnExt",
  "Lean.Elab.Term.elabAsElim", "Lean.Meta.Match.Extension.extension", "Lean.Meta.congrKindsExt",
  "Lean.Meta.Grind.grindExt", "reducibilityCore", "Lean.defeqAttr", "Lean.backwardDefeqAttr",
  -- instances and simp lemmas: listed and compared in `SupplementAudit.lean`
  "Lean.Meta.instanceExtension", "Lean.Meta.simpExtension",
  -- statistics for premise selection
  "sineQueNon", "symbolFrequency"]

run_cmd do
  let mut todo : List Name := [`R56Audit]
  let mut seen : NameSet := {}
  let mut constants := 0
  let mut used : Std.HashMap String Nat := {}
  while !todo.isEmpty do
    let m := todo.head!
    todo := todo.tail!
    if seen.contains m then continue
    seen := seen.insert m
    let (data, _) ← readModuleData (← findOLean m)
    constants := constants + data.constNames.size
    for imp in data.imports do
      if (`R56Audit).isPrefixOf imp.module then todo := imp.module :: todo
    for (ext, entries) in data.entries do
      if entries.size > 0 then
        unless allowed.contains (toString ext) do
          throwError "module {m} adds {entries.size} entries to the extension {ext}"
        used := used.insert (toString ext) (used.getD (toString ext) 0 + entries.size)
  IO.println s!"OLEAN CHECK: {seen.size} modules, {constants} constants; entries only in {used.size} of the {allowed.length} allowed extensions (instances: {used.getD "Lean.Meta.instanceExtension" 0}, simp lemmas: {used.getD "Lean.Meta.simpExtension" 0}, reducibility attributes: {used.getD "reducibilityCore" 0})"

end AuditScripts.Olean
