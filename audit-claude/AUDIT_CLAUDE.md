> Historical report for the supplied Claude audit archive. Its archive layout, hash lists, and r56 integration remarks describe that input, not the current r65 repository. See ../AUDIT_R65.md and PROVENANCE.json for the current integration.

# Tusnády r65：Lean 归档审计（第二版）

- 归档：`tusnady-r56-lean-verified.zip`，sha256 `ca4eecc2…e3be`，90 个文件。源码、脚本、记录均未改动。稿件 AI 声明所指的应是它；声明里的公开仓库打不开，无法核对（见下）。
- 稿件：`tusnady-plane-stoc27-vC-r65.tex`，sha256 `2c3f3f16…2460`。定理号、式号按该稿。
- 环境：Lean 4.34.1，Mathlib v4.34.1，Linux x86-64。日期 2026-10-07。
- 审计者：Claude。新增的是补充库 `R56Audit/`（32 个模块）与 `R56Audit.lean`、本目录 `audit-claude/`；被改动的归档文件只有 `lakefile.toml`，末尾追加 `[[lean_lib]] name = "R56Audit"`。库名沿用上一版，指"对 r56 归档的审计"；内容已按 r65。

## 结论

### 一、归档与 r65 是否一致

**一致，结论与对 r56 相同。**

1. r56 → r65：10 条编号陈述里 9 条逐字未变，18 个编号公式全部未变。唯一的陈述改动是 Lemma 2.4 加了 "almost surely"。Theorem 1.1 与 Corollary 1.2 逐字相同。
2. 归档验证的正是 Theorem 1.1 和 Corollary 1.2 的下界方向，所以它对 r65 的效力不变：**结论过了内核；证明路线不是稿件写的那条**（偶数底、有限探针势函数、Rademacher 形式的局部增益）。这一点上一版报告已说明。
3. r65 的 AI 声明改成 "A Lean formalization of **the main lower-bound theorem** was produced with GPT"。这句话与归档相符。r56 写的是 "of the proof"，说多了；现在是对的。

三件事需要处理：

- **仓库地址打不开。** 声明里的 `https://github.com/wzskytop/tusnady-lean`，我在 10 月 7 日匿名访问得到 404；账号主页列出的公开仓库是 TopPPR、PRSim-Code、academic-kickstart、academic-kickstart1，没有它。仓库应是私有或尚未建立。公开之前，"is available at" 不成立；我也无法核对公开版本是否就是这份归档。
- **归档的文档和记录只认 r56。** `README.md`、`PROOF_MAP.md`、`AUDIT_R56.md`、`verification/manuscript-r56.json` 里的稿件哈希，以及 `scripts/verify.py`、`scripts/package.py` 里写死的文件名，都指向 r56。
- **归档里的注释有不少指向旧稿，我看到的至少十六处，没有穷举。** 编号或说法对不上 r65 的：`Oscillation/DirectScale.lean` 的 "Proposition 3.1"，`Oscillation/R17LocalFacts.lean` 的 "Fact 2.3"，`Riesz/Exponential.lean` 的 "Section 4"，`Oscillation/PaperGoodTransitions.lean` 的 "Proposition 2.4, equation (9)" 和 "at least half the transitions satisfy G_j"，`Riesz/Dyadic.lean` 的 "Section 2 of the manuscript"。另有十处说旧路线里的某个对象是稿件的（"the manuscript's …"、"the paper's …"、"… from the manuscript" 等），这些对象或提法 r65 里已经没有：`Riesz/UniformGrid.lean`（w_L）、`Riesz/Dyadic.lean`、`Riesz/Moments.lean` 两处与 `Riesz/WeightedMoments.lean`（one-rectangle Laplace 估计）、`Riesz/Occupancy.lean` 两处、`Oscillation/Accumulation.lean`、`Oscillation/Stages.lean`（compensated exponential estimate）、`Oscillation/HistogramTransport.lean`。

r65 第 3 节新增的两处断言（在线差异 Ω(log^{3/2} T)；Bansal 猜想在 d = 2 不成立）是 Theorem 1.1 加文献引用，不在 Lean 的范围内。被引文献的内容我没有核对。

### 二、补充库：稿件写的那个证明，现在过了内核

上一版留下的差别这次都补上了：

| 上一版缺的 | 现在 |
|---|---|
| 势函数取在有限高度网格上 | `Zpot`：(1) 式，极值取遍整个竖直区间 |
| 没有 𝓕_j、T | `digitSigma`（原文定义：高度加前 j 位数字）、`fluctDigits` |
| Lemma 2.4、2.6 只有探针形式 | `lemma_2_4_digits`、`lemma_2_6_digits`，原文陈述。Lemma 2.6 的三步按稿件；逐次取条件与 Markov 不等式只用 Mathlib（`SuccessiveConditioning.lean`） |
| Proposition 2.7、Theorem 1.1 走归档的补偿指数路线 | `proposition_2_7`、`theorem_1_1`：(10) 式分解 + Lemma 2.4 + 2.5 + 2.6，用的就是 𝓕_j 和 T 的原文陈述 |
| Fact 2.2、Fact A.1 只有有限情形 | `fact_2_2_general`、`fact_A_1`：一般概率空间上的随机变量 |
| Lemma 2.5(ii) 借归档的估计 | `lemma_2_5_ii`：稿件自己的证明（W_𝒮、E_𝒮、对重区域的集合取并） |
| Lemma 2.1 借归档的代数内核 | 直接证明，只用 Mathlib |
| 证明里的中间式子多数只在证明内部 | 每个编号公式都有单独的声明；证明各步的结论绝大多数也有。`Gates.lean` 按稿件顺序钉住 266 条陈述。只在证明内部出现的中间结论和句内理由，见下文第 9 点 |
| (18) 式非严格，(16) 式用归档的引理 | `display_16`、`display_17`、`display_18`，M > n 与 M ≤ n 两种情形都按稿件 |

规模：33 个文件（32 个模块加一个只含导入和说明的根文件），10,308 行，521 条定理，84 个定义和 1 个归纳类型；连同自动生成的辅助项共 907 个常量。全部无警告，只依赖 `propext`、`Classical.choice`、`Quot.sound`，32 个模块内核重放通过。

`Gates.lean` 末尾由机器检查证明路线。`theorem_1_1`、`theorem_1_1_unfolded`、`theorem_1_1_constant`、`theorem_1_1_constant_event`、`exists_points`、`corollary_1_2_lower` 六条都：

- **经过** 28 条指定的声明：稿件的编号陈述和证明的步骤，包括 `proposition_2_7`、`roadmap_digits`、`lemma_2_4_digits`、`local_gain`、`vertical_comparison`、`fact_2_2_general`、`lemma_2_5_i`、`lemma_2_5_ii`、`lemma_2_5_ii_all`、`lemma_2_6_digits`、`fact_A_1`、`Zstep_update_le`、`display_16`、`display_17`、`display_18`，以及两种 σ-域之间的桥 `condExp_digitSigma`；
- **不经过** 33 个指定的声明，包括归档的 `gridPotential`、偶数底局部增益、`badSet`、`GoodEvent`、`integral_prefixProduct_le_of_cond`，也不经过 `Oscillation.Direct`、`Oscillation.R56` 两个命名空间里的任何声明；
- 用到的归档内容**全部落在 8 个模块内**（见第 10 点）。

### 三、仍有的差别

1. **没有形式化的**：Corollary 1.2 的上界（Nikolov，引用）；第 3 节的断言，包括 a^{(I)} = E[|I|⁻¹∫_I F dx | 𝓕_j]；引言里关于密度 n/M 的讨论。第 2 节里的几句说明性文字也没有对应陈述："All intervals of Section 2.4 have endpoints of this form"；Lemma 2.1 后关于 offset 的解释；Fact 2.2 前与 Khintchine 不等式的比较；2.3 节末 "about (1−2/b)n points … of order √n" 及所引的 O(log^{3/2} n)；"δ_j would be about (1/(4b))√(n/M)"；参数一节关于 b⁻⁴ 不够的说明。
2. **σ-域。** Proposition 2.7 用的是 𝓕_j = `digitSigma` 的陈述。这三条陈述（(10) 式、Lemma 2.4、Lemma 2.6）是从 `stageSigma` 的同名陈述推出来的：`stageSigma` 由高度和每个横坐标所在的第 j 级区间编号生成。在 2.1 节的概率 1 事件上两组生成元互相决定，所以条件期望几乎必然相等（`condExp_digitSigma`）。
3. **"Z_j 是 𝓕_j-可测的"** 形式化为几乎必然等于一个 𝓕_j-可测函数（`Zpot_aestronglyMeasurable_digits`）。逐点的可测性在零测集上不成立：点落在网格线上时，数字决定的是左闭右开的区间，而 F 按闭矩形计数。稿件本来就限定在概率 1 事件上。
4. **Fact 2.2。** 多写一条假设 `h4i`：X_i⁴ 可积。这是 "E X_i⁴ ≤ 3σ⁴" 本来的意思；Lean 里不可积函数的积分记为 0，不写出来反而会改变命题。证明里"两个矩"一步是按变量个数归纳（`sum_moments`），不是展开 X⁴ 后数项；稿件的 6Σ_{i<j} E X_i² E X_j² 以 3m(m−1)σ⁴ 的形式出现。
5. **Fact A.1。** ξ_i 取值在同一个可测空间 E；稿件的实值随机变量是 E = ℝ，Lemma 2.6 用的是 E = {0,…,b−1}。证明对乘积测度逐个坐标积分，没有把鞅差 Y_i 写成随机变量；这与逐步取条件期望是同一个论证。"One difference" 按稿件的条件期望形式另有陈述（`condExp_exp_le_cosh`），但 Fact A.1 的证明用的是它的无条件形式（`integral_exp_le_cosh`）。
6. **局部试验**（Lemma 2.3）写成对全部 r ∈ {1,…,b}ⁿ 的均匀平均。I 外的点的 r_i 不进入任何量。它与真实概率空间的联系在 Lemma 2.4 的证明里：给定区间编号，下一位数字独立均匀（`condExp_fresh_given_heights`）。`condExp_nextDigits` 是这句话对 𝓕_j 的重述，不在主链上。
7. **Lean 的假设有几处比稿件弱**：Lemma 2.1、2.3、2.4 只要 b ≥ 2；Lemma 2.3 不要求高度互异；Lemma 2.5(i) 对任意点集成立，带 `0 < n`，对应稿件的 n ≥ 1；Lemma 2.6 对所有 h、n 陈述，h = 0 或 n = 0 时右端是 1，平凡。
8. **M、G 没有单独的名字**，写作 `b ^ (h - 1)` 与 `{P | ∀ j < h, GoodTransition b h j P}`。
9. **两层陈述，哪些陈述不在主链上，粒度。** 一些步骤先对一般对象证明，再写成稿件的形式：Lemma 2.1 和 Lemma 2.3 的各式先对"任意高度集合"，再对区间的块；条件增益和波动估计先对"高度与区间编号的函数" `Zstep`，再对 Z_j 与 𝓕_j。所以 266 条钉住的陈述里，205 条在 Theorem 1.1 或 Corollary 1.2 的依赖里，另外 61 条不在。`Gates.lean` 的输出列出这 61 条：
   - 由主结论推出的 `theorem_1_1_unfolded`，和与主链并列的 `one_rectangle`（2 条）；
   - 稿件形式的重述，由链上的定义或一般形式推出（5 条）：`display_5`、`offset_eq`、`withoutJumps_eq`、`lemma_2_6_step2`、`condExp_nextDigits`；后两条还各用到下面"说明对象或假设"一类里的一条（`fluctTerm_ae_eq`、`nextDigits_ae_eq_freshInfo`）；
   - 稿件里有、这里的证明没有以那种形式用到的（7 条）：`ae_setupEvent`（证明分别用高度互异、`ae_noGrid`、`ae_inUnit`）、`display_6`、"Z_j 是 𝓕_j-可测的"两条、面积等式 `volume_boundaryStrips`（证明只需要上界）、"One difference" 的条件期望形式两条；
   - Lemma 2.3 对任意高度集合的形式（3 条）：`local_gain_core`、`local_gain_sets`、`expected_offset_core`，只有归档探针路线的 `GridDrift` 用到；
   - 说明对象或假设是什么的（5 条）：`childAvg_eq_F`、`nextDigits_ae_eq_freshInfo`、`fluctTerm_ae_eq`、`inUnit_of_noGrid`、`exists_symm_perm_iff`；
   - 集合层面的几何与计数（22 条），事件与函数的可测性（7 条），极值可达（3 条），Fact A.1 设定下的可积性（1 条）；
   - 关于归档路线的 6 条。

   粒度：稿件每个编号公式都有单独的声明；证明里各步、各句的结论绝大多数也有（少数有声明但没有列入 `Gates.lean`，如 `childMean_eq_withoutJumps_of_lt`、`mem_Wset_heavySet`、`sum_innerCount_le`）。只在证明内部出现、没有单列的中间结论和句内理由，我对照时记下的有：
   - (3) 式一段：有限和的三角不等式稿件说 "By induction"，`osc_sum_le` 是直接证的；
   - Lemma 2.3：第 2 步权重式的左端 ((b−r)+½)/b；第 3 步展示式里的两个等号；第 4 步的 "16(b²−1) ≥ 9b²"；
   - (9) 式："every oscillation is at most 2‖F‖∞"；
   - Lemma 2.4：恒等式 bM(Z_{j+1}−Z_j) = Σ_R(…) 以两半的形式陈述（`Zstep_eq_sum_blocks`、`Zstep_succ_eq_sum_children`）；
   - Lemma 2.5(i) 的不等式链；Lemma 2.5(ii) 的 "at most 2ⁿ sets of indices"、"(3/b)^{⌈n/2⌉} ≤ (3/b)^{n/2}"、"2^{M+n} ≤ 4ⁿ = 16^{n/2}"；
   - Lemma 2.6：第 1 步的 "Hence the endpoint average of each child changes by a multiple …"；第 3 步的等式 Pr(T ≤ −λ) = Pr(e^{−tT} ≥ e^{tλ})；
   - Proposition 2.7："in particular T ≤ −λ"；
   - Fact 2.2："|θ+x| + |θ−x| ≥ 2|x|"、"trivial for m = 0"、Hölder 一行的中间项；
   - Fact A.1：鞅差 Y_i 及 |Y_i| ≤ c；(2k)! ≥ 2^k k!。

   这份清单是人工对照的，不保证穷尽。
10. **仍用到归档的 8 个模块。** 多数是基础设施：点的分布 `unifPts` 及其坐标分解，两个零测事件（`ae_pointSampleLaw_mem_Ioc`、`diag_null`），有限平均 `finAvg`，区间编号 `gridIndex`，下一位数字 `freshGridIndex`，以及它们的可测性。**一处是稿件的数学断言**："The (j+1)-st digits … are independent and uniform conditional on 𝓕_j" 用的是归档的 `condExp_freshGrid_with_past`，补充库没有重证；稿件对这句话也没有给证明。Corollary 1.2 另用归档的 `Δ₂` 及其几条初等引理。Lemma 2.1、Fact 2.2、Lemma 2.5(i)、Fact A.1 和 `SuccessiveConditioning` 只用 Mathlib。清单由 `Closure.lean` 列出。
11. **几何的两处写法。** 格和比较矩形的个数是按下标集合数的（`card_cells_stage`、`card_compRect`）。竖直区间下闭上开，所以各级的格铺满的是 [0,1] × [0,1)，高度恰为 1 的点不在任何格里；这是零测事件。
12. **"一个矩形给出什么"**（`one_rectangle`）是由 Lemma 2.4 取 h = 1 再加 (9) 式得到的，不是直接从 Lemma 2.3 推。内容相同。

## 1 编译与可信性

除最后一行外，每一行都是 `check.sh` 的一步，失败即停。脚本最后把各步的摘要行与 `expected-summary.txt` 逐行比对（114 行），所以表里的数字是被检查的，不只是被打印。文件完整性一步除外：它的输出不进摘要，没有哈希清单或带 `--record` 时这一步跳过。交付目录顶层的 `logs/check.log` 是在干净副本上、不带 `--record` 跑完的完整记录。

| 检查 | 结果 |
|---|---|
| 文件完整性（`archive.sha256`、`files.sha256`） | 归档的 89 个文件与被审计的 zip 相同；`lakefile.toml`、补充库和本目录的文件与交付时相同 |
| 全量编译 `lake build Oscillation R56Audit` | 归档 58 个模块，补充库 33 个（含根模块），0 error |
| 补充库逐个模块严格重编（`unusedVariables`、`unusedSectionVars`、`unusedSimpArgs`） | 33 个模块，无任何输出 |
| 源码扫描 `scan.py` | 补充库无 `sorry`、`axiom`、`native_decide`、`unsafe`、`partial`、元代码、宏、记号、以 `#` 开头的命令、`set_option`、`instance`、属性（`@[…]`、`attribute`）、`_root_`、带引号的标识符；一个归纳类型 `Side`（左、内、右），带 `deriving DecidableEq`；字母限于白名单。归档库的实例、结构、选项、属性与记录的相同 |
| 编译产物 `OleanCheck.lean`（不导入补充库，把 `.olean` 当数据读） | 33 个模块只向 37 类环境扩展写入条目：声明及其位置与文档、编译时记录的公理表、编译代码、归纳类型与 `match` 与 `abbrev` 的自动条目、实例、simp 引理、统计信息。没有语法、宏、繁饰器、记号、强制转换、类、别名、`implemented_by`、初始化器 |
| 环境 `SupplementAudit.lean` | 907 个常量：定理 801，定义 101（其中写在源码里的是 521 条定理、84 个定义），`Side` 及其 3 个构造子和 1 个递归子；无 `axiom`、`opaque`、`unsafe`、`partial`、`implemented_by`、`extern`。实例 2 个、simp 引理 3 个、reducible 定义 13 个、instance-reducible 定义 4 个：`Side` 自动生成的，4 个 `abbrev`，2 个 `match` 的辅助项。声明名只含 ASCII、`Δ`、`₂` |
| 命名空间与重名（同一脚本） | 903 个常量在 `R56Audit` 里；另外 4 个是 Lean 为别的模块的定义按需生成的引理（3 条等式引理 `.eq_1`，1 条同余引理 `.congr_simp`）。补充库的名字去掉前缀后，与根命名空间或检查脚本打开的命名空间里的声明或导出别名重名的有 8 个，都在预期清单里：`maxOn`、`minOn` 与核心库的函数重名，其余 6 个与归档重名。`maxOn`、`minOn` 在陈述 gate 里不带前缀出现，读错会使 `rfl` 失败，定义 gate 里写的是全名；其余 6 个名字，检查脚本只带前缀使用或不使用 |
| 公理，两种方法 | `#print axioms` 的方法逐个查 907 个常量；另外沿证明项遍历 51,195 个常量（含 Mathlib 与核心库），不读编译时缓存的公理表。两者都只得到 `propext`、`Classical.choice`、`Quot.sound` |
| 内核重放 `leanchecker` | 32 个模块逐个通过（根模块没有声明） |
| 陈述 gate（`Gates.lean`，警告视为错误） | 353 个 `example`，在去掉注释的文件上计数：266 条陈述用 `(陈述) = type_of% @T := rfl` 双向钉住；80 个定义 gate，覆盖 83 个名字，其中 78 个是 `rfl` 展开，`Side` 与归档的 `freshGridIndex` 各用一条证明了的事实刻画；4 对"两条陈述相同"；3 条小事实 |
| 阅读清单（`Gates.lean` 末尾） | `theorem_1_1_unfolded` 的陈述不含任何项目定义。归档路线一节之外的 260 条陈述 gate 里出现的补充库与归档的定义，连同这些定义的定义体里出现的，共 82 个，每个都有定义 gate。哪个 `example` 是哪个定义的 gate，由模板里的 `--@def` 标注给出，`mkgates.py` 检查该 `example` 的陈述以这个名字开头，并据此生成清单。等式成立由 `rfl` 保证；写出的定义体对不对，要靠人读 |
| gate 的反向测试（`mutants.py`） | 改动一个假设、常数、不等号或区间端点，共 52 处（40 处陈述、12 处定义），每一处都在各自的 `rfl` 上被拒绝；3 个未改动的对照通过 |
| 归档本身（`ArchiveAudit.lean`、`MainTheoremClosure.lean`，与上一版相同） | 结果与上一版相同。唯一被标出的常量是 `Riesz.Moments.SampleSpace._unsafe_rec`：编译器为递归定义自动生成的辅助项，没有常量引用它 |
| 归档自带 `scripts/verify.py --replay`（不在 `check.sh` 里） | 在同一份干净副本里、`check.sh` 跑完之后运行，通过（`logs/archive-verify.log`）。它会改写 `verification/` 下的记录，所以交付的目录里没有运行它 |

266 条陈述 gate 的文本由 `mkgates.py` 从去掉注释的源码抄出，`check.sh` 每次重新生成并比对。gate 保证的是"库里的陈述与 `Gates.lean` 里写的那句话定义上相等"。**那句话是否等于稿件的话，要靠人读**；我的读法记在第 2 节，`Gates.lean` 按稿件顺序排列，可以对着 PDF 读。独立复核做了三轮，第一轮四位，第二轮两位，第三轮一位（只核对第二轮之后的改动）；指出的问题都已处理。第二轮之后的改动是：`lemma_2_5_ii_all` 改由 `lemma_2_5_ii` 推出（陈述未变），`Crowding.lean`、`Fluctuations.lean`、`R56Audit.lean` 三处说明文字的更正，检查脚本加固（阅读清单、重名检查、文件完整性、扫描规则），以及本报告的更正。第三轮之后又改了几处，只经过 `check.sh`，没有再复核：`ArchiveInterface.lean` 里的 `toBool` 改名为 `colorBool`（它与核心库导出到根命名空间的别名重名），重名检查加上导出别名，`freshGridIndex` 的刻画去掉 k > 0 的假设，`Side` 的三个构造子互异，`--@def` 标注的检查收紧，以及第三轮指出的措辞。

## 2 逐条对照

三问：Lean 是否**加了条件**、**减了结论**、**换了对象**。"无"表示三问都没有。证明的各步见 `Gates.lean` 相应小节。

| 稿件 | Lean | 三问 |
|---|---|---|
| F_χ、‖F_χ‖∞ | `F`、`supNorm` | 无。着色是 `Fin n → ℤˣ`；上确界可达（`exists_eq_supNorm`） |
| **Theorem 1.1** | `theorem_1_1`；`theorem_1_1_unfolded` 不含任何项目定义 | 无。事件可测（`measurableSet_forall_le_supNorm`） |
| 定理后的 "there is an n-point set …" | `exists_points` | 无；略强：点互异，严格不等号 |
| **Corollary 1.2** | `corollary_1_2_lower` | 只有下界。`Δ₂` 是归档的定义：n 个互异点，闭矩形，与稿件一致 |
| 2.1 节的概率 1 事件 | `SetupEvent`、`ae_setupEvent` | 无 |
| (2) 式，端点平均 | `endAvg`、`endpointAvg_eq_F` | 加：坐标非负（单位正方形内恒成立）。区间左端点上的点算作"在 I 左边"；稿件说端点不影响 |
| (3) 式，osc、mid 及其性质 | `osc`、`mid`、`maxOn_eq_mid_add`、`osc_const_mul`、`osc_add_const`、`mid_add_const`、`maxOn_add_le`、`add_minOn_le`、`osc_add_le`、`osc_sum_le`、`osc_neg`、`osc_le_osc_add_add`、`abs_osc_add_sub_le` | 无。`osc` 用 sup − inf 定义；取有限个值时就是 max − min（`maxOn_mem`、`minOn_mem`） |
| **Lemma 2.1**，(4) 式及其证明 | `vertical_comparison`；`maxOn_sub_minOn_le_osc`、`maxOn_sub_minOn_eq`、`half_osc_add_abs_mid_sub_le`、`osc_mono` | 无；b ≥ 2 即可 |
| **Fact 2.2** 及其证明 | `fact_2_2_general`；`integral_abs_add_eq_integral_abs_sub`、`integral_abs_le_integral_abs_add_of_symm`、`sum_moments`、`sum_fourth_moment_le`、`integral_sq_le_rpow_mul_rpow` | 多一条 X_i⁴ 可积；"两个矩"用归纳（见上文第 4 点） |
| **Lemma 2.3**，(5)–(8) 式 | `local_gain`；`display_5`、`display_6`、`finAvg_childMean`、`display_8` | 无；b ≥ 2，不要求高度互异。期望是对子区间编号的均匀平均 |
| Lemma 2.3 第 4 步 | `offset_eq`；`jump_sq_eq`、`finAvg_childIndex`、`finAvg_childIndex_sq`、`finAvg_childIndex_var`、`finAvg_jump_sq`、`finAvg_jump_fourth_le_sq`、`sq_mul_sigma_sq_le`；`expected_offset_ge_sigma`、`sigma_mul_sqrt_eq`、`sqrt_sq_sub_one_div_ge`、`expected_offset_ge` | 无。对其余点的子区间取条件，写成偏移 θ 可依赖其余数字（`symmetric_sum_abs`） |
| 2.3 节末，一个矩形 | `one_rectangle` | 无。"高度固定"写成给定高度的条件期望，几乎必然；由 Lemma 2.4 得到（第 12 点） |
| 阶段、格、比较矩形、内部区域 | `hcell`、`vcell`、`cell`、`compRect`、`innerRegion`；`iUnion_cell`、`compRect_eq_iUnion_old`、`compRect_eq_iUnion_new`、`innerRegion_eq_diff` | 无。横向区间闭，竖向下闭上开，与稿件相同（第 11 点） |
| (1) 式 Z_j，(9) 式 | `Zpot`；`Zpot_nonneg`、`Zpot_le_two_supNorm` | 无；对每个点集成立，不只是几乎必然 |
| 𝓕_j；"Z_j 是 𝓕_j-可测的" | `digitSigma`；`Zpot_aestronglyMeasurable_digits` | 可测性是几乎必然意义下的（第 3 点） |
| "下一位数字给定 𝓕_j 独立均匀" | `condExp_nextDigits`；证明里用 `condExp_fresh_given_heights` | 无。写成：下一位数字的有界函数的条件期望等于对数字的均匀平均。证明取自归档（第 10 点） |
| (10) 式 | `roadmap_digits` | 无；几乎必然 |
| **Lemma 2.4**，(11) 式 | `lemma_2_4_digits`；`Zstep_eq_sum_blocks`、`Zstep_succ_eq_sum_children`、`Zstep_gain` | 无；b ≥ 2 |
| 重、好转移、δ_*，(12) 式 | `Heavy`、`GoodTransition`、`deltaStar` | 无 |
| **Lemma 2.5** (i) | `lemma_2_5_i` | 无；对任意点集，不需要 j < h |
| **Lemma 2.5** (ii) 及其证明 | `lemma_2_5_ii`、`lemma_2_5_ii_all`；`card_heavySet_lt`、`half_lt_card_Wset`、`volume_boundaryStrips`（面积等于 2/b）、`volume_innerRegions_lt`（小于 1/b）、`volume_Wset_le`、`unifPts_crowdEvent_le`、`unifPts_bad_le` | 无 |
| **Lemma 2.6**，(13) 式 | `lemma_2_6_digits`；第 1 步 `Zstep_update_le`；第 2 步 `condExp_exp_step`、`lemma_2_6_step2`；第 3 步 `fluctTerm_measurable_of_lt`、`integral_prod_le_of_condExp_le`、`lemma_2_6_step3`、`measureReal_le_exp_mul_integral_exp_neg`、`lemma_2_6_markov` | 无。事件可测（`measurableSet_fluctDigits_le`）。各步对 `stageSigma` 陈述，结论对 𝓕_j |
| **Proposition 2.7**，(14) 式 | `proposition_2_7`；`condGain_ge_deltaStar`、`Zpot_ge_of_good`、`Zpot_le_of_small`、`fluct_le_of_good`、`exponent_eq`、`good_inter_small_le`、`prob_exists_small_le`、`threshold_eq` | 无 |
| (15) 式与 c_A | `exists_base_of_15`、`base_ge_49`、`sixty_four_le_pow_four`、`cA` | 无 |
| h 的选取，(16)–(18) 式 | `IsScale`、`exists_isScale`、`lt_of_isScale`、`display_16`、`lt_two_mul_pow_of_isScale`、`display_17`、`display_18` | 无 |
| Theorem 1.1 的证明，M > n | `scale_lt_pow_five`、`cA_mul_lt_of_lt`、`inv_pow_eight_mul_rpow_lt_one`、`cA_mul_lt_one`、`one_le_supNorm`、`ae_cA_mul_lt_supNorm` | 无 |
| Theorem 1.1 的证明，M ≤ n | `scale_le_of_pow_le`、`first_term_le_mul`、`exponent_gt`、`exponent_ge`、`second_term_le`、`sum_terms_le`、`add_one_mul_exp_le`、`failure_le`；`threshold_ge_sqrt`、`threshold_sqrt_eq`、`rpow_div_ge`、`threshold_gt`；`theorem_1_1_constant` | 无。`theorem_1_1_constant` 对任何满足 (15) 的整数 b 成立，常数就是 c_A |
| **Fact A.1** 及其证明 | `fact_A_1`、`fact_A_1_integrable`；`fact_A_1_freeze`、`abs_sub_le_of_bounded_differences`、`bounded_differences_pi`、`exp_mul_le_chord`、`integral_exp_le_cosh`、`cosh_le_exp_sq_half`、`condExp_exp_le_cosh` | ξ_i 同值域；证明的组织见上文第 5 点 |

除 σ-域外，还有五处是桥接而不是字面：

- **势函数**：`Zpot` 由 F 定义；证明里用 `Zstep`，它是高度与区间编号的函数。两者在坐标非负时逐点相等（`Zpot_eq_Zstep`）。条件期望 E[Z_{j+1} | 𝓕_j] 在证明里写成对下一位数字的平均 `Zmean`，T 相应地写成 `fluctStep`（`fluct_ae_eq`、`fluctDigits_ae_eq`）。
- **δ_j 与 m_R**：`delta`、`innerCount` 按闭区域数点；证明里用按区间编号数点的 `deltaStep`、`innerSet`。两者在概率 1 事件上相等（`delta_eq_deltaStep`）。
- **下一位数字**：`nextDigits` 是第 j+1 位数字；证明里用归档的 `freshGridIndex`。两者几乎必然相等（`nextDigits_ae_eq_freshInfo`）。
- **a 与 a_k**：Lemma 2.3 用按权重定义的 `endpointAvg`、`childAvg`；它们就是由 F 定义的端点平均（`endpointAvg_eq_F`、`childAvg_eq_F`）。
- **点的分布**：定理用 `unifPts`（单位正方形上均匀测度的 n 重乘积）；条件期望的计算用两个坐标分开的乘积 `pointSampleLaw`。两者相等（归档的 `pointSampleLaw_eq_unifPts`）。

## 3 补充库的模块

| 稿件 | 模块 |
|---|---|
| 第 1 节 | `Notation`、`SupNorm`、`Parameters` |
| 2.1 | `GoodTransitions`（概率 1 事件）、`Osc`、`StepOsc`、`EndpointAverage` |
| 2.2 | `Osc` |
| 2.3 | `SymmetricSumsGeneral`、`UniformDigits`、`SymmetricSums`、`LocalGain`、`OneRectangle` |
| 2.4 | `StageGeometry`、`Potential`、`Measurability`；`StageFiltration`、`ConditionalLaw`、`Digits`、`CondExpGenerators`；`StageGain`、`ConditionalGain`；`GoodTransitions`、`Crowding`；`Influence`、`SuccessiveConditioning`、`Fluctuations`；`Simultaneous` |
| 2.5 | `Parameters` |
| 附录 A | `SymmetricSumsGeneral`、`BoundedDifferencesGeneral` |
| 关于归档的路线，主结论不依赖 | `ArchiveInterface`、`ArchiveRoute`、`GoodTransitionsArchive`、`GridDrift`、`AllBases` |

Theorem 1.1 的依赖里有 24 个模块（`Closure.lean` 列出）。不在其中的，除最后一行的五个外，还有 `StageGeometry`（格与比较矩形的集合关系）、`Measurability`（Z_j 与 T 逐点的可测性）、`OneRectangle`：它们是稿件里另外的陈述，证明不需要。

最后一行的五个模块保留了上一版的结果：归档的定理用 F_χ、‖F_χ‖∞ 重述；归档的好转移事件几乎必然就是 G_j；归档的有限探针证明去掉奇偶限制后给出 (14) 式的第二个证明 `proposition_2_7_probe`。`ArchiveInterface` 里只有 `lt_Δ₂_of_supNorm` 被 Corollary 1.2 用到。

## 4 与上一版审计包的差别

| 上一版 | 现在 |
|---|---|
| `theorem_1_1`、`corollary_1_2_lower`、`proposition_2_7`（归档定理的改写） | `theorem_1_1_archive`、`corollary_1_2_lower_archive`、`proposition_2_7_archive` |
| `theorem_1_1_any_base`、`corollary_1_2_lower_any_base` | `theorem_1_1`、`corollary_1_2_lower` |
| `proposition_2_7_all`（探针路线） | `proposition_2_7_probe`；`proposition_2_7` 现在指稿件路线的证明 |
| `lemma_2_5_ii`、`lemma_2_5_ii_all`（借归档的估计） | `lemma_2_5_ii_archive`、`lemma_2_5_ii_all_archive`；原名现在是稿件自己的证明 |
| `innerRegion` 左开右闭；`mem_innerRegionClosed_iff` | 按稿件：横向闭，竖向下闭上开；与左开右闭的比较是 `mem_innerRegion_iff_Ioc` |
| `theorem_1_1_event`、`exists_points_anchored` | `theorem_1_1_event_archive`、`exists_points_anchored_archive` |
| `logb_two_lt_of_scale`、`cA_mul_le`（后者非严格） | `display_17`、`display_18`（都严格） |
| `MainTheorem.lean` | 删去，内容分入 `ArchiveInterface.lean` 与 `ArchiveRoute.lean` |
| 12 个文件，3,310 行 | 33 个文件，10,308 行 |

## 5 建议

1. 公开仓库，并把归档的文档、稿件哈希记录更新到 r65。
2. 如果把补充库并进仓库：AI 声明里 "produced with GPT" 不再覆盖全部内容，补充库是 Claude 写的；同时可以把话说足，例如 "A Lean formalization of the proof of Theorem 1.1, following Section 2 and the appendix"。只引用归档时，现在的措辞是准确的。
3. 顺手把指向旧稿的注释改掉。

## 6 复现

```sh
# 需要归档钉住的工具链与依赖（lean-toolchain、lake-manifest.json）
bash audit-claude/check.sh             # 本审计的全部检查，约一刻钟
python3 scripts/verify.py --replay     # 归档自带的验证；会改写 verification/ 下的记录，建议在副本里跑
```

改动之后要重录摘要，用 `bash audit-claude/check.sh --record`；它跳过文件完整性一步，之后须重新生成或删去两份哈希清单，否则不带参数的运行第一步就停。

`audit-claude/` 里的文件：

- `check.sh`、`expected-summary.txt`：全部检查及其应有的摘要行。
- `scan.py`：源码扫描。
- `OleanCheck.lean`、`SupplementAudit.lean`：编译产物与环境的检查，含重名检查。
- `Gates.lean`、`Gates.template`、`mkgates.py`、`mutants.py`：陈述 gate、路线检查、阅读清单，及其生成与反向测试。
- `Closure.lean`：补充库用到归档的什么。
- `ArchiveAudit.lean`、`MainTheoremClosure.lean`：对归档本身的检查，与上一版相同。
- `archive.sha256`、`files.sha256`：归档原有文件的哈希，新增与改动文件的哈希；`check.sh` 第一步核对。

交付目录顶层的 `logs/` 是干净副本上的运行记录：`check.log`、`archive-verify.log`。
