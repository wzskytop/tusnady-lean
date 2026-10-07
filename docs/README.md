# Tusnády's Problem in the Plane — an interactive guide

An interactive, step-by-step guide to the paper **"Tight Bounds for Tusnády's Problem in the Plane"**
([arXiv:2610.08130](https://arxiv.org/abs/2610.08130)), which shows that the combinatorial discrepancy of
axis-parallel rectangles in the plane is Θ(log^{3/2} n).

- **English:** [`index.html`](index.html)
- **中文：** [`index.zh.html`](index.zh.html)

The guide starts from a coloring game and works up to the full proof. It has 22 short sections, 21 interactive
figures, and assumes only second-year undergraduate mathematics. The numbering of equations
(1)–(18), Lemmas 2.1 and 2.3–2.6, Fact 2.2, Proposition 2.7 and Fact A.1 follows manuscript version r65 of the
paper; the TeX source of arXiv v1 was checked on 2026-10-07 and is byte-for-byte identical to the repository’s r65 TeX source.

## Viewing

Each page is a single self-contained HTML file (styles, scripts and math fonts are inlined). The two pages link
to each other with relative paths, so they must stay in the same folder.

- **GitHub Pages, own repository:** put the files in the repository root, then *Settings → Pages → Deploy from a
  branch*.
- **GitHub Pages, inside an existing repository:** put the files in `docs/` (including the empty `.nojekyll`),
  then *Settings → Pages → Deploy from a branch → `main` / `/docs`*. Uploading the files alone does not turn
  Pages on.
- **Locally:** download a file and open it in a browser.

The pages request three text fonts from Google Fonts; if that request is blocked, system fonts are used instead
and nothing else changes. They make no other network requests.

## What is and is not verified

- The guide is an explanation, not a substitute for the paper. Where the two differ, the paper is authoritative.
- The derivations, examples and interactive figures added by the guide have not been formally verified and are
  no substitute for independent review.
- A Lean formalization of the paper's new lower bound is at <https://github.com/wzskytop/tusnady-lean>; see that
  repository for its exact scope and for how it was produced and checked. The cited upper bound, the resulting
  two-sided statement, the historical account and everything specific to this guide are outside that
  formalization.
- The English page is a translation of the Chinese one.

## Third-party material

The pages embed the styles and math fonts of KaTeX 0.16.22 (MIT License); see
[`THIRD-PARTY-NOTICES.md`](THIRD-PARTY-NOTICES.md).

---

# 平面上的 Tusnády 问题：交互式导读

论文 **Tight Bounds for Tusnády's Problem in the Plane**（[arXiv:2610.08130](https://arxiv.org/abs/2610.08130)）的交互式导读。
论文证明平面上轴平行矩形的组合差异度是 Θ(log^{3/2} n)。

- **中文：** [`index.zh.html`](index.zh.html)
- **English:** [`index.html`](index.html)

导读从一个染色游戏讲起，一步一步推到完整的证明，共 22 节、21 个交互图，只假设大二水平的数学。式 (1)–(18)、引理 2.1 和
2.3–2.6、Fact 2.2、命题 2.7、Fact A.1 的编号与论文 r65 版稿件一致；2026-10-07 已核对，arXiv v1 的 TeX 源文件与仓库绑定的 r65 TeX 逐字节相同。

## 查看方式

两个页面都是自包含的单个 HTML 文件（样式、脚本和数学字体都已内嵌），互相之间用相对路径链接，所以要放在同一个目录里。

- **GitHub Pages，单独的仓库：** 把文件放在仓库根目录，然后 *Settings → Pages → Deploy from a branch*。
- **GitHub Pages，放进已有仓库：** 把文件放进 `docs/`（连同空文件 `.nojekyll`），然后 *Settings → Pages → Deploy from a branch →
  `main` / `/docs`*。只上传文件并不会开通网页。
- **本地查看：** 下载文件，用浏览器直接打开。

页面会向 Google Fonts 请求三种正文字体；请求不通时自动改用系统字体，其余不受影响。除此之外没有别的网络请求。

## 哪些经过验证，哪些没有

- 导读是讲解，不能代替论文。两者不一致时以论文为准。
- 导读补充的推导、例子和交互演示没有经过形式化验证，也不能代替独立的审阅。
- 论文新下界的 Lean 形式化见 <https://github.com/wzskytop/tusnady-lean>，确切范围以及它是怎样完成和核查的，以该仓库的说明为准。
  引用的上界、由此得到的双边结论、历史叙述，以及这份导读特有的内容，都不在形式化的范围里。
- 英文页面由中文页面翻译而来。

## 第三方内容

页面内嵌了 KaTeX 0.16.22 的样式和数学字体（MIT 许可证），见 [`THIRD-PARTY-NOTICES.md`](THIRD-PARTY-NOTICES.md)。
