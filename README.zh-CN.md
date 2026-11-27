# AutoGraphForge 第 54 条猜想的一个最小反例及其 Lean 证明

[English note](README.md)

**已有公开反驳。** Rohan Arun 在技术说明 *A tree counterexample to AutoGraphForge conjecture 991e8e84* 中给出一棵 16 个顶点的树，证明 $b=3$、$\gamma_P=5$，并证明在燃烧数为 3 的树上电力支配数无界。说明署期 2026 年 11 月 19 日，GitHub 提交及 Zenodo 归档记录均可追溯至 11 月 20 日，早于本次 11 月 26 日的计算。本目录给出 15 个顶点的构造、最小阶数的纸笔论证，以及该反例族的 Lean 形式化。[Arun 的原始提交](https://github.com/rohanarun/autographforge-tree-counterexample/tree/e2be55776572fe18c21a44cfa5d8e8c65b807c7b) · [Zenodo 归档版本](https://doi.org/10.5281/zenodo.24383172)

AutoGraphForge 的公开审查表第 54 条提出，对每个非平凡连通简单图 $G$，电力支配数与燃烧数满足 $\gamma_P(G)\le 3b(G)-5$。其中 54 是排名，项目内的标识为 `991e8e84`，第 55 条是同一不等式的代数改写。[原表，第 54、55 条](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/2026_ITAT_paper/tab_audit.tex#L59-L60) · [项目论文 §4.2](https://arxiv.org/html/2609.03478v1#S4.SS2)

## 构造

画一个有 $k$ 个顶点的星形，称这 $k$ 个点为基点。再给每个基点单独接两片新叶子，包括星形的中心。每个基点和自己的两片叶子组成一组，共有 $3k$ 个点。取 $k=5$ 就得到下面这棵树，图中每个小写字母代表一个独立的叶顶点。

```text
中心 A ─┬─ a₁
        ├─ a₂
        ├─ 基点 B ─┬─ b₁
        │          └─ b₂
        ├─ 基点 C ─┬─ c₁
        │          └─ c₂
        ├─ 基点 D ─┬─ d₁
        │          └─ d₂
        └─ 基点 E ─┬─ e₁
                   └─ e₂
```

**燃烧数等于 3。** 每轮可以点燃一个此前未燃的顶点，此前的火同时向外走一条边。第一轮从 A 开始，它到每个顶点最多两条边，所以第三轮全图已燃。一个完整的合法点火顺序是 $A,b_1,b_2$。反过来，两轮时第一次点火只能覆盖它自己和邻居，因而最多碰到一组的叶子。任取另一组，其两片叶子只靠第二次点火最多能烧到一片。这个论证对每个 $k\ge2$ 都成立。[图燃烧的原始定义](https://arxiv.org/abs/1507.06524)

**电力支配数等于 $k$。** 最初，传感器能观测安装点及其所有邻居。之后，只有在某个已观测点恰好剩一个未观测邻居时，才能把观测传给它。若一个三点组里没有传感器，两片私有叶子起初都未被观测，而且只能通过同一个基点观测。基点同时面对两片未知叶子，永远无法迈出第一步。因此每组至少需要一个传感器。在全部基点各放一个，初始观测便覆盖全图，恰好达到下界。

于是 $k=5$ 时原式要求 $5\le4$。把组数继续增加，燃烧数仍是 3，电力支配数可以任意大。即使把右边的线性式换成燃烧数的任意有限值函数，也没有适用于全部连通图的上界。

## 为什么 15 个点已经最少

以下是利用既有定理的纸笔推论。对至少有 3 个顶点的连通图，Zhao、Kang、Chang 的上界给出 $\gamma_P(G)\le\lfloor |V(G)|/3\rfloor$。因此，少于 15 个点且 $b\ge3$ 时，$\gamma_P\le4\le3b-5$。若 $b=2$，第一次点火顶点及其邻居之外最多剩一个顶点未覆盖。在起点放一个传感器，便能观测上述邻域。若真剩一点，连通性保证它有已观测邻居，后者可以立即观测它。此时 $\gamma_P=1=3b-5$。非平凡图至少需要两轮燃烧。这就排除了所有更小的反例。[Zhao、Kang、Chang，2006](https://doi.org/10.1016/j.disc.2006.03.037)

## 复核

在本目录运行，Lean 只用标准库，版本由 `lean-toolchain` 固定。

```powershell
lean --version
lean -DwarningAsError=true -t 0 Rank54.lean
python check_tree.py
```

Lean 中的 `power_exact` 和 `burning_exact` 分别从两种传播规则证明精确值。`fifteen_vertices` 检查有限反例确有 15 个互异顶点，`not_published_bound` 验证图满足原命题的假设并推出矛盾，`unbounded_at_three` 证明固定燃烧数时电力支配数无界。本次编译及对编译产物的 `leanchecker` 内核重放均已通过。主定理只依赖 Lean 的标准公理 `propext`、`Classical.choice`、`Quot.sound`。关于 15 个顶点最少的论证单独引用了文献上界，未收入 Lean 文件。

Python 脚本从零开始枚举。它在 15 个顶点上计得 **104 种**最短合法点火顺序、**243 组**最小传感器集合。后一个数也可手算。五组各从三个顶点中选一个，共 $3^5=243$ 种选法。这样每个基点一开始就已被观测，而且每组至多剩下一片未观测的叶子。

## 两种构造与归属

Arun 的树为每个分支配置两片私有叶，另设一个公共中心，共 $3k+1$ 个顶点。本目录的树让中心也承担一组，取 $k-1$ 个外围基点，共 $3k$ 个顶点。两者的下界都来自同一条传播规则。Arun 的归档包含文字证明和 Python 验证；本目录增加了一个阶数最小的见证和可重放的 Lean 证明。成对私有叶的电力支配极值构造也有更早的文献。对 15 顶点改进和 Lean 形式化的独立优先权，此处不作认定。[Arun 的构造](https://github.com/rohanarun/autographforge-tree-counterexample/blob/e2be55776572fe18c21a44cfa5d8e8c65b807c7b/README.md) · [电力支配极值图族](https://doi.org/10.1016/j.disc.2006.03.037)

技术说明、Lean 形式化和 Python 复核脚本由 OpenAI Codex 协助完成。

## 相关说明

- [换热网络年费用单谷性猜想的三设备反例](heat-exchanger-unimodality/README.md)
- [18 光子双模纠错码的多面体对称性排除](photon-loss-symmetry/README.md)
