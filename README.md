# A smallest tree counterexample to AutoGraphForge's power domination bound

[中文说明](README.zh-CN.md)

The AutoGraphForge audit proposed that every finite connected simple graph $G$ with at least two vertices satisfies $\gamma_P(G)\le 3b(G)-5$, where $\gamma_P$ denotes the power domination number and $b$ the burning number. The proposal is identified as `991e8e84` and appears in two equivalent forms at ranks 54 and 55. [Audit table](https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/2026_ITAT_paper/tab_audit.tex#L59-L60) · [Pastorek, *AutoGraphForge*, §4.2](https://arxiv.org/html/2609.03478v1#S4.SS2)

Rohan Arun's technical note, dated 19 November 2026, refuted this proposal with a 16-vertex tree and showed that power domination is unbounded among trees with burning number three. This supplement gives a 15-vertex witness, proves that its order is minimum, and supplies a Lean formalization of the witness and its family. [Arun's archived note](https://doi.org/10.5281/zenodo.24383172) · [Arun's GitHub proof](https://github.com/rohanarun/autographforge-tree-counterexample/blob/e2be55776572fe18c21a44cfa5d8e8c65b807c7b/README.md)

## Construction and proof

Start with a star on $k\ge 2$ base vertices, including its center. Attach two private leaves to each base vertex. The resulting tree $T_k$ has $3k$ vertices, partitioned into triples consisting of a base vertex and its leaves. The paired-leaf construction belongs to the family of extremal graphs studied by Zhao, Kang and Chang. [Zhao, Kang and Chang, *Power domination in graphs*, 2006](https://doi.org/10.1016/j.disc.2006.03.037)

**Burning number.** In each round, one previously unburned vertex is ignited and fire from earlier rounds spreads one edge. Ignite the center in round one and the two private leaves of any one peripheral base vertex in rounds two and three, respectively. Every vertex is within distance two of the center, so this schedule burns the tree in three rounds. In two rounds the first source can reach leaves in at most one triple. The second source can cover at most one of the two leaves in another triple. Thus $b(T_k)=3$. [Bonato, Janssen and Roshanbin, *How to burn a graph*](https://arxiv.org/abs/1507.06524)

**Power domination number.** A seed set initially observes its closed neighborhood. After that, an observed vertex can force its sole unobserved neighbor. If a triple contains no seed, neither leaf is initially observed. Both leaves have the same sole neighbor, which cannot force either while both are unobserved. Every triple therefore needs a seed. Seeding all $k$ base vertices observes the entire tree in the initial step, so $\gamma_P(T_k)=k$.

With $k=5$ the proposed inequality becomes $5\le4$. With $k$ arbitrary the same construction recovers Arun's unboundedness conclusion at burning number three.

## Minimum order

For a connected graph of order $n\ge3$, Zhao, Kang and Chang proved $\gamma_P(G)\le\lfloor n/3\rfloor$. Thus a graph of order less than 15 and burning number at least three has $\gamma_P(G)\le4\le3b(G)-5$. If $b(G)=2$, the first ignition's closed neighborhood misses at most one vertex. Seeding the first ignition observes that neighborhood. If a vertex remains, connectedness gives it an observed neighbor, which can force it. Hence $\gamma_P(G)=1=3b(G)-5$. A graph with at least two vertices needs at least two rounds, so 15 is the minimum order among counterexamples. [Zhao, Kang and Chang, 2006](https://doi.org/10.1016/j.disc.2006.03.037)

## Reproduction

Run these commands from the repository root with Elan and Python 3 installed. The toolchain is pinned to Lean 4.28.0 and the proof uses the standard library.

```sh
lean -DwarningAsError=true -t 0 Rank54.lean
python check_tree.py
```

In [`Rank54.lean`](Rank54.lean), `not_published_bound` refutes the stated universal inequality and `unbounded_at_three` gives the family result. The file checks that the witness has 15 distinct vertices and proves the exact two parameters directly from the process rules. It was compiled with warnings treated as errors, and the compiled module passed kernel replay with `leanchecker`. The minimum-order argument above uses the published bound on $\gamma_P$ and is given in prose. The [Python verifier](check_tree.py) independently finds $b=3$ and $\gamma_P=5$ for the finite witness.

The note, Lean formalization and Python verifier were prepared with OpenAI Codex.
