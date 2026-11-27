# The minimum order of a D(4) graph

A graph is a $D(4)$ graph if its domination number $\gamma$, chromatic number $\chi$, and dominator chromatic number $\chi_d$ are all four. A dominator coloring is proper and the closed neighborhood of every vertex contains an entire nonempty color class. This note proves that the minimum order is **12**, settling the $k=4$ case of Kalarkop, Kaemawichanurat and Rangarajan's minimum-order conjecture. The construction attaining 12 is their Figure 2. [Conjecture 1 and Figure 2, RAIRO Operations Research 59 (2025), 1141–1152](https://doi.org/10.1051/ro/2025015) · [2022 preprint](https://arxiv.org/abs/2208.07020)

## Lower bound

Take a dominator coloring with four colors. If a given class contains no vertex with neighbors in all three other classes, recolor each of its vertices with a color absent from its neighbors. Vertices of the class are pairwise nonadjacent, so these recolorings give a proper three-coloring. Since $\chi=4$, every class therefore contains a vertex that sees all three other colors.

Sort the four class sizes $a\le b\le c\le d$. Take a vertex in the first class that sees the other three colors, and choose one neighbor in each other class. Label these four vertices first within their respective classes. The next step uses the following constraints.

- Each class is an independent set.
- The first vertex of the smallest class is adjacent to the first vertex of each other class.
- Every vertex has a closed neighborhood containing some whole class.
- Every triple fails to dominate at least one vertex.

When $a+b+c+d\le11$, there are 38 positive nondecreasing profiles. A CNF uses one variable for each unordered pair of vertices. Auxiliary literals select a whole class dominated by a vertex or select an uncovered vertex for a triple. The Lean proof transfers every graph satisfying the four constraints to a satisfying assignment of its profile's CNF. The SAT solver returns an LRAT refutation for every profile, and the Lean checker validates each refutation against the corresponding CNF. The reduction uses only the three specified edges from the chromatic-number assumption.

| Order | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Profiles excluded | 1 | 1 | 2 | 3 | 5 | 6 | 9 | 11 |

## The published twelve-vertex construction

Take two copies of $K_{3,3}$. Distinguish one vertex on each side and join the four distinguished vertices into a clique. The four bipartition sides form a dominator coloring, and the clique requires four colors. To cover both nondistinguished vertices on a side, a dominating set must contain a vertex on the opposite side or both of those vertices. Thus each copy requires at least two vertices in a dominating set. One vertex per side suffices. The Lean proof also verifies connectivity and the exact three parameters. [Kalarkop, Kaemawichanurat and Rangarajan, Figure 2 and Lemma 2](https://doi.org/10.1051/ro/2025015)

## Reproduction

Run these commands from this directory with Elan. The repository pins Lean 4.28.0 and the package pins mathlib.

```sh
lake exe cache get
lake --wfail build
```

The public results in `DominatorFour.lean` are `order_ge_twelve` and `exists_order_twelve`. Replay the graph-level theorem module after the build with `lake env leanchecker DominatorFour`. `DominatorFourCert.lean` constructs the CNFs and checks the solver's LRAT output using Lean's proved checker. The Boolean certificate checks use compiled evaluation, as recorded by the axiom audit in the source. The SAT solver is supplied with the Lean toolchain.

## Prior work

The 12-vertex upper bound is the authors' published construction. Searches by author, title, DOI, parameter names and exact bound found the conjecture and the planarity result, with no matching proof of the unrestricted 12-vertex lower bound in the public sources examined. The first author's dissertation was identified through his university profile. Its full text was unavailable for comparison. [Dissertation record](https://ftp.sju.edu.in/school-of-physical-sciences/department-of-mathematics/MTg0Mw)

The proof, mathematical note and Lean formalization were prepared with OpenAI Codex.
