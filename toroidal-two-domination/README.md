# Two-domination under vertex and edge deletion in toroidal grids

Let $G=C_m\square C_n$ with $m,n\ge3$. Its vertices are pairs $(a,b)$, and the four neighbors are obtained by adding $(\pm1,0)$ or $(0,\pm1)$ modulo $(m,n)$. A set $D$ is 2-dominating if each vertex outside $D$ has two distinct neighbors in $D$. Write $\gamma_2(G)$ for the minimum size of such a set. This note answers Problems 1 and 2 of Chen and Zhang's 2019 paper *Fault Tolerance and 2-Domination in Certain Interconnection Networks*, *Journal of Mathematics Research* 11(2), 181–188. [DOI and publication record](https://doi.org/10.5539/jmr.v11n2p181) · [Full issue containing §3.2, Table 4 and the two problems](https://www.academia.edu/39293980/Journal_of_Mathematics_Research_V11N2)

## Problem 1. Single-vertex deletion

The torus $C_4\square C_7$ has $\gamma_2(G)=12$ and $\gamma_2(G-v)=11$ for every vertex $v$. It has the fewest vertices of any toroidal-grid counterexample. Table 4 of Chen and Zhang already gives the unmodified value 12. The value after vertex deletion contradicts the single-vertex stability claimed for $3\le m,n\le10$ in §3.2. [Chen and Zhang, §3.2 and Table 4](https://www.academia.edu/39293980/Journal_of_Mathematics_Research_V11N2)

For the deletion of $(0,0)$, an 11-vertex witness is given by the following second coordinates at each first coordinate.

| First coordinate | Selected second coordinates |
| ---: | :--- |
| 0 | 2, 5 |
| 1 | 1, 3, 6 |
| 2 | 1, 4, 6 |
| 3 | 0, 2, 4 |

The Lean certificate excludes every set of at most 11 vertices in the unmodified torus. Inserting the deleted vertex into any 2-dominating set of the punctured torus gives a 2-dominating set of the full torus. Thus the two minima are exactly 11 and 12. Translations carry the deletion of $(0,0)$ to the deletion of any vertex.

For minimality, coordinate interchange reduces to $3\le m\le n$ and $mn<28$. The table gives the orders and the common values before and after deletion of an arbitrary vertex.

| $(m,n)$ | Order | Common $\gamma_2$ |
| :---: | ---: | ---: |
| $(3,3)$ | 9 | 3 |
| $(3,4)$ | 12 | 5 |
| $(3,5)$ | 15 | 6 |
| $(3,6)$ | 18 | 6 |
| $(3,7)$ | 21 | 8 |
| $(3,8)$ | 24 | 9 |
| $(3,9)$ | 27 | 9 |
| $(4,4)$ | 16 | 7 |
| $(4,5)$ | 20 | 8 |
| $(4,6)$ | 24 | 10 |
| $(5,5)$ | 25 | 10 |

In each case Lean checks an upper-bound witness in the full torus and a lower bound on the punctured torus. A minimum set can be translated to omit the vertex being deleted, so deletion cannot increase the minimum. The matching bounds force equality. The proof checks the enumeration of dimensions and the symmetry reductions as well as the finite certificates.

## Problem 2. Deletion of two edges on a path

The requested bound holds. In fact, in any finite vertex-transitive simple graph of minimum degree at least two, if every edge in $F$ is incident to one vertex $v$, then

$$
\gamma_2(G)\le\gamma_2(G-F)\le\gamma_2(G)+1.
$$

The set $V(G)\setminus\{v\}$ is 2-dominating, so a minimum set omits at least one vertex. An automorphism moves an omitted vertex to $v$, giving a minimum set $D$ that omits $v$. Each $x\notin D\cup\{v\}$ has two neighbors in $D$ via edges with neither endpoint at $v$. These edges survive the deletion of $F$. Hence $D\cup\{v\}$ is 2-dominating in $G-F$, giving the upper bound. Any 2-dominating set in $G-F$ is also one in $G$, giving the lower bound.

The additive constant is attained by deleting the edges from $(0,0)$ to $(0,1)$ and $(0,5)$ in $C_3\square C_6$. The minimum increases from 6 to 7. Chen and Zhang's Table 4 already reports an increase from 6 to 7 for two-edge path deletion in this grid. The formal proof gives an explicit path and verifies its exact values. [Chen and Zhang, Table 4](https://www.academia.edu/39293980/Journal_of_Mathematics_Research_V11N2)

## Reproduction

Use Elan and run these commands in this directory. The repository fixes Lean 4.28.0 and this package pins mathlib.

```sh
lake exe cache get
lake --wfail build
```

The Lean file proves (1) the exact minima for the 28-vertex counterexample, (2) stability below order 28, (3) the star-deletion bound and (4) its sharpness for a two-edge path. The entry points are shown below.

| Result | Lean theorem |
| :--- | :--- |
| Counterexample and exact minima | `four_seven_counterexample` |
| Minimum order | `stable_lt_twenty_eight` |
| General star-deletion proof | `minimum_omits_of_transitive` and `star_bounds_of_minimum` |
| Star-deletion bound on tori | `star_deletion_bound` |
| Sharpness example | `straight_path_sharp` |

The finite proofs use the bit at position $an+b$ for vertex $(a,b)$. Lean proves that every vertex set admits this encoding, that the bit count agrees with the set cardinality, and that the Boolean constraints express the original two-domination rule. Explicit masks give the upper bounds. `bv_decide` checks SAT refutations for the lower bounds, using the compiler via `Lean.ofReduceBool` and `Lean.trustCompiler`. The star-deletion theorem uses only the standard Lean axioms. The source prints these dependencies for all four main results.

## Prior work check

On 27 November 2026 we searched the paper title, DOI and both problem statements, as well as equivalent formulations using vertex deletion, punctured tori, 2-domination stability and 2-bondage. The search covered indexed literature, arXiv and public GitHub repositories, issues and pull requests. We found no earlier statement or proof of the 28-vertex counterexample or of the general star-deletion bound giving the answer to Problem 2. This records the coverage of the search and attributes the known numerical results to the original paper.

The mathematical note and Lean formalization were prepared with OpenAI Codex.
