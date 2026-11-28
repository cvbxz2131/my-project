# The seven-point conjecture for four triangle shapes

Let $X$ be a finite subset of the Euclidean plane. Its triangle types are the sorted triples of side lengths of triples of distinct points. Collinear triples count. Palsson and Yu's Conjecture 4.1 states that the maximum size of a planar set determining four triangle types is seven, with equality only for a regular heptagon. [Palsson and Yu, *On Optimal Point Sets Determining Distinct Triangles*, §4](https://arxiv.org/html/2308.13107#S4) · [Journal version](https://doi.org/10.37236/12360)

**Theorem.** Every seven-point planar set determining at most four triangle types is a regular heptagon up to similarity. No set of eight or more points determines at most four types.

## Distance reduction

Suppose first that $X$ has exactly seven points and at most four triangle types. Write $D$ for the number of distinct pairwise distances. For fixed distinct centers $a,b$, each ordered pair $(|a-p|,|b-p|)$ occurs for at most two different third points $p$, by the two-circle intersection bound. On an edge of length $s$, a triangle type containing $s$ gives at most two such ordered pairs. Thus each distance occurs in at least two types, since an edge has five possible third points. The sum of the numbers of different lengths in all the types is at most twelve, so $D\le6$.

If $D=6$, all four types are scalene. Edges of any fixed length form a matching, since two at a vertex would give a repeated length in a type. Each vertex has six edges using six distances, so each matching must meet all seven vertices. This is impossible.

Suppose $D=5$. There are four types whose total number of length incidences is at least ten. The loss relative to four scalene types is at most two. At least one type has a repeated length because each vertex has degree six. Two types with repetitions must therefore both be isosceles.

- If only one type has a repeated length $r$, all four other lengths form matchings. Every vertex has at least two $r$-neighbors. If a vertex has three, then their three pairwise distances are all the third length in that unique type. If this length equals $r$, the four vertices are mutually equidistant, which is impossible in the plane. Otherwise it is a matching length, also impossible. Each vertex therefore has exactly two $r$-neighbors and must meet all four matching lengths, contradicting the odd order.
- If there are two isosceles types with the same repeated length $r$, they are the only two types containing $r$ by the incidence count. There can be no triple with just one $r$-edge. Nonadjacency for the $r$-edges, including equality of vertices, is therefore an equivalence relation. The $r$-edges form a complete multipartite graph with at most two parts, since no triangle is all $r$. Both parts have size at least two because the other four lengths are matchings and every vertex has at least two $r$-neighbors. The larger part has at least three vertices. Two centers in the smaller part and three vertices at distance $r$ from both violate the two-circle bound.
- In the remaining case the two isosceles types are $\{r,r,c\}$ and $\{s,s,d\}$, with distinct repeated lengths $r,s$. Their singleton lengths $c,d$ must be distinct. If they coincided, the edge of that length could see only the two equal-radius pairs from those types and hence at most four third points.

For any edge $ab$ of length $c$ or $d$, let $Y$ consist of its endpoints and all possible third points from the two types containing its length. The corresponding isosceles type contributes at most two points, and the other type at most four. Thus $X\subseteq Y$ and $|Y|\le8$. The half-turn about the midpoint of $ab$ swaps its endpoints and the two distances in every ordered pair. Therefore it preserves $Y$ and sends at most one point of $X$ outside $X$.

If all the edges of lengths $c,d$ had one midpoint, those edges together would form a matching. No triangle could contain two of them. As $c,d$ each appear in two types, all four types would then contain one of these lengths. A matching on seven vertices has an independent triple, giving a contradiction.

Choose two such edges with different midpoints. The composition of their half-turns is a nonzero translation $x\mapsto x+t$, and it sends at most two points of $X$ outside $X$. The set is partitioned into finite chains along $t$, each starting at a point in $X\setminus(X+t)$. There are at most two such points, so at least four points are collinear. If all points are collinear, the distances from one extreme point already give six lengths. Otherwise the four collinear points give two different collinear types by taking triples with different spans. A point outside the line makes three different noncollinear types with the three distinct bases from one extreme among the four, because their areas differ. These five types again contradict the hypothesis. This concludes the proof that $D\le4$.

## One and two distances

Four mutually equidistant points cannot lie in the plane. If there are just two distances, there is a monochromatic triangle among any six points. Indeed, some three of the five edges incident to a chosen vertex have the same length. An edge of that length among the three neighbors completes a monochromatic triangle with the vertex. If none does, the three neighbors already form one in the other length.

Scale that triangle to have side one and write $z\ne1$ for the other length. Any additional point has distances to its three vertices in $\{1,z\}$. All three distances equal to one is impossible. If all are $z$, the point is the center and $z^2=1/3$. If two distances are one, the point is the reflection of the remaining triangle vertex across the side joining those two centers, so $z^2=3$. If exactly one distance is one, use coordinates $(-1/2,0),(1/2,0),(0,\sqrt3/2)$ with the lone unit distance to the last vertex. The point is on the vertical bisector and at height $\sqrt3/2\pm1$, so $z^2=2\pm\sqrt3$. These possibilities for $z^2$ are distinct. For a given $z$, there are at most three additional points, one for each choice of the singled-out vertex in a nonconstant distance triple. Hence seven is impossible.

## Finite check of distance-label patterns

Number the vertices $0,\ldots,6$. Label the distances in order of first appearance as the edges $(i,j)$ with $j<i$ are read in lexicographic order. For each successive edge the checker tries every used label and the next unused label if there are fewer than six. The initial two-circle incidence bound already gives this limit. On assigning $(i,j)$, the new triangle types are precisely those with third vertex $k<j$. The checker prunes a branch as soon as it has more than four types. On a completed vertex prefix, it also checks the two-circle bound and excludes a monochromatic four-vertex complete graph. At the end, every distance must occur in at least two types as proved above. These conditions hold for every actual point configuration, so the enumeration contains the distance matrix of any hypothetical example after relabeling its distances.

The accompanying [Python checker](check_colorings.py) verifies these finite statements.

| Number of distances | Matrices after first-appearance relabeling | Property of every matrix |
| --- | ---: | --- |
| 3 | 120 | There is a cyclic ordering in which the distance label depends only on the cyclic separation. |
| 4 | 105 | There exist distinct $a,b,c,d,p,q$ with $c,d,p,q$ each equidistant from $a,b$, and $p,q$ each equidistant from $c,d$. |
| 5 or 6 | 0 | These cases also follow from the geometric distance reduction. |

In the four-distance case, $c,d,p,q$ would all lie on the perpendicular bisector of $ab$. On this line the unique point equidistant from $c,d$ is their midpoint, so the distinct $p,q$ cannot both occur.

In the three-distance case, the cyclic shift of the seven vertices preserves every distance. The set is noncollinear because seven collinear points have at least six distances. The shift on any three noncollinear points therefore extends to a plane isometry. It agrees with the shift on all vertices because distances to three noncollinear points determine a point. The isometry fixes the centroid and its orthogonal linear part has order seven. Its determinant is one, so it is a nonidentity rotation of order seven. The orbit is a regular heptagon.

## Sharpness and larger sets

On a regular heptagon the positive cyclic gaps of a triangle sum to seven. The unordered possibilities are $(1,1,5),(1,2,4),(1,3,3),(2,2,3)$. Replacing each gap $g$ by its shorter circular separation $\min(g,7-g)$ gives four different side-length types.

If a set of at least eight points had at most four types, each seven-point subset would be a regular heptagon. Two such subsets differing by one vertex share six vertices and hence have the same circumcircle. A regular heptagon on that circle containing a given common vertex is uniquely determined. The two subsets would coincide, a contradiction.

## Reproduction

Run from the repository root with Elan and Python 3. The repository pins Lean 4.28.0. The formalization uses Lean's standard library.

```sh
lean -DwarningAsError=true -j1 four-triangle-conjecture/FourTriangles.lean
python four-triangle-conjecture/check_colorings.py
```

[FourTriangles.lean](FourTriangles.lean) defines the edge order, first-appearance labeling and prefix checks used in the enumeration. An induction on the remaining edges proves that every sequence accepted by `follow` is covered by `certify`. The theorem `finite_classification` gives the three-label cyclic order or the four-label obstruction. The theorem `cyclic_of_no_bisector` gives a propositional cyclic-order result once the geometric bisector condition is supplied. The geometric reductions and the passage from this order to a regular heptagon are proved above.

The finite search uses `native_decide`. The Lean axiom audit printed by the source includes `Lean.ofReduceBool` and `Lean.trustCompiler`. The Python checker independently enumerates the distance-label matrices and checks the cyclic orders and bisector obstructions. In verification the two implementations produced exactly the same 225 admitted matrices.

Lean 4.28.0 compiled the source and imported the resulting module. A separate run of `leanchecker` reported an unknown `native_decide` auxiliary declaration during replay.

## Prior work

The November 28, 2026 search used the paper title, authors, arXiv identifier and statement, along with searches of public proof repositories. It found the original conjecture and no matching public proof in the sources examined.

The proof note, Lean formalization and Python checker were prepared with OpenAI Codex.

