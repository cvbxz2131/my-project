# Huffman trees maximize branching histories with three events

[中文说明](README.zh-CN.md)

Dickey and Rosenberg's Conjecture 20(ii) asks whether the uniform-weight Huffman tree maximizes the number of tie-permitting labeled histories for every prescribed event count among strictly $r$-furcating rooted trees with a fixed number of leaves. This note proves the case of exactly three events for every admissible arity and leaf count. It also proves optimality for every event count when there are at most $r+1$ internal vertices. The reference Huffman tree is the one constructed by successive smallest-weight merges in §5.1. [Dickey and Rosenberg, Conjecture 20](https://arxiv.org/html/2602.07426v1#Thmtheorem20)

## The three-event maximum

In a strictly $r$-furcating tree, each internal vertex has exactly $r$ children. There are $m=(n-1)/(r-1)$ internal vertices when there are $n$ leaves. For a fixed labeling of the leaves, a history assigns each internal vertex to an event. A proper ancestor must have an earlier event than its descendants. Each event is used at least once. Numbering events from the root toward the leaves reverses the direction used in the original paper and preserves counts. [Dickey and Rosenberg, 2025, Theorem 15](https://doi.org/10.1098/rstb.2023.0307)

Suppose $r^2<n\le r^3$ and write $m=1+r+q$, where $1\le q\le r^2$. The largest number of histories using exactly three events is

$$
2^{r-\lceil q/r\rceil}.
$$

A tree with a chain of four internal vertices admits no three-event history. In a tree of internal height at most three, let $k\le r$ be the number of internal children of the root, and let $d$ be the number of those children that have an internal child of their own. There are $r+q-k\ge q$ internal grandchildren, so $rd\ge q$. The root has event 1, each of the $d$ deeper branches has its internal child of the root at event 2 and all of its internal grandchildren at event 3, and each of the remaining $k-d$ children can independently choose event 2 or 3. Since $q>0$, a chain uses all three events. The count is therefore $2^{k-d}$, which is at most the displayed value. Equality holds exactly when $k=r$ and $d=\lceil q/r\rceil$.

### Why Huffman attains the bound

Write $q=ar+b$ with $0\le b<r$. Beginning with $n=r^2+(r-1)q$ items of weight 1, all merges of $r$ ordinary leaves make subtrees of weight $r$.

- If $b=0$, the first phase produces $r+(r-1)a$ items of weight $r$. The next $a$ merges each take $r$ such items. At the final merge the $r$ items comprise $a$ deeper branches and $r-a$ shallow branches.
- If $b>0$, the first phase produces $r+(r-1)a+b-1$ items of weight $r$, with $r-b$ ordinary leaves left over. The next merge consumes those leaves and $b$ weight-$r$ items, creating one partially filled deeper branch of weight greater than $r$. The remaining $r+(r-1)a-1$ items of weight $r$ feed $a$ full deeper branches. The final merge has those $a+1$ deeper branches and $r-a-1$ shallow branches.

This gives $d=\lceil q/r\rceil$ in both cases. For instance, the four-way tree on 19 leaves has three shallow branches and one deeper branch, achieving eight histories.

### Other leaf counts

If $1\le m\le r+1$, Huffman first merges ordinary leaves $m-1$ times and connects those subtrees and the remaining leaves to the root. All internal vertices other than the root can then be assigned freely to the $z-1$ later events, subject to using all of them. Every tree on the same number of vertices has at most this many assignments. For three events the maximum is $\max(0,2^{m-1}-2)$. If $m>1+r+r^2$, no tree has enough room in three internal levels, so the three-event count is zero. A single leaf uses zero events.

## Verification

```sh
lean -DwarningAsError=true -t 0 ThreeEvents.lean
python count_histories.py
```

[The Lean file](ThreeEvents.lean) checks completeness and uniqueness of schedule enumeration in the three-level branch model and proves the upper bound and its attainment for $q>0$. It uses the standard library in Lean 4.28.0 and passes kernel replay with `leanchecker`. The reduction from trees to branch counts and the identification of the attaining shape under Huffman merging are proved above.

[The integer search](count_histories.py) also checked all event counts for $2\le r\le10$, $m\le42$, comparing 454,023 alternative root splits. For a fixed root split and allotted sets of times for the subtrees, the history count is a product of the subtree counts. Summing over compatible sets of times gives a componentwise monotone function of the subtree counts. Induction on $m$ thus reduces the bounded search to checking each split with Huffman subtrees. It found no counterexample in this range. The proof for arbitrary parameters in this note covers three events and the shallow regime stated above.

## Prior work

The original papers give an enumeration recurrence, binary tables up to 21 leaves, and ternary tables up to 29 leaves. Searches by title, arXiv identifier, and technical terms found no earlier public statement of the general three-event maximum among the sources inspected. The authors' publication list also contains a closely titled paper in press without a linked full text. Priority for the formula and proof remains unconfirmed. [Earlier binary case](https://arxiv.org/html/2511.16799v1#Thmtheorem14) · [Original ternary data](https://arxiv.org/html/2602.07426v1#S7) · [Authors' publication list](https://rosenberglab.stanford.edu/publications.html)

The note and the verification files were prepared with OpenAI Codex.
