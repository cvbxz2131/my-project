# Sharp outer regions in symmetric additive subtraction games

Consider normal play on the nonnegative integer lattice. A legal move subtracts one of $(a,b),(b,a),(a+b,a+b)$ and leaves both coordinates nonnegative. Write $P(x,y)=1$ for a losing position. The recurrence gives $P(x,y)=1$ precisely when all legal options have value zero.

In *Subtraction games in more than one dimension*, Larsson, Saha and Yokoo describe symmetric additive games with $b\le 2a$ in Proposition 47 and illustrate $(a,b)=(1,5),(2,5)$ in Figures 16 and 18. The following results determine both pictured games on the whole board and the sharp outer regions for all $a=1,\ b\ge2$. [Theoretical Computer Science 1016 (2024), 114775](https://doi.org/10.1016/j.tcs.2024.114775) · [Sections 9–10](https://arxiv.org/html/2307.12458#S9)

## Sharp outer-region theorem for $a=1$

Put $e=b\bmod 2$, $v=2b+e$, $u=b^2+eb+1$, and $d=b^2-1$. Define $R(y)=1$ when $y\bmod v$ is even and less than $b$, and $R(y)=0$ otherwise. For $y=kv+r$ with $0\le r<v$, put

$$
H(y)=ku+br-d\,\mathbf 1_{\{r\ge b\}}.
$$

For every $b\ge2$ and every $y\ge0$, $P(x,y)=R(y)$ whenever $x\ge H(y)$. In particular,

$$
vx-uy>C,\qquad C=(b^2-1)(b-1)-v,
$$

implies $P(x,y)=R(y)$. The transposed region has the same description with the coordinates interchanged.

Every point

$$
(x_k,y_k)=(ku+b(b-1)-1,\ kv+b-1),\qquad k\ge0,
$$

has $vx_k-uy_k=C$ and $P(x_k,y_k)=1-R(y_k)$. Thus $C$ is the least real cutoff for the stated $u,v$ in the strict inequality above. For every $\lambda<u/v$ and every fixed offset $t$, some $(x_k,y_k)$ satisfies $x_k>\lambda y_k+t$, so $u/v$ is the least slope admissible in such a bound.

### Agreement for $x\ge H(y)$

Use induction on $y$. If $R(y)=1$, the residue $r$ is even and $r<b$. Each move whose second coordinate $q$ is at most $y$ reaches a row with $R(y-q)=0$. Subtracting $1$ gives an odd residue or $v-1$. Subtracting $b$ gives a residue at least $b$. Subtracting $b+1$ also gives a residue at least $b$, except when $r=e=0$, when it gives the odd residue $b-1$.

The differences in the table follow from $bv-d=u$ and the formula for $H$, for each move with $q\le y$.

| Move $(p,q)$ | $H(y)-H(y-q)-p$ when $r<b$ |
| --- | --- |
| $(b,1)$ | $0$ |
| $(1,b)$ | $d$ |
| $(b+1,b+1)$ | $0$ if $r=e=0$, and $d$ otherwise |

At $x\ge H(y)$, every legal predecessor therefore lies in the established region of its row and has value zero. This gives $P(x,y)=1$.

If $R(y)=0$ and $r<b$, then $r$ is odd. Move $(b,1)$ reaches the even residue $r-1$, with difference zero. If $r\ge b$ and $r-b$ is even, move $(1,b)$ reaches residue $r-b<b$. If $r\ge b$ and $r-b$ is odd, move $(b+1,b+1)$ reaches residue $r-b-1<b$. In these last two cases the residue reached is even and substitution into $H$ gives $H(y)=H(y-q)+p$. Each chosen move is legal at $x\ge H(y)$ and reaches a losing position by induction, so $P(x,y)=0$.

If $x<H(y)$, then $vx-uy\le v(H(y)-1)-uy$. This last expression is $dr-v$ for $r<b$ and $dr-vb^2$ for $r\ge b$. The maxima on the two ranges are $C$ and $-d-v$, respectively.

### Sharpness along infinitely many positions

Write $w(y)=H(y)-1$. We show $P(w(kv+r),kv+r)=1-R(kv+r)$ for $0\le r<b$, with $P(-1,0)=0$ denoting an unavailable position. For $k=0$ and $1\le r<b$, only $(b,1)$ can be played. Starting at $(br-1,r)$, exactly $r-1$ moves can be made, so the position is losing precisely when $r$ is odd.

Suppose the assertion holds on the first $b$ rows of block $j=k-1$. We show it first at $(w(kv),kv)$, where $R(kv)=1$.

- If $b$ is even, the diagonal move reaches $(w(jv+b-1),jv+b-1)$. This is losing by the block hypothesis since $b-1$ is odd, so $(w(kv),kv)$ is winning.
- If $b$ is odd, the position $(w(jv+2b-1),jv+2b-1)$ is winning because its diagonal move reaches the losing position $(w(jv+b-2),jv+b-2)$. At $(w(jv+2b),jv+2b)$, move $(b,1)$ reaches that winning position. Move $(1,b)$ reaches $(ju+b^2-1,jv+b)$, which has value zero since $ju+b^2-1\ge H(jv+b)=ju+1$. The diagonal reaches $(w(jv+b-1),jv+b-1)$, which also has value zero by the block hypothesis. Thus $(w(jv+2b),jv+2b)$ is losing. The move $(b,1)$ from $(w(kv),kv)$ reaches it, making $(w(kv),kv)$ winning.

For $1\le r<b$, the move $(b,1)$ reaches the preceding position $(w(kv+r-1),kv+r-1)$. Both other moves go to residues at least $b$ and have difference $d\ge1$ in the table, so they reach winning positions even from $x=w(kv+r)$. The value at each successive position therefore flips, as does $R$ on these rows. This proves the block assertion. Taking $r=b-1$ gives the required infinite sequence.

## Exact whole-board outcomes for the pictured games

| $(a,b)$ | Lower and upper translations | Lookup cutoff $C_0$ | Losing residues in the lower region | Finite check square |
| --- | --- | ---: | --- | --- |
| $(1,5)$ | $(31,11),(11,31)$ | 85 | $y\bmod11\in\{0,2,4\}$ | $0\le x,y\le91$ |
| $(2,5)$ | $(34,22),(22,34)$ | 154 | $y\bmod22\in\{0,1,4,10,13,14\}$ | $0\le x,y\le122$ |

For a row of the table, write $(u,v)$ for the lower translation and $D=u^2-v^2$, $s=ux-vy$, $t=uy-vx$. If $t<-C_0$, use the lower-region residue rule. If $s<-C_0$, transpose it. In the remaining region put $\rho(z)=z$ for $z<2D$ and $\rho(z)=D+z\bmod D$ otherwise. The value is the finite table entry at

$$
\left(\frac{u\rho(s)+v\rho(t)}{D},\ \frac{v\rho(s)+u\rho(t)}{D}\right).
$$

Subtracting $(u,v)$ reduces $s$ by $D$ and preserves $t$, while subtracting $(v,u)$ has the transposed effect. The Lean proof verifies the original recurrence by induction on $x+y$. Where $s$ or $t$ is large, the translations preserve both the position's value and the values of its followers. Near the axes, the one-dimensional residue rule gives a separate reduction. The finite checks use kernel reduction.

## Reproduction

From the repository root, run the following command with Elan. The repository pins Lean 4.28.0 and the proof uses its standard library.

```sh
lean -j1 planar-subtraction/PlanarSubtraction.lean
```

In [PlanarSubtraction.lean](PlanarSubtraction.lean), `exists_unique_outcome` identifies the lookup function as the unique solution of the original move recurrence. The axiom audit for `outcome_recurrence` and `exact_outcome` reports `propext`, `Classical.choice` and `Quot.sound`. The sharp boundary theorem for all $b\ge2$ is proved above in prose.

## Related work

The November 27, 2026 public submission on the same paper treats Figure 17 and Problem 58 and gives a 15-move example for Conjecture 57. Its Figure 17 game has moves $(a,2a),(3a,4a),(4a,6a)$. The uniform central-region formula for $a=1$ remains an open step in this analysis. [Public submission #997](https://github.com/1337isnot1337/solved-conjectures/issues/997)

The proof, mathematical note and Lean formalization were prepared with OpenAI Codex.
