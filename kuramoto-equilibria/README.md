# The exact maximum equilibrium count for rank-one Kuramoto coupling

For every $n\geq 2$, the maximum number of distinct equilibria of the positively coupled rank-one Kuramoto model is **$2^n-2$** after identifying common phase shifts. The natural frequencies have zero sum and are not all zero. Rational weights and frequencies attain the maximum for every $n$. This refutes Conjecture 4.14 of Coss, Hauenstein, Hong, and Molzahn in its rank-one form for every $n\geq 4$. The same paper gives the radical reduction and the upper bound used here. [Coss et al., equations (2)–(3), Theorem 4.3, and Conjecture 4.14](https://arxiv.org/html/1705.06568v2)

For uniform coupling on five oscillators, we also prove that the maximum is **26** on the two-parameter frequency family $(-b,-a,0,a,b)$ with $0\leq a\leq b$ and $b>0$. The bound for general frequencies in the uniform model remains open.

## Equilibrium equation

The model with positive weights $k_i$ is

$$
\dot\theta_i=\omega_i-\frac{k_i}{n}\sum_{j=1}^n k_j\sin(\theta_i-\theta_j).
$$

Write the weighted order parameter as $r e^{i\psi}=n^{-1}\sum_j k_j e^{i\theta_j}$. At equilibrium $r>0$ because $\omega$ is nonzero. Fix the common phase by setting $\psi=0$. Then $\sin\theta_i=\omega_i/(k_i r)$. Putting $R=r^2$ and choosing signs $\sigma_i\in\{-1,+1\}$ for the cosines gives

$$
nR=\sum_{i=1}^n \sigma_i k_i\sqrt{R-(\omega_i/k_i)^2},
\qquad R\geq \max_i(\omega_i/k_i)^2 .
\tag{1}
$$

Conversely, a root gives angles with these sines and cosines. Their weighted sine sum vanishes by $\sum_i\omega_i=0$, and (1) makes their weighted cosine sum $nr$. Thus their order parameter is positive real and they give an equilibrium. Each interior root yields a different phase class for each distinct sign vector. At a boundary root, flipping the sign of a zero cosine gives the same angle. [Radical reduction in Coss et al., §2](https://arxiv.org/html/1705.06568v2#S2)

## A construction attaining the upper bound

Let $m=n-1$. For $1\leq j\leq m$, define rational numbers

$$
t_j=4^{-j},\qquad u_j=\frac{1-t_j^2}{1+t_j^2},
\qquad v_j=\frac{2t_j}{1+t_j^2},\qquad
\kappa=\sum_{j=1}^m u_j.
$$

Then $u_j^2+v_j^2=1$ and $0<u_1<\cdots<u_m<1$. We have $\sum_j(1-u_j)<2\sum_{j\geq 1}16^{-j}=2/15$, so $m-1<\kappa<m$. Also $v_1=8/17>\sum_{j\geq2}2t_j=1/6\geq\sum_{j=2}^m v_j$. In particular every signed sum of the $v_j$ is nonzero.

Set

$$
k=(1,\ldots,1,\kappa),\qquad
\omega=s(-u_1,\ldots,-u_m,\kappa)
$$

for a sufficiently small $s>0$. The frequencies sum to zero. The largest absolute ratio $|\omega_i/k_i|$ is $s$, so take $z=R/s^2$. Equation (1) becomes $F_\sigma(z)=0$ on $z\geq 1$, where

$$
S_\sigma(z)=\sum_{j=1}^m \sigma_j\sqrt{z-u_j^2}
  +\sigma_n\kappa\sqrt{z-1},\qquad
F_\sigma(z)=S_\sigma(z)-nsz.
$$

At $z=1$, the strict sign of $S_\sigma(1)=\sum_{j=1}^{m}\sigma_j v_j$ is independent of $\sigma_n$. As $z\to\infty$, the limit of $S_\sigma(z)/\sqrt z$ is $\sum_{j=1}^m\sigma_j+\kappa\sigma_n$. For mixed signs among the first $m$ entries, the magnitude of their sum is at most $m-2$, so the limit has sign $\sigma_n$. For unanimous signs among the first $m$ entries, the limit has their common sign because $\kappa<m$.

Choose an integer $Z>1$ large enough that every $S_\sigma(Z)$ has the sign of its limit after division by $\sqrt Z$. Then choose a positive rational $s$ such that $F_\sigma(1)$ and $F_\sigma(Z)$ retain the signs of $S_\sigma(1)$ and $S_\sigma(Z)$ for every sign vector. All the margins used in this choice are strict.

For each of the $2^m-2$ mixed vectors of the first $m$ signs, exactly one choice of $\sigma_n$ gives opposite signs at $1$ and $Z$. This produces at least $2^m-2$ equilibria with $1<z<Z$. At $Z$, exactly $2^m$ vectors give a positive value because the signs of $S_{\sigma}(Z)$ and $S_{-\sigma}(Z)$ are opposite. Each of these $F_\sigma(z)$ is ultimately negative since $S_\sigma(z)=O(\sqrt z)$ and $s>0$. That gives another $2^m$ equilibria with $z>Z$. All these roots are interior, so the total count is at least $2^n-2$.

Coss et al.'s Theorem 4.3 gives the matching upper bound. Here is the degree argument including boundary roots. Take the product of the left side minus the right side of (1) over all $2^n$ sign vectors. It is invariant under negating each square root, so it is a polynomial in $R$ of degree $2^n$. If all frequencies are nonzero, the two opposite sign vectors formed from the signs of the frequencies give two vanishing analytic factors at $R=0$ by zero sum. If $\ell\geq1$ frequencies are zero, their signs are free and at least $2^{\ell+1}$ factors vanish as $O(\sqrt R)$, giving polynomial order at least $2^\ell\geq2$ at zero. Each interior equilibrium consumes at least one unit of positive-root multiplicity. At the positive lower endpoint of the domain, an equilibrium with $h$ zero cosines gives $2^h$ vanishing factors of order at least one half. The product then contributes order at least $2^{h-1}\geq1$ for that equilibrium. The total count is therefore at most $2^n-2$. [Coss et al., Proposition 4.1 and Theorem 4.3](https://arxiv.org/html/1705.06568v2#S4.SS2)

## Explicit five-oscillator witness

Take $k=(1,1,1,1,39/10)$ and $\omega=(-96,-97,-98,-99,390)/100000$. With $s=1/1000$, the absolute ratios $|\omega_i/(s k_i)|$ are $(96,97,98,99,100)/100$. Across the 32 sign vectors, there are 14 strict sign reversals between $z=1$ and $z=4$ and 16 between $z=4$ and $z=4000000$. The intermediate value theorem yields 30 distinct equilibria, meeting the general upper bound. Conjecture 4.14's proposed value for these five oscillators was 26.

[RankOneFiveWitness.lean](RankOneFiveWitness.lean) checks the frequency balance, rational square root enclosures, strict signs at the three endpoints, and the counts 14 and 16. The radical reduction, the existence of roots between sign reversals, and the general theorem are proved above. Run from the repository root with the pinned Lean toolchain.

~~~sh
lean -DwarningAsError=true -t 0 kuramoto-equilibria/RankOneFiveWitness.lean
~~~

## Five uniformly coupled oscillators with two opposite frequency pairs

Normalize the common coupling strength to one, so $k_i=1$ in (1), and take $\omega=(-b,-a,0,a,b)$ with $0\leq a\leq b$ and $b>0$. For $x=R\geq b^2$, write $u=\sqrt{x-a^2}$ and $v=\sqrt{x-b^2}$. Each branch equation is

$$
f_{A,B,\epsilon}(x)=5x-\epsilon\sqrt x-Au-Bv=0,
\qquad A,B\in\{-2,0,2\},\quad \epsilon\in\{-1,+1\}.
$$

The coefficients $A,B$ are the sums of the two cosine signs within the pairs of frequencies $\pm a$ and $\pm b$. Let $m(0)=2$ and $m(\pm2)=1$. For $x>b^2$, a root counts with weight $m(A)m(B)$.

First assume $a<b$. At $x=b^2$, the two cosines for the outer pair vanish. The three choices of $B$ for any fixed $(A,\epsilon)$ give a single boundary root of weight $m(A)$ if the common endpoint value is zero. The following table includes this boundary contribution.

| $A$ | $\epsilon$ | Bound for $b\leq 1/5$ | Bound for $b>1/5$ |
| ---: | :---: | ---: | ---: |
| $-2$ | $-1$ | 0 | 0 |
| $-2$ | $+1$ | 4 | 0 |
| $0$ | $-1$ | 4 | 4 |
| $0$ | $+1$ | 8 | 4 |
| $2$ | $-1$ | 6 | 6 |
| $2$ | $+1$ | 4 | 6 |
| Total | | 26 | 20 |

Here are the root bounds behind the table. A strictly convex branch has at most two interior zeros, or at most one when its endpoint value is nonpositive. We use that $u\geq v$ and that $u-v$ is decreasing and convex.

- When $A=-2$ and $\epsilon=-1$, all branches are positive. For $\epsilon=+1$, the branches $B=0,-2$ are strictly increasing and $B=2$ is strictly convex. The common endpoint value $h$ is the same for all three branches. If $h<0$, their weighted sum is at most $2+1+1=4$. If $h=0$, only the convex branch can have an interior root, besides the single boundary root. If $h>0$, only the convex branch can have roots, giving at most two. For $b>1/5$, $5x-\sqrt x>0$ makes all three branches positive.
- When $A=0$ and $\epsilon=-1$, only $B=2$ can give a zero and this branch is strictly convex. For $\epsilon=+1$, the $B=-2$ branch is strictly increasing, $B=0$ has its sole positive zero at $1/25$, and $B=2$ is strictly convex. For $b<1/5$ the endpoint value is negative, so the three branches give at most $1+2+1=4$ per inner sign choice. At $b=1/5$ there can be a boundary root and at most one interior root. For $b>1/5$ only the convex branch can give roots. The factor $m(0)=2$ applies throughout.
- When $A=2$, the branches $B=0,2$ are strictly convex for either choice of $\epsilon$. The branch $B=-2$ is strictly increasing for $\epsilon=-1$. For $\epsilon=+1$ it is negative at $x\leq1/25$ and strictly increasing at $x\geq1/25$. In both cases it gives at most one interior root when $h<0$ and zero when $h\geq0$. The three weighted counts are at most $4$ for $h<0$, at most $4$ for $h=0$ after including the boundary, and at most $6$ for $h>0$. With $\epsilon=+1$ and $b\leq1/5$ we have $h=5b^2-b-2\sqrt{b^2-a^2}<0$.

For $a=b>0$, group all four noncentral signs by their sum $C=A+B$, with weights $1,4,6,4,1$ for $C=-4,-2,0,2,4$. With $\epsilon=-1$, only $C>0$ can contribute, each with at most two roots by strict convexity. With $\epsilon=+1$ and $b<1/5$, each branch gives at most one root because the endpoint value is negative and the branch is either increasing ($C<0$) or strictly convex ($C\geq0$). At $b=1/5$ there is one boundary root and only the $C>0$ branches can have an interior root. For $b>1/5$ only $C>0$ can give roots, with at most two per branch. These bounds again give at most 26.

For attainment with distinct magnitudes, take $a=9/1000$ and $b=1/100$. At $x=b^2$, all $\epsilon=+1$ branches are negative and all $\epsilon=-1$ branches are positive. The strict signs follow from $b-5b^2>2\sqrt{b^2-a^2}$. At $x=1/100$, the $\epsilon=-1$ branches with $(A,B)=(2,0),(0,2),(2,2)$ are negative, since $5x+\sqrt x<2\sqrt{x-b^2}$. All branches are ultimately positive. There are at least 16 equilibria from the $\epsilon=+1$ branches and at least $2(2+2+1)=10$ from the listed $\epsilon=-1$ branches. This attains 26. Coss et al. give attainment for the equal-magnitude subfamily in their Theorem 4.12. [Coss et al., §4.3](https://arxiv.org/html/1705.06568v2#S4.SS3)

The note and the finite Lean certificate were prepared with OpenAI Codex.
