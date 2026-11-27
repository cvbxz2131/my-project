# Two exact extrema in finite-dimensional quantum information

## 1. Global Wigner negativity of a single five-level system

In the Gross phase-point convention, take $q,p,x,y\in\mathbb F_5$ and
$\zeta=\exp(2\pi i/5)$. The operator entries are
$A_{q,p}[x,y]=\mathbf 1_{x+y=2q}\zeta^{p(x-y)}$ and the Wigner values
are $W_\rho(q,p)=\operatorname{Tr}(A_{q,p}\rho)/5$.
Write $\mathrm{sn}(\rho)=\sum_{W_\rho(q,p)<0}|W_\rho(q,p)|$. Then

$$
\max_{\rho}\mathrm{sn}(\rho)
=\frac{\sqrt 5+\sqrt{15+6\sqrt 5}-2}{10}.
$$

Exactly 500 pure-state projectors attain equality. They form one orbit
of the single-system Clifford group. The pure states in Erew and
Goldstein's equation (4.40e) attain this value. Their paper gives the
same evaluation in Appendix F and proves local maximality in Section
4.4.2. The result here supplies the global bound and all equality cases.
[Gross, 2006](https://arxiv.org/abs/quant-ph/0602001) ·
[Veitch et al., 2014, §4.4](https://arxiv.org/pdf/1307.7171#page=14) ·
[Erew and Goldstein, §4.4 and Appendix F](https://arxiv.org/html/2512.19657v2#S4.SS4)

### Exact certificate

For a subset $T$ of the 25 phase points, put $A_T=\sum_{u\in T}A_u$.
For any state, $5\,\mathrm{sn}(\rho)$ is the maximum of
$-\operatorname{Tr}(A_T\rho)$ over $T$. The spectral theorem gives
$5\max_\rho\mathrm{sn}(\rho)=-\min_T\lambda_{\min}(A_T)$.

The affine symplectic group on $\mathbb F_5^2$ has 3000 elements.
Translations, quadratic diagonal phases and the Fourier transform act
on the phase-point operators by unitary conjugation. With $X|x\rangle
=|x+1\rangle$ and $Z|x\rangle=\zeta^x|x\rangle$, $X^rZ^s$ translates
by $(r,s)$. The diagonal phase $\zeta^{t x^2/2}$ sends $(q,p)$ to
$(q,p+tq)$. The Fourier matrix with entries $\zeta^{xy}/\sqrt5$ sends
$(q,p)$ to $(-p,q)$. The shear and rotation generate
$\operatorname{SL}(2,\mathbb F_5)$ by elementary row operations. Thus
one representative per orbit suffices.

There are 11,408 orbits on subsets. The code uses bit $5q+p$ for phase
point $(q,p)$ and starts with mask 18874956, namely

$$
T_* = \{(0,2),(0,3),(1,1),(1,4),(4,1),(4,4)\}.
$$

For every other orbit, $139 I+50 A_T$ has five positive unscaled Schur
pivots. The leading four-dimensional compression of $139 I+50 A_{T_*}$
has four positive pivots. At each step write the current Hermitian
matrix in blocks $\bigl(\begin{smallmatrix}a& b^*\\b&D\end{smallmatrix}\bigr)$.
The next matrix is $aD-bb^*$. When $a>0$, completing one square
shows that positivity of the original matrix is equivalent to positivity
of the next matrix. The code uses integer coefficients of
$1,\zeta,\ldots,\zeta^4$ with $\zeta^5=1$. For conjugate-symmetric
coefficients $(c_0,c_1,c_2,c_2,c_1)$ the value is
$(c_0-c_2)+(c_1-c_2)\tau$, where $\tau=(\sqrt5-1)/2$. Comparing
integer squares certifies each sign.

Set $\lambda=(2-\sqrt5-\sqrt{15+6\sqrt5})/2<-139/50$. The winning
matrix is

$$
A_{T_*} =
\begin{pmatrix}
2&0&-1-\tau&-1-\tau&0\\
0&2&\tau&0&\tau\\
-1-\tau&\tau&0&-1-\tau&0\\
-1-\tau&0&-1-\tau&0&\tau\\
0&\tau&0&\tau&2
\end{pmatrix}.
$$

The vector $(u,v,w,w,v)$ with

$$
u=2(1+\tau)(2+\tau-\lambda),\qquad
v=-\tau(2-\lambda),\qquad
w=(2-\lambda)(2+\tau-\lambda)
$$

is a $\lambda$-eigenvector. Substitution uses
$\tau^2+\tau=1$ and
$\lambda^2-(1-2\tau)\lambda-(4+5\tau)=0$. Its fifth component $v$
is nonzero. On the hyperplane with fifth coordinate zero,
$A_{T_*}-\lambda I$ is positive definite by the compression check
and $\lambda<-139/50$. Subtracting a multiple of the eigenvector
puts any vector in that hyperplane and preserves the shifted quadratic
form. This proves that $\lambda$ is the simple bottom eigenvalue.

Only the winning orbit has bottom eigenvalue below $-139/50$. The
winning masks have six points and their orbit has size 500. Each
winning mask gives one pure eigenstate. Any global maximizer has
negative support equal to one winning mask and is supported on the
bottom eigenspace of that mask. A zero Wigner entry would allow
toggling one point and produce a winning mask of a different size.
Therefore the winning masks and maximizing pure projectors correspond
bijectively.

## 2. Strict Hesse optimality within the three-level SIC family

Let $\omega=\exp(2\pi i/3)$, $\alpha=\pi/9$, and
$\psi_{qp}(\theta)=(|q+1\rangle-e^{i\theta}\omega^p|q+2\rangle)/\sqrt2$
for $q,p\in\mathbb F_3$ and $0\le\theta\le\alpha$. The SIC effects
are $E_{qp}=|\psi_{qp}\rangle\langle\psi_{qp}|/3$. The critical
visibility $v^*(\theta)$ is the largest $v$ for which
$v E_{qp}+(1-v)I/9$ can be realized by a random projective measurement
followed by classical relabeling. The Hesse point is $\theta=0$.

$$
v^*(0)=\frac{1+4\cos\alpha}{6},\qquad
v^*(\theta)>v^*(0)\quad(0<\theta\le\alpha).
$$

Cobucci et al. give a projective decomposition at the Hesse point and
plot the comparison along the rest of this family using semidefinite
programming. The construction below supplies the strict comparison on
the whole interval. Unitary or antiunitary equivalence reduces all
three-level SIC-POVMs to this family. The broader extremal problem
over all three-level POVMs remains open in the cited work.
[Cobucci et al., Eq. (7), Figure 1 and Appendix D](https://arxiv.org/html/2508.03652v2) ·
[Brinster et al., Eq. (33)](https://arxiv.org/html/2511.04446v2)

### Coordinates of a symmetrized measurement

Let $b_j$ be three orthonormal basis vectors, assigned to labels
$(q_j,p_j)$. Average over Weyl conjugations with the induced
relabeling, the diagonal $\operatorname{diag}(\omega,1,1)$, and the
antiunitary parity followed by conjugation. The diagonal maps label
$(q,p)$ to $(q,p+q)$, and parity followed by conjugation sends
$(q,p)$ to $(-q,p)$. The ensemble uses ordinary projective measurements
in the resulting bases. Its normalized seed $3E_{00}$ has population
$r$ at coordinate 0, equal populations $(1-r)/2$ at 1 and 2, zero
entries connecting 0 to 1 and 2, and entry $-e^{-i\theta}c/2$
at row 1, column 2. Directly averaging the seed gives

$$
r=\frac{1}{3}\sum_j |b_j[q_j]|^2,\qquad
c=-\frac{2e^{i\theta}}{3}
\sum_j\omega^{p_j}b_j[q_j+1]\overline{b_j[q_j+2]}.
$$

The depolarized target of visibility $v$ is $(r,c)=((1-v)/3,v)$.

### The Hesse endpoint and its decomposition

For each unordered noncollinear triple of labels, use the columns of
the unitary polar factor of the matrix $V$ with columns the corresponding
Hesse state vectors. There are 72 such triples. The Weyl group, the
diagonal above and the discrete Fourier transform act on labels as
translations, a shear and a rotation. They act transitively on
noncollinear unordered triples. The uniform average of the resulting
labeled bases is covariant. Its seed commutes with the diagonal and
the Fourier transform, both of which fix $\psi_{00}(0)$ up to a phase.
Fourier squared is parity. On the two-dimensional complement of
$\psi_{00}(0)$, the diagonal separates $|0\rangle$ and
$(|1\rangle+|2\rangle)/\sqrt2$, and the Fourier transform mixes them.
The seed is therefore scalar on that complement.

For an explicit triple take missing coordinates $0,1,2$ with
$p=0,0,1$. Put $g=e^{2i\alpha}$ and $D=\operatorname{diag}(1,g^2,g)$.
This triple is, column by column up to phase, $D$ times the columns
of $(X-gX^2)/\sqrt2$, where $X$ shifts the computational coordinates.
In the Fourier basis with $Xf_k=\omega^k f_k$, the polar factor of
$(X-gX^2)/\sqrt2$ is, up to a common phase, $I-2f_1 f_1^*$.
Its phases can be read from
$\omega^k(1-g\omega^k)=-2i e^{i\alpha}(-1)^k
\sin(\alpha+k\pi/3)$ for $k=0,1,2$. The resulting
coordinates are $r=1/9$ and $c=(8/9)e^{-i\alpha}$.
The fidelity of each labeled column is
$[1-r+\operatorname{Re}(c)]/2=4(1+\cos\alpha)/9$.
By covariance the full Hesse average has exactly $v=v^*(0)$ as above.

To see optimality at the endpoint, use the witness
$\sum_a\operatorname{Tr}(|\psi_a\rangle\langle\psi_a|F_a)$.
It equals $1+2v$ on the depolarized SIC. It suffices to maximize over
rank-one orthogonal bases with deterministic labels. For three distinct
noncollinear labels rephase their vectors so their Gram matrix
$G=V^*V$ is circulant. This is possible because every off-diagonal
overlap has modulus $1/2$ and the phases on the three cyclic edges
can be made equal. If $d=\operatorname{Tr}(\sqrt G)/3$, every diagonal
of $\sqrt G$ equals $d$. In the polar frame
$d\sqrt{VV^*}\succeq|\psi_j\rangle\langle\psi_j|$ follows by
congruence from
$dI\succeq G^{1/4}|j\rangle\langle j|G^{1/4}$. The summed score is
at most $3d^2$, attained in the polar basis. For collinear triples the
Gram eigenvalues are $3/2,3/2,0$, so the same bound is 2 using a unitary
extension of the polar factor. For two distinct labels the bound is
$1+\sqrt3/2$ by the eigenvalues of the difference of their rank-one
projectors. One label gives score 1. Thus the endpoint construction
saturates the witness bound.

### Transport to every other parameter

Of the 72 triples, 54 use two missing coordinates and 18 use three.
The triples of the latter type have one label at each missing coordinate,
and their $p$ labels sum to $1$ or $2$ modulo 3, nine of each. Diagonal
rephasing reduces the first set to the explicit triple used above.
Conjugation gives the second set.

Write $C=\cos\alpha$ and $S=\sin\alpha$. At the endpoint the
equal-weight three-coordinate ensemble has $(r,c)=(1/9,8C/9)$.
The two-coordinate ensemble has real coordinates by conjugation.
Its weight $3/4$ in the full endpoint decomposition gives

$$
r_2=(9-8C)/27,\qquad c_2=(6+16C)/27.
$$

For each two-coordinate triple choose a diagonal rephasing that adds
$\theta$ to the relative phase of each of its two coordinate pairs.
The two edges impose independent conditions on the three phases.
The rephasing exactly cancels the new alignment factor, preserving
$(r_2,c_2)$.

Keep the three-coordinate bases from $\theta=0$. Their aligned
coherences are $(8/9)e^{i(\theta\pm\alpha)}$ and their population
is fixed. Put $x=\cos\theta$ and $y=\sin\theta$. Mix the positive-sign
ensemble with weight $(1-Cy/(Sx))/2$, which belongs to $[0,1/2]$
because $Sx-Cy=\sin(\alpha-\theta)\ge0$. The new coordinates are
$(1/9,8C/(9x))$. The mixture with the two-coordinate ensemble meets
$c=1-3r$ at three-coordinate weight

$$
w(x)=\frac{4C-3}{4C(1+3/x)-12}.
$$

At $x=1$ the weight is $1/4$. Throughout $0<\theta\le\alpha$ it
lies strictly between 0 and $1/4$, since $C>3/4$ and $x<1$.
Since $1/9>r_2$, this produces a strictly lower population and hence
a strictly larger visibility $1-3((1-w)r_2+w/9)$.

## Reproduction

The Lean installation is pinned by [lean-toolchain](lean-toolchain).
Mathlib is pinned by [lake-manifest.json](lake-manifest.json). From
this directory, run

~~~sh
lake exe cache get Mathlib.Tactic Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
lake --wfail build
lake env leanchecker -v HesseSIC WignerFiveComputation WignerFiveCertificate WignerFive
~~~

### Lean results

- [WignerFiveComputation.lean](WignerFiveComputation.lean) builds the
  orbit table, verifies the bitset coverage count of $2^{25}$ masks
  and checks the exact pivots for every representative.
  [WignerFiveCertificate.lean](WignerFiveCertificate.lean) proves that
  this calculation succeeds by compiler-backed Boolean reduction
  (`Lean.ofReduceBool`).
- [WignerFive.lean](WignerFive.lean) interprets the fifth-root
  coefficients, proves the Schur step and the exact quadratic bound
  on the representatives, and verifies the explicit eigenvector and
  radical value. The note supplies unitary covariance and the
  density-matrix and equality-classification arguments.
- [HesseSIC.lean](HesseSIC.lean) checks the triple counts, diagonal phase
  transport and orthonormality, and constructs the admissible mixture
  weights for every angle in the interval. The strict visibility
  theorem uses the three prototype seed measurements. The note
  supplies their projective realization and the endpoint witness.

The note and code were prepared with OpenAI Codex.
