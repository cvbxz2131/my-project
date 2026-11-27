# Spectral instability of planar relative equilibria of five, six, and seven equal masses

Every collision-free relative equilibrium of $n\in\{5,6,7\}$ equal positive masses in the planar Newtonian problem is spectrally unstable. If the orbit rotates at angular speed $\Omega$, its linearization has an eigenvalue with real part strictly greater than $2\Omega/5$.

Moczurad and Zgliczyński proved that the central configurations for these body counts fall into $5$, $9$, and $14$ classes, respectively. Their 2020 paper reported floating-point evidence of instability for every class. This note proves the instability using outward-rounded integer interval arithmetic on the coordinate enclosures in their 2019 report. [Classification and report, Theorem 1 and Appendix A.1](https://arxiv.org/abs/1812.07279v3) · [Numerical stability study, §8](https://doi.org/10.1007/s10569-020-09993-1)

## Proof

Choose units so the gravitational constant, the total mass, and the angular speed are one. Translate the origin to the center of mass. Changes of length and time units preserve the sign of the real parts of characteristic exponents. With $J=\begin{pmatrix}0&-1\\1&0\end{pmatrix}$, the acceleration in the rotating frame is

$$
\ddot q_i=-2J\dot q_i+q_i-\frac1n\sum_{j\ne i}
\frac{q_i-q_j}{\lVert q_i-q_j\rVert^3}.
$$

A relative equilibrium is stationary in these coordinates. Write $\mathcal J=\operatorname{diag}(J,\ldots,J)$ and let $K$ be the $2n\times 2n$ position derivative of the acceleration. For $d_{ij}=q_i-q_j$ and $r_{ij}=\lVert d_{ij}\rVert$, each pair contributes

$$
C_{ij}=\frac{1}{n r_{ij}^3}
\left(\frac{3d_{ij}d_{ij}^{\mathsf T}}{r_{ij}^2}-I_2\right).
$$

Starting from $K=I_{2n}$, add $C_{ij}$ to diagonal blocks $(i,i)$ and $(j,j)$ and subtract it from off-diagonal blocks $(i,j)$ and $(j,i)$. The rotating-frame Jacobian is then

$$
A=\begin{pmatrix}0&I_{2n}\\K&-2\mathcal J\end{pmatrix}.
$$

Its characteristic polynomial is $\det(z^2 I_{2n}+2z\mathcal J-K)$. Because $K$ is symmetric and $\mathcal J$ is skew-symmetric, transposition shows this polynomial is even. Thus an eigenvalue with nonzero real part gives one with strictly positive real part. Rotations and relabelings conjugate the matrices. A reflection changes the sign of the conjugated Coriolis block, which preserves the characteristic polynomial by the same transposition identity. The result for each representative therefore covers its entire equivalence class in the published classification.

If all eigenvalues $\lambda_j$ of $A$ were purely imaginary, then for every positive integer $k$ we would have

$$
T_k=\operatorname{tr}((-A^2)^k)
   =\sum_j(-\lambda_j^2)^k\ \geq\ 0 .
$$

The trace identity counts eigenvalues with algebraic multiplicity. The interval calculation below proves that every configuration box has $T_k<0$ throughout the box for some $k\in\{1,2,3\}$. This excludes purely imaginary spectrum at every relative equilibrium in the classification.

## Quantitative growth bound

We continue in the units where $\Omega=1$. On position perturbations that translate all bodies by the same vector, the pair contributions cancel and $K=I_2$. The four-dimensional block for translations and their velocities has characteristic polynomial $(z^2+1)^2$. The position plane spanned by the central configuration $q$ and $\mathcal Jq$ is also invariant. Homogeneity of the gravitational acceleration of degree $-2$ gives $Kq=3q$ at a stationary point. Rotational equivariance gives $K\mathcal Jq=0$. The block for this plane and its velocities has characteristic polynomial $z^2(z^2+1)$. This plane has center of mass zero and is independent of the translations.

These two invariant blocks give two zero eigenvalues and three pairs $\pm i$. They contribute $6$ to each of the traces $T_k$, leaving $4n-8$ eigenvalues counted with multiplicity.

For $\lambda=a+ib$, the following bounds on a single term hold:

$$
\operatorname{Re}((-\lambda^2)^k)\geq-c_k |a|^{2k},
\qquad (c_1,c_2,c_3)=(1,8,356).
$$

For $k=1$ the real part is $b^2-a^2$. For $k=2$ it is $(b^2-3a^2)^2-8a^4$. For $k=3$ and $a\ne0$, divide by $a^6$ and put $y=b^2/a^2$. The polynomial $y^3-15y^2+15y-1$ on $y\geq0$ attains its minimum $-176-80\sqrt5>-356$ at $y=5+2\sqrt5$. The inequality for $a=0$ follows directly.

If all real parts had magnitude at most $2/5$, the trace would satisfy

$$
T_k\geq 6-(4n-8)c_k(2/5)^{2k}.
$$

For each configuration box the checker finds an upper bound $U_k$ for its selected trace and verifies $6-(4n-8)c_k(2/5)^{2k}-U_k>0$ exactly. The smallest of these positive margins over the 28 boxes is $2307289636282469/10^{15}$. This contradicts the assumed bound on all real parts. Evenness of the characteristic polynomial gives an eigenvalue with real part greater than $2/5$. Restoring the time unit multiplies the bound by $\Omega$.

## Certificate and reproduction

The checker reads the $28$ coordinate boxes from the pinned report appendix. It widens each printed coordinate interval by $10^{-6}$ to cover the rounding of its displayed endpoints, then stores endpoints as integers with a common denominator $10^{15}$. Products and positive reciprocals round outwards by integer division. Positive square roots round outwards using integer square roots. These enclosure rules apply successively to the pair distances, matrix entries, and traces. The input report is identified by its SHA-256 digest in the checker.

Run from the repository root with Python 3. On Windows PowerShell, use the executable name curl.exe.

~~~sh
curl -fL https://arxiv.org/src/1812.07279v3 -o arxiv-1812.07279v3.tar.gz
python equal-mass-relative-equilibria/check_instability.py arxiv-1812.07279v3.tar.gz
~~~

The script prints the first successful $k$, the exact rational trace upper bound, and the margin for the growth bound for every published box. It exits with an error if a required strict inequality fails. [Python checker](check_instability.py)

| Bodies | Verified boxes | First success at $k=1,2,3$ | Largest of the selected upper bounds |
| ---: | ---: | :---: | ---: |
| 5 | 5 | 1, 3, 1 | $-4476628384665312/10^{15}$ |
| 6 | 9 | 2, 4, 3 | $-4437179473941632/10^{15}$ |
| 7 | 14 | 6, 5, 3 | $-403289636282469/10^{15}$ |

## Relation to earlier work

Equal-mass instability is a consequence of the dominant-mass question attributed to Rick Moeckel in Problem 15 of Albouy, Cabral, and Santos. Roberts used the squared eigenvalues to derive an instability criterion and proved a general equal-mass result for $n\ge 24306$. The present calculation uses the known complete classification for $n=5,6,7$ and tests traces up to the sixth power of the Jacobian. [Problem 15](https://arxiv.org/abs/1305.3191) · [Roberts, *Spectral instability of relative equilibria in the planar n-body problem*](https://mathcs.holycross.edu/~groberts/Papers/EqualMass.pdf)

The note and checker were prepared with OpenAI Codex.
