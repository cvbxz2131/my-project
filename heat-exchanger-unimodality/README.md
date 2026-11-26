# A three-exchanger counterexample to the unimodality conjecture for minimal heat exchanger networks

Chang et al. (2020) conjectured that for a fixed minimal heat exchanger network, the total annualized cost as a function of hot utility demand has a single valley. A network with one process exchanger, one heater, and one cooler violates this conjecture. The example uses fixed film coefficients, linear area costs, and the logarithmic mean temperature difference. The same three operating points also violate unimodality with the Chen approximation. [Chang et al., 2020, p. 3](https://www.ou.edu/class/che-design/pub-papers/Globally%20Optimal%20Synthesis%20of%20Heat%20Exchanger%20Networks%20-%20Part%20I%20-%20Minimal%20Networks%28Chang%20et%20al%29-20.pdf#page=3)

A second choice of costs on the same network makes the paper's monotony test return a suboptimal utility demand. [Section 6 of Chang et al.](https://www.ou.edu/class/che-design/pub-papers/Globally%20Optimal%20Synthesis%20of%20Heat%20Exchanger%20Networks%20-%20Part%20I%20-%20Minimal%20Networks%28Chang%20et%20al%29-20.pdf#page=7)

## Network and feasibility

The hot process stream $H$ runs from 600 to 500 K, and the cold process stream $C$ runs from 300 to 400 K. Each has a heat capacity flow rate of 1 kW/K. Each stream passes through the countercurrent process exchanger first, then through its utility exchanger. The heater uses an isothermal utility at 410 K. The countercurrent cooler heats cooling water from 280 to 290 K, with the cooling water flow rate set by the cooling duty.

Let $E$ denote the hot utility duty in kW. The heat balance fixes the process exchanger duty at $100-E$ and the cooler duty at $E$. The stream temperatures between the process and utility exchangers are $500+E$ K on $H$ and $400-E$ K on $C$. Thus every duty is uniquely determined when $E$ is fixed. The graph of stream matches is the path HU–$C$–$H$–CU, so there is no energy loop. This is a minimal structure in the sense of Chang et al. [Definition of a minimal structure, p. 2](https://www.ou.edu/class/che-design/pub-papers/Globally%20Optimal%20Synthesis%20of%20Heat%20Exchanger%20Networks%20-%20Part%20I%20-%20Minimal%20Networks%28Chang%20et%20al%29-20.pdf#page=2)

| Unit | Duty (kW) | Terminal temperature differences (K) | Overall coefficient $U$ (kW/(m² K)) | Annual area charge (USD/(m² yr)) |
|---|---:|---|---:|---:|
| Process exchanger | $100-E$ | $200+E$, $200+E$ | $1/2$ | 600 |
| Heater | $E$ | $10$, $10+E$ | $5/6$ | 150 |
| Cooler | $E$ | $220$, $210+E$ | $1/2$ | 150 |

The film coefficients for $H$, $C$, and the cold utility are 1 kW/(m² K), and the hot utility film coefficient is 5 kW/(m² K). The overall coefficients in the table follow from adding the two film resistances. The hot and cold utility charges are 0.8 and 0.2 dollars per kW per year, respectively. For every $E\in[1,99]$, all three units have a duty of at least 1 kW and every terminal temperature difference is at least 10 K. The three points used below are therefore feasible with a 10 K minimum approach and a 1 kW minimum active duty.

## Cost and strict inequalities

For positive terminal differences $a,b$, let $R(a,b)$ be the reciprocal of their logarithmic mean. For $a\ne b$ it is $\ln(b/a)/(b-a)$, and at equality it is $1/a$. The area of each unit is its duty times $R(a,b)/U$. Fixed equipment costs contribute a constant because all three units remain active. After subtracting that constant, the annualized cost is

$$
F(E) = \frac{1200(100-E)}{200+E} + E
       + 180E R(10,10+E) + 300E R(220,210+E).
$$

| $E$ (kW) | $F(E)$ (dollars per year, approximate) |
|---:|---:|
| 5 | 640.98 |
| 40 | **680.83** |
| 95 | 648.12 |

To certify the comparison, sort the two terminal differences so that $a\le b$. Then

$$
R(a,b)=\int_0^1 \frac{dt}{a+(b-a)t}.
$$

The integrand is nonincreasing. Right and left endpoint sums on 64 equal subintervals give the rational bounds

$$
\sum_{j=1}^{64}\frac{1}{64a+j(b-a)}
\;\le R(a,b)\le\;
\sum_{j=0}^{63}\frac{1}{64a+j(b-a)}.
$$

Substituting the upper bounds at $E=5,95$ and the lower bounds at $E=40$ gives the strict inequalities

$$
F(5)<665<F(40), \qquad F(95)<665.
$$

A cost that weakly decreases up to a minimizer and then weakly increases must satisfy $F(y)\le\max(F(x),F(z))$ for $x<y<z$. The three points violate this condition. The integral representation also gives continuity at equal terminal differences. Consequently $F$ attains a maximum on $[5,95]$ at an interior point, which is a local maximum. The single-valley hypothesis used to justify golden-section search fails for this network.

## Chen approximation

Section 7 of Chang et al. uses Chen's approximation in the model that supplies a lower bound. With $\Delta T_{\mathrm{Ch}}=(ab(a+b)/2)^{1/3}$ substituted for the logarithmic mean, the same three points still satisfy the strict comparison about 665. The process exchanger has equal terminal differences, for which the two means agree. For the utility exchangers, a floor $m$ is certified by $2m^3\le ab(a+b)<2(m+1)^3$.

| $E$ (kW) | Heater floor $m$ (K) | Cooler floor $m$ (K) |
|---:|---:|---:|
| 5 | 12 | 217 |
| 40 | 24 | 234 |
| 95 | 39 | 260 |

Replacing the two utility temperature means by their floors $m$ gives upper cost bounds at 5 and 95 kW. Replacing those means by $m+1$ gives a lower cost bound at 40 kW. [Chang et al., §7](https://doi.org/10.1002/aic.16267)

## A suboptimal result from the monotony test

Keep the same stream and equipment data, change the heater area charge to $250/3$ dollars per square metre per year, and set the hot and cold utility charges to 2 and 1 dollars per kW per year, respectively. Take the user bounds on hot utility demand to be 23 and 95 kW, as allowed by equations (12) and (18). Every $E\in[23,95]$ remains feasible for the three-exchanger network, so these are its minimum and maximum within the user bounds. [Chang et al., §4](https://www.ou.edu/class/che-design/pub-papers/Globally%20Optimal%20Synthesis%20of%20Heat%20Exchanger%20Networks%20-%20Part%20I%20-%20Minimal%20Networks%28Chang%20et%20al%29-20.pdf#page=6)

Subtracting the fixed charges gives the new annual cost

$$
G(E)=\frac{1200(100-E)}{200+E}+3E+100E R(10,10+E)+300E R(220,210+E).
$$

Section 6 starts by comparing the costs at 23 kW, 95 kW, and the interior sample $E_\phi=23+72/\phi=36\sqrt{5}-13$, where $\phi=(1+\sqrt5)/2$. Since 23 kW has the lowest cost of these three, the test evaluates $G(23.01)$. Its step 3 declares 23 kW optimal when the cost increases at this probe. [Chang et al., §6](https://www.ou.edu/class/che-design/pub-papers/Globally%20Optimal%20Synthesis%20of%20Heat%20Exchanger%20Networks%20-%20Part%20I%20-%20Minimal%20Networks%28Chang%20et%20al%29-20.pdf#page=7)

| Hot utility demand (kW) | Exact LMTD cost (USD/year, rounded) | Chen cost (USD/year, rounded) |
|---:|---:|---:|
| 23 | 633.213966 | 633.517002 |
| 23.01 | 633.214463 | 633.517869 |
| $E_\phi \approx 67.498447$ | 634.835637 | 638.616670 |
| 95 | 650.011809 | 657.037200 |
| 40 | **632.077140** | **633.325421** |

The strict comparisons are $G(40)<G(23)<\min\{G(23.01),G(E_\phi),G(95)\}$ for either choice of temperature mean. Thus the test reports 23 kW even though 40 kW gives a lower annual cost on the same fixed network.

### Rational certificate

For the logarithmic mean, let $z=(b-a)/(b+a)$, with $0<a<b$, and put $L=2\sum_{j=0}^{23}z^{2j+1}/(2j+1)$. Integrating the finite geometric expansion of $1/(1-t^2)$ from $0$ to $z$ gives

$$
L\le\ln(b/a)\le L+\frac{2z^{49}}{49(1-z^2)}.
$$

Divide by $b-a$ to enclose $R(a,b)$. For the Chen mean, the certificate brackets $10^5\Delta T_{\mathrm{Ch}}$ between $m$ and $m+1$ by comparing their cubes with $10^{15}ab(a+b)/2$. Reciprocating these positive bounds encloses the corresponding reciprocal mean.

The positive numbers $(67.49+13)/36$ and $(67.50+13)/36$ have squares below and above 5, respectively, so $67.49<E_\phi<67.50$. For a cost over an interval $[\ell,h]$, its process exchanger area charge and the reciprocal means decrease with $E$, while the utility duties and usage charges increase. A lower bound uses $h$ for the process charge and reciprocal means and $\ell$ for the utility duties and usage charges. An upper bound reverses those choices. The four other sample points use degenerate intervals. These enclosures establish the strict comparisons in both columns.

## Reproduction

Run this from the repository root with Elan. The root toolchain pins Lean 4.28.0 and the certificate uses its standard library.

~~~sh
lean -DwarningAsError=true -t 0 heat-exchanger-unimodality/HeatExchangerUnimodality.lean
lean -DwarningAsError=true -t 0 heat-exchanger-unimodality/MonotonyTestFailure.lean
~~~

[The unimodality certificate](HeatExchangerUnimodality.lean) verifies the rational comparisons for the three-point peak. [The monotony-test certificate](MonotonyTestFailure.lean) verifies the golden-section sample bracket, the Chen cube brackets, and the strict cost comparisons that make the test return a suboptimal point. The connection between these arithmetic comparisons, the physical model, and the algorithm is proved above. Both files compile with warnings treated as errors and pass kernel replay via leanchecker.

## Related work and priority

Quesada and Grossmann's 1992 technical report gives a one-dimensional fixed-topology example with two local optima. Its Figure 2 varies the duty in one of two process branches at constant external hot utility load. In the Chang et al. conjecture the independent variable is total hot utility demand, and that demand uniquely determines the duties. Oliva et al. explicitly retained the unimodality conjecture as a premise of the original method's global optimality guarantee in 2024. [Quesada and Grossmann, 1992, Figure 2](https://ndownloader.figshare.com/files/11894972#page=39) · [Journal version, 1993](https://doi.org/10.1021/ie00015a012) · [Oliva et al., 2024](https://doi.org/10.1002/aic.18450)

The literature check through 27 November 2026 covered exact-title and DOI searches, the OpenAlex, Semantic Scholar, and OpenCitations citation records, and the most relevant follow-up papers. It found no published counterexample to this specific conjecture. The article cites supplementary Appendix C in its discussion of the conjecture. The publisher's supplementary files could not be retrieved for review, so priority remains undetermined. [Wiley supporting information](https://aiche.onlinelibrary.wiley.com/doi/10.1002/aic.16267#support-information-section)

This note and the Lean certificates were prepared with OpenAI Codex.
