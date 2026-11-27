import Std

/-!
# The tetrahedral case of the 18-photon two-mode loss problem

The distance-five question was posed by Giannisis Manes, Subramanian and
Jiang, arXiv:2610.00561v1, Sec. VIII.3, Table S4. Yuxuan Zhang's public
manuscript of 10 November 2026 gives exact third-moment certificates for the
unrestricted lower bound in the equivalent symmetric-qubit model.
https://yuxuanzhang1995.github.io/agentic-research/symmetric-two-error-code-length/

The argument below independently excludes tetrahedrally invariant rank-two
codes in the fixed 18-photon sector. Octahedral and icosahedral rotation
groups both contain a tetrahedral subgroup.

In the spin-9 representation the three orthogonal half-turns form a Klein
four group. A tetrahedral 120-degree rotation permutes its three nontrivial
characters transitively. A two-dimensional invariant subspace therefore lies
in the common fixed space of the half-turns. A half-turn about z acts on
`|k,18-k>` by `(-1)^(k-9)` and a half-turn about x acts by
`|k,18-k> ↦ -|18-k,k>`. The common fixed space has the orthonormal basis of
normalized antisymmetric pairs at k = 1, 3, 5, 7 in that order.

Correcting four losses requires the compression of each polynomial of degree
at most four in the collective spin operators to be scalar. This follows
from the loss error products by normal ordering, or from the loss–spin
equivalence in the source. On the four-dimensional space, D = J_z² has
diagonal (64,36,16,4) and X = J_+² + J_-² is tridiagonal with squared
off-diagonal entries (1632,4200,6552).

Let W be a four-by-two isometry onto a putative code and let B_i be the
rank-at-most-one positive matrix formed from row i of W. Scalar compression
of I, D, D² puts the tuple of traceless parts of B_i in the moment kernel
spanned by (2,-9,14,-7), since the three-row Vandermonde matrix has rank 3.
The common traceless factor is nonzero because otherwise all B_i vanish.
In its eigenbasis the signs give disjoint codeword supports {1,3} and {2,4}.
Rank one and normalization force the squared amplitudes to be (2,14)/16 and
(9,7)/16, respectively.

Call the three terms of the off-diagonal compression of X u, v, w in
edge order. Scalar compression of X and DX+XD requires
u+v+w = 0 and 100u+52v+20w = 0, giving v = -(5/2)u. Yet the prescribed
amplitudes and couplings give |v/u|² = (14*4200)/(2*1632) = 1225/68,
distinct from 25/4. The argument includes arbitrary complex codewords.

The code below checks these integer and rational calculations.
-/

def moment (degree : Nat) : Int :=
  ((([64, 36, 16, 4] : List Int).zip [2, -9, 14, -7]).map fun (x, weight) =>
    weight * x ^ degree).sum

theorem momentKernelWeights :
    moment 0 = 0 ∧ moment 1 = 0 ∧ moment 2 = 0 := by
  decide +kernel

def squaredSpinCoupling (k : Nat) : Nat :=
  (18 - k) * (17 - k) * (k + 1) * (k + 2)

theorem spinCouplings :
    squaredSpinCoupling 1 = 1632 ∧
    squaredSpinCoupling 3 = 4200 ∧
    squaredSpinCoupling 5 = 6552 := by
  decide +kernel

def requiredSquaredRatio : Rat :=
  (((64 + 36 - (16 + 4) : Rat) / (36 + 16 - (16 + 4))) ^ 2)

def squaredAmplitudeRatio : Rat :=
  ((14 * squaredSpinCoupling 3 : Nat) : Rat) /
    ((2 * squaredSpinCoupling 1 : Nat) : Rat)

theorem incompatibleSquaredRatios :
    requiredSquaredRatio = 25 / 4 ∧
    squaredAmplitudeRatio = 1225 / 68 ∧
    squaredAmplitudeRatio ≠ requiredSquaredRatio := by
  decide +kernel

#print axioms momentKernelWeights
#print axioms spinCouplings
#print axioms incompatibleSquaredRatios
