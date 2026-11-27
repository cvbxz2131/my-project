import WignerFiveComputation

/-!
# Exhaustive single-ququint Wigner certificate

The Boolean procedure is imported as a compiled declaration so the
reflection proof can also be replayed by Lean's kernel checker.
-/

namespace WignerFive

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
/-- This exact calculation uses Lean's compiler-backed Boolean reduction. -/
theorem certificate_passes : checkCertificate = true :=
  Lean.ofReduceBool checkCertificate true (Eq.refl true)

theorem certified_pivots {m : Mask} {size : Nat} (hm : (m, size) ∈ orbitRepresentatives) :
    positivePivots (if m == winningMask then 4 else 5) (shiftedEntry m) = true :=
  pivots_of_certificate certificate_passes hm

end WignerFive
