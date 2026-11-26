import Std

namespace MonotonyTest

/-- For b > a > 0, bound the reciprocal logarithmic mean with 24 terms of
the series for log(b/a) and a geometric bound on its tail. -/
def logMeanReciprocalBounds (a b : Rat) : Rat × Rat :=
  let z := (b - a) / (b + a)
  let partialSum := 2 * ((List.range 24).map fun k =>
    z ^ (2 * k + 1) / ((2 * k + 1 : Nat) : Rat)).sum
  let tail := 2 * z ^ 49 / (49 * (1 - z ^ 2))
  (partialSum / (b - a), (partialSum + tail) / (b - a))

def chenScale : Rat := 100000

def scaledChenCube (a b : Rat) : Rat :=
  chenScale ^ 3 * a * b * (a + b) / 2

/-- Find a candidate floor of the scaled Chen mean. The cube brackets are
checked on all inputs to the cost comparisons below. -/
def chenFloor (cube : Rat) : Nat :=
  ((List.range 26).foldl (fun (bracket : Nat × Nat) _ =>
    let mid := (bracket.1 + bracket.2) / 2
    if (mid : Rat) ^ 3 ≤ cube then (mid, bracket.2) else (bracket.1, mid))
    (0, 2 ^ 26)).1

abbrev chenBracket (a b : Rat) : Prop :=
  let cube := scaledChenCube a b
  let lower := chenFloor cube
  0 < lower ∧ (lower : Rat) ^ 3 ≤ cube ∧ cube < ((lower : Rat) + 1) ^ 3

def chenMeanReciprocalBounds (a b : Rat) : Rat × Rat :=
  let lower := (chenFloor (scaledChenCube a b) : Rat)
  (chenScale / (lower + 1), chenScale / lower)

def goldenSampleLower : Rat := 6749 / 100
def goldenSampleUpper : Rat := 6750 / 100

/-- The golden-section sample is 36*sqrt(5) - 13. -/
theorem goldenSampleBracket :
    ((goldenSampleLower + 13) / 36) ^ 2 < 5 ∧
    5 < ((goldenSampleUpper + 13) / 36) ^ 2 := by
  decide +kernel

abbrev chenBracketsAt (e : Rat) : Prop :=
  chenBracket 10 (10 + e) ∧ chenBracket 220 (210 + e)

theorem chenCubeBrackets :
    chenBracketsAt 23 ∧ chenBracketsAt (2301 / 100) ∧
    chenBracketsAt goldenSampleLower ∧ chenBracketsAt goldenSampleUpper ∧
    chenBracketsAt 95 ∧ chenBracketsAt 40 := by
  decide +kernel

/-- Enclose the cost at any E in [lo, hi]. The recovery charge and the
reciprocal means decrease with E. The utility loads and charges increase. -/
def costBounds (meanBounds : Rat → Rat → Rat × Rat) (lo hi : Rat) : Rat × Rat :=
  let heaterAtHigh := meanBounds 10 (10 + hi)
  let coolerAtHigh := meanBounds 220 (210 + hi)
  let heaterAtLow := meanBounds 10 (10 + lo)
  let coolerAtLow := meanBounds 220 (210 + lo)
  (1200 * (100 - hi) / (200 + hi) + 3 * lo +
      100 * lo * heaterAtHigh.1 + 300 * lo * coolerAtHigh.1,
   1200 * (100 - lo) / (200 + lo) + 3 * hi +
      100 * hi * heaterAtLow.2 + 300 * hi * coolerAtLow.2)

abbrev testComparisons (meanBounds : Rat → Rat → Rat × Rat) : Prop :=
  let atMinimum := costBounds meanBounds 23 23
  let atProbe := costBounds meanBounds (2301 / 100) (2301 / 100)
  let atGoldenSample := costBounds meanBounds goldenSampleLower goldenSampleUpper
  let atMaximum := costBounds meanBounds 95 95
  let atBetterPoint := costBounds meanBounds 40 40
  atBetterPoint.2 < atMinimum.1 ∧
    atMinimum.2 < atProbe.1 ∧
    atMinimum.2 < atGoldenSample.1 ∧
    atMinimum.2 < atMaximum.1

theorem exactLmtdTestFailure : testComparisons logMeanReciprocalBounds := by
  decide +kernel

theorem chenTestFailure : testComparisons chenMeanReciprocalBounds := by
  decide +kernel

#print axioms goldenSampleBracket
#print axioms chenCubeBrackets
#print axioms exactLmtdTestFailure
#print axioms chenTestFailure

end MonotonyTest
