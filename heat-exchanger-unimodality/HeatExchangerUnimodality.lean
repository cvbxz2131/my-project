import Std

/-!
Arithmetic certificate for the three-exchanger counterexample in README.md.
The first two terms of the cost are the process exchanger area charge and
the combined utility usage charge. The two other terms are the utility
exchanger area charges.
-/

def baseAnnualCost (e : Nat) : Rat :=
  1200 * ((100 - e : Nat) : Rat) / (200 + (e : Rat)) + (e : Rat)

/-- Bounds on the reciprocal logarithmic mean for 0 < a ≤ b.
Use firstIndex = 0 for left endpoints and firstIndex = 1 for right endpoints. -/
def inverseLogMeanSum (a b firstIndex : Nat) : Rat :=
  ((List.range 64).map fun i =>
    1 / ((64 * a + (b - a) * (i + firstIndex) : Nat) : Rat)).sum

def annualCostBound (e firstIndex : Nat) : Rat :=
  let coolerInletDifference := 210 + e
  let coolerOutletDifference := 220
  baseAnnualCost e +
    180 * (e : Rat) * inverseLogMeanSum 10 (10 + e) firstIndex +
    300 * (e : Rat) * inverseLogMeanSum
      (min coolerInletDifference coolerOutletDifference)
      (max coolerInletDifference coolerOutletDifference) firstIndex

theorem annualCostBounds :
    annualCostBound 5 0 < 665 ∧
    665 < annualCostBound 40 1 ∧
    annualCostBound 95 0 < 665 := by
  decide +kernel

/-- The integer bracket [floor, floor + 1) for the Chen mean. -/
abbrev chenMeanBracket (a b floor : Nat) : Prop :=
  2 * floor ^ 3 ≤ a * b * (a + b) ∧ a * b * (a + b) < 2 * (floor + 1) ^ 3

theorem chenMeanBounds :
    chenMeanBracket 10 15 12 ∧ chenMeanBracket 220 215 217 ∧
    chenMeanBracket 10 50 24 ∧ chenMeanBracket 220 250 234 ∧
    chenMeanBracket 10 105 39 ∧ chenMeanBracket 220 305 260 := by
  decide +kernel

def chenCostAtMeans (e heaterMean coolerMean : Nat) : Rat :=
  baseAnnualCost e + 180 * (e : Rat) / (heaterMean : Rat) +
    300 * (e : Rat) / (coolerMean : Rat)

theorem chenAnnualCostBounds :
    chenCostAtMeans 5 12 217 < 665 ∧
    665 < chenCostAtMeans 40 25 235 ∧
    chenCostAtMeans 95 39 260 < 665 := by
  decide +kernel

#print axioms annualCostBounds
#print axioms chenMeanBounds
#print axioms chenAnnualCostBounds
