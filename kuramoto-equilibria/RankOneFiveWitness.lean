import Std

/-!
Integer certificates for the crossings in the five-oscillator example.
The analytical reduction to the branch functions and the intermediate
value argument are given in the accompanying note.
-/

namespace RankOneFiveWitness

def scale : Nat := 100000000

/-- Absolute values of ωᵢ/(s kᵢ), with denominator 100. -/
def ratioNumerators : List Nat := [96, 97, 98, 99, 100]

/-- Weights kᵢ, with denominator 10. -/
def weightNumerators : List Nat := [10, 10, 10, 10, 39]

def frequencyNumerators : List Int := [-96, -97, -98, -99, 390]

structure Sample where
  z : Nat
  lower : List Nat
  upper : List Nat

def first : Sample :=
  ⟨1, [28000000, 24310491, 19899748, 14106735, 0],
      [28000000, 24310492, 19899749, 14106736, 0]⟩

def middle : Sample :=
  ⟨4, [175453697, 174902830, 174344486, 173778594, 173205080],
      [175453698, 174902831, 174344487, 173778595, 173205081]⟩

def last : Sample :=
  ⟨4000000, [199999976959, 199999976477, 199999975989, 199999975497, 199999974999],
            [199999976960, 199999976478, 199999975990, 199999975498, 199999975000]⟩

def sampleBoundsValid (sample : Sample) : Bool :=
  sample.lower.length == 5 && sample.upper.length == 5 &&
    (List.range 5).all fun i =>
      let numerator := ratioNumerators[i]!
      let radicand := (10000 * sample.z - numerator ^ 2) * (scale / 100) ^ 2
      10000 * sample.z >= numerator ^ 2 &&
        sample.lower[i]! ^ 2 <= radicand && radicand <= sample.upper[i]! ^ 2

def signVectors : List (List Bool) :=
  (List.range 32).map fun mask =>
    (List.range 5).map fun i => mask / (2 ^ i) % 2 == 1

def residualBounds (sample : Sample) (signs : List Bool) : Int × Int :=
  let linear : Int := -(Int.ofNat (scale * sample.z))
  (List.range 5).foldl (fun (lo, hi) i =>
    let coefficient := 20 * weightNumerators[i]!
    let a := Int.ofNat (coefficient * sample.lower[i]!)
    let b := Int.ofNat (coefficient * sample.upper[i]!)
    if signs[i]! then (lo + a, hi + b) else (lo - b, hi - a)) (linear, linear)

def residualSign (sample : Sample) (signs : List Bool) : Int :=
  let (lo, hi) := residualBounds sample signs
  if 0 < lo then 1 else if hi < 0 then -1 else 0

def crossingCount (a b : Sample) : Nat :=
  (signVectors.filter fun signs => residualSign a signs != residualSign b signs).length

/-- Frequencies use denominator 100000 and s is 1/1000. -/
theorem inputs_valid :
    frequencyNumerators.sum = 0 ∧
      (List.range 5).all (fun i =>
        10 * (frequencyNumerators[i]!).natAbs == weightNumerators[i]! * ratioNumerators[i]!) = true := by
  decide

theorem radical_enclosures :
    [first, middle, last].all sampleBoundsValid = true := by decide

theorem sign_vectors_are_distinct : signVectors.eraseDups.length = 32 := by decide

theorem endpoint_signs_are_strict :
    [first, middle, last].all
      (fun sample => signVectors.all fun signs => residualSign sample signs != 0) = true := by
  decide

theorem inner_crossings : crossingCount first middle = 14 := by decide

theorem outer_crossings : crossingCount middle last = 16 := by decide

theorem thirty_brackets : crossingCount first middle + crossingCount middle last = 30 := by decide

#print axioms inputs_valid
#print axioms radical_enclosures
#print axioms sign_vectors_are_distinct
#print axioms endpoint_signs_are_strict
#print axioms thirty_brackets

end RankOneFiveWitness
