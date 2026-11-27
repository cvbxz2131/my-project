import Std.Tactic

/-!
# Exact arithmetic for the single-ququint Wigner certificate

A bit at position `5*q+p` includes the phase point `(q,p)`. Affine maps
are enumerated over the field with five elements. The arithmetic is in
the integral group ring on a fifth root of unity.
-/

namespace WignerFive

abbrev Mask := UInt32

def phaseSpaceSize : Nat := 25
def maskCount : Nat := 2 ^ phaseSpaceSize

def winningMask : Mask := 18874956

structure Affine where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  qShift : Nat
  pShift : Nat
  deriving Inhabited

def Affine.point (g : Affine) (i : Nat) : Nat :=
  let q := i / 5
  let p := i % 5
  5 * ((g.a * q + g.b * p + g.qShift) % 5) +
    ((g.c * q + g.d * p + g.pShift) % 5)

def affineMaps : Array Affine := Id.run do
  let mut maps := #[]
  for a in [0:5] do
    for b in [0:5] do
      for c in [0:5] do
        for d in [0:5] do
          if (a * d + 25 - b * c) % 5 == 1 then
            for q in [0:5] do
              for p in [0:5] do
                maps := maps.push ⟨a, b, c, d, q, p⟩
  return maps

def hasPoint (m : Mask) (i : Nat) : Bool :=
  (m >>> i.toUInt32) &&& 1 == 1

def transform (g : Affine) (m : Mask) : Mask :=
  (List.range phaseSpaceSize).foldl (fun u i =>
    if hasPoint m i then u ||| (1 <<< (g.point i).toUInt32) else u) 0

-- Tabulate the action on each eight-bit block once for the orbit traversal.
private def actionTable (g : Affine) (block : Nat) : Array Mask := Id.run do
  let mut table : Array Mask := #[0]
  for x in [1:2 ^ min 8 (phaseSpaceSize - 8 * block)] do
    let low := x &&& (2 ^ 8 - x)
    let dest := g.point (8 * block + low.log2)
    table := table.push (table[x - low]! ||| (1 <<< dest.toUInt32))
  return table

private def images (table : Array (Array Mask)) (m : Mask) : Mask :=
  table[0]![(m &&& 255).toNat]! |||
    table[1]![((m >>> 8) &&& 255).toNat]! |||
    table[2]![((m >>> 16) &&& 255).toNat]! |||
    table[3]![(m >>> 24).toNat]!

private def orbitTables : Array (Array (Array Mask)) :=
  affineMaps.map fun g => #[actionTable g 0, actionTable g 1, actionTable g 2, actionTable g 3]

private def markOrbit (tables : Array (Array (Array Mask))) (seen : ByteArray)
    (m : Mask) (count : Nat) : ByteArray × Nat := Id.run do
  let mut seen := seen
  let mut count := count
  for table in tables do
    let n := (images table m).toNat
    if seen[n]! == 0 then
      count := count + 1
      seen := seen.set! n 1
  return (seen, count)

/-- Visit the winning orbit first, then scan all masks in increasing order. -/
def orbitRepresentatives : Array (Mask × Nat) := Id.run do
  let tables := orbitTables
  let (initial, size) := markOrbit tables (⟨Array.replicate maskCount 0⟩ : ByteArray) winningMask 0
  let mut seen := initial
  let mut reps := #[(winningMask, size)]
  for i in [0:maskCount] do
    if seen[i]! == 0 then
      let m := i.toUInt32
      let (updated, size) := markOrbit tables seen m 0
      seen := updated
      reps := reps.push (m, size)
  return reps

structure Cyclotomic where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
  c4 : Int
  deriving DecidableEq, Repr, Inhabited

namespace Cyclotomic

def scalar (x : Int) : Cyclotomic := ⟨x, 0, 0, 0, 0⟩
def rootPower (i : Nat) : Cyclotomic :=
  match i % 5 with
  | 0 => ⟨1, 0, 0, 0, 0⟩
  | 1 => ⟨0, 1, 0, 0, 0⟩
  | 2 => ⟨0, 0, 1, 0, 0⟩
  | 3 => ⟨0, 0, 0, 1, 0⟩
  | _ => ⟨0, 0, 0, 0, 1⟩

instance : Add Cyclotomic where
  add a b := ⟨a.c0 + b.c0, a.c1 + b.c1, a.c2 + b.c2, a.c3 + b.c3, a.c4 + b.c4⟩

instance : Sub Cyclotomic where
  sub a b := ⟨a.c0 - b.c0, a.c1 - b.c1, a.c2 - b.c2, a.c3 - b.c3, a.c4 - b.c4⟩

instance : Mul Cyclotomic where
  mul a b :=
    ⟨a.c0*b.c0 + a.c1*b.c4 + a.c2*b.c3 + a.c3*b.c2 + a.c4*b.c1,
      a.c0*b.c1 + a.c1*b.c0 + a.c2*b.c4 + a.c3*b.c3 + a.c4*b.c2,
      a.c0*b.c2 + a.c1*b.c1 + a.c2*b.c0 + a.c3*b.c4 + a.c4*b.c3,
      a.c0*b.c3 + a.c1*b.c2 + a.c2*b.c1 + a.c3*b.c0 + a.c4*b.c4,
      a.c0*b.c4 + a.c1*b.c3 + a.c2*b.c2 + a.c3*b.c1 + a.c4*b.c0⟩

/-- For a real element, test the sign of `(2a-b) + b*sqrt(5)`. -/
def positive (x : Cyclotomic) : Bool :=
  let a := x.c0 - x.c2
  let b := x.c1 - x.c2
  let u := 2*a - b
  x.c1 == x.c4 && x.c2 == x.c3 &&
    (if 0 ≤ b then
      if 0 ≤ u then 0 < u || 0 < b else u*u < 5*b*b
     else 0 < u && 5*b*b < u*u)

end Cyclotomic

def phaseEntry (i x y : Nat) : Cyclotomic :=
  if (x+y) % 5 == (2*(i/5)) % 5 then
    Cyclotomic.rootPower ((i%5) * (x+5-y))
  else Cyclotomic.scalar 0

def sumEntry (m : Mask) (x y : Nat) : Cyclotomic :=
  (List.range phaseSpaceSize).foldl (fun value i =>
    if hasPoint m i then value + phaseEntry i x y else value) (Cyclotomic.scalar 0)

/-- `139 I + 50 A_S` in exact cyclotomic coefficients. -/
def shiftedEntry (m : Mask) (x y : Nat) : Cyclotomic :=
  Cyclotomic.scalar 50 * sumEntry m x y +
    Cyclotomic.scalar (if x = y then 139 else 0)

/-- An unscaled Schur complement step, so that no division is needed. -/
def schurStep (entry : Nat → Nat → Cyclotomic) (i j : Nat) : Cyclotomic :=
  entry 0 0 * entry (i+1) (j+1) - entry (i+1) 0 * entry 0 (j+1)

def positivePivots : Nat → (Nat → Nat → Cyclotomic) → Bool
  | 0, _ => true
  | n+1, entry => (entry 0 0).positive && positivePivots n (schurStep entry)

-- Cache each trailing matrix before the next Schur step.
private def shiftedMatrix (m : Mask) : Array (Array Cyclotomic) :=
  (List.range 5).toArray.map fun i => (List.range 5).toArray.map fun j => shiftedEntry m i j

private theorem rangeMatrix_get {n : Nat} (entry : Nat → Nat → Cyclotomic)
    {i j : Nat} (hi : i < n) (hj : j < n) :
    ((List.range n).toArray.map fun i => (List.range n).toArray.map (entry i))[i]![j]! =
      entry i j := by
  have hn : ((List.range n).toArray.map
      fun i => (List.range n).toArray.map (entry i)).size = n := by simp
  have hrow : ((List.range n).toArray.map
      fun i => (List.range n).toArray.map (entry i))[i]! =
      (List.range n).toArray.map (entry i) := by
    rw [getElem!_pos _ _ (by simpa only [hn] using hi), Array.getElem_map]
    simp
  rw [hrow]
  rw [getElem!_pos _ _ (by simpa using hj), Array.getElem_map]
  simp

private def positiveArrayPivots : Nat → Array (Array Cyclotomic) → Bool
  | 0, _ => true
  | n+1, matrix =>
    matrix[0]![0]!.positive &&
      positiveArrayPivots n ((List.range n).toArray.map fun i =>
        (List.range n).toArray.map fun j => schurStep (fun x y => matrix[x]![y]!) i j)

private theorem pivots_eq (n : Nat) (matrix : Array (Array Cyclotomic))
    (entry : Nat → Nat → Cyclotomic)
    (h : ∀ i < n, ∀ j < n, matrix[i]![j]! = entry i j) :
    positiveArrayPivots n matrix = positivePivots n entry := by
  induction n generalizing matrix entry with
  | zero => rfl
  | succ n ih =>
    rw [positiveArrayPivots, positivePivots, h 0 (Nat.zero_lt_succ _) 0 (Nat.zero_lt_succ _)]
    congr 1
    apply ih
    intro i hi j hj
    rw [rangeMatrix_get _ hi hj]
    simp only [schurStep]
    rw [h 0 (Nat.zero_lt_succ _) 0 (Nat.zero_lt_succ _),
      h (i+1) (Nat.succ_lt_succ hi) (j+1) (Nat.succ_lt_succ hj),
      h (i+1) (Nat.succ_lt_succ hi) 0 (Nat.zero_lt_succ _),
      h 0 (Nat.zero_lt_succ _) (j+1) (Nat.succ_lt_succ hj)]

/-- A rational separation test for every orbit. The winning orbit only
needs a positive four-dimensional compression. -/
def allOrbitPivots (reps : Array (Mask × Nat)) : Bool :=
  reps.all fun (m, _) => positiveArrayPivots (if m == winningMask then 4 else 5) (shiftedMatrix m)

/- Arithmetic and orbit traversal use bounded matrix arrays and
unbounded signed coefficients. -/
def checkCertificate : Bool := Id.run do
  let reps := orbitRepresentatives
  return affineMaps.size == 3000 && reps.size == 11408 &&
    reps[0]! == (winningMask, 500) &&
    reps.foldl (fun n p => n+p.2) 0 == maskCount &&
    allOrbitPivots reps

theorem pivots_of_certificate (hc : checkCertificate = true) {m : Mask} {size : Nat} (hm : (m, size) ∈ orbitRepresentatives) :
    positivePivots (if m == winningMask then 4 else 5) (shiftedEntry m) = true := by
  simp only [checkCertificate, Id.run_pure, Bool.and_eq_true] at hc
  have ha := Array.all_eq_true_iff_forall_mem.mp hc.2 (m, size) hm
  change positiveArrayPivots (if m == winningMask then 4 else 5) (shiftedMatrix m) = true at ha
  rw [pivots_eq _ _ (shiftedEntry m)] at ha
  · exact ha
  · intro i hi j hj
    change (((List.range 5).toArray.map
      fun i => (List.range 5).toArray.map (shiftedEntry m i))[i]![j]!) = shiftedEntry m i j
    have h : (if m == winningMask then 4 else 5) ≤ 5 := by split <;> decide
    exact rangeMatrix_get _ (Nat.lt_of_lt_of_le hi h) (Nat.lt_of_lt_of_le hj h)

end WignerFive
