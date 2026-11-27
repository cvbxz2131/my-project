import Std

/-!
Exact normal-play outcomes for the two symmetric additive games in Figure 16
of Larsson, Saha and Yokoo, Subtraction games in more than one dimension.
-/

namespace PlanarSubtraction

inductive Example where
  | first   -- {(1,5), (5,1), (6,6)}
  | second  -- {(2,5), (5,2), (7,7)}

def a : Example → Int | .first => 1 | .second => 2
def u : Example → Int | .first => 31 | .second => 34
def v : Example → Int | .first => 11 | .second => 22
def cutoff : Example → Int | .first => 85 | .second => 154
def guardWidth : Example → Int | .first => 24 | .second => 42
def limit : Example → Int | .first => 1824 | .second => 1470
def radius : Example → Nat | .first => 91 | .second => 122
def det (g : Example) : Int := u g * u g - v g * v g
def alpha (g : Example) (x y : Int) : Int := u g * x - v g * y
def beta (g : Example) (x y : Int) : Int := alpha g y x

private def tileWidth : Example → Nat | .first => 84 | .second => 112

-- In the finite table, bit (i * tileWidth + j) represents a loss at (i,j).
-- Its entries are checked through the recurrence on the base square.
private def table : Example → Nat
  | .first => 0x7c1f03e0f83f0540a815000000000e0380540a81500000000000000140a81500000000000000140a81500000000000000140a81580000000000000140a81583e0f83f00c030140a81583e0f83e07c1f0740a81583e0f83e0fc1f0740a81583e0f83e0f81f0740a81503e0f83e0f83f0740a815000080200f83e0740a81500000000000000040a81500000000000000040a81500000000000000040a81580000000000000040a81583f03c0f000000040a81583e07c1f07c1f07c0a81583e0fc1f07c1f07c0a81583e0f81f07c1f07c0a81503e0f83f07c1f07c0a8150000e03807c1f07c0a81500000000000100400a81500000000000000000a81500000000000000000a81500000000000000000a81583f00c03000000000a81583e07c1f07e0781e0a81583e0fc1f07c0f83e0a81583e0f81f07c1f83e0a81583e0f83f07c1f03e0a8150200f83e07c1f07e0a815000000000001c0700a815000000000000000002815000000000000000002815000000000000000002815c0f000000000000002815c1f07c1f07e0180602815c1f07c1f07c0f83e0e81581f07c1f07c1f83e0e81583f07c1f07c1f03e0e81503807c1f07c1f07e0e815000000100401f07c0e815000000000000000000815000000000000000000815000000000000000000815c03000000000000000815c1f07e0781e0000000815c1f07c0f83e0f83e0f81581f07c1f83e0f83e0f81583f07c1f03e0f83e0f81583e07c1f07e0f83e0f8150000001c0700f83e0f815000000000000002008015000000000000000000015000000000000000000015000000000000000000015c1f07e01806000000001501f07c0f83e0fc0f03c15fff07c1f83e0f81f07c1500007c1f03e0f83f07c15fffffc1f07e0f83e07c150000001f07c0f83e0fc1500000000000000380e015000000000000000000005000000000000000000005000000000000000000005000000000000000000005ffffffff83e0fc0300c050000000003e0f81f07c1dffffffffffe0f83f07c1d000000000000f83e07c1dfffffffffffff83e0fc1d000000000000003e0f81d000000000000000000001000000000000000000001000000000000000000001000000000000000000001000000000000000000001ffffffffffffffff07c1f000000000000000007c1fffffffffffffffffffc1f00000000000000000001ffffffffffffffffffffff
  | .second => 0x4000000c0641301904c0641307c04016000c0641301904c0641300000000000c0641301904c0641300000140000c0641301904c0641300000000000c0641301904c0641341fc0f45f07c0641301904c0641340000f40507c0641301904c0641345f01f05d07c0641301904c0641345f07f05d17c0641301904c0641345d07f07d17c0641301904c0641305807c0401600641301904c0641305d17c07c1600641301904c064130400000000000641301904c064130401600001000641301904c064130000000000000641301904c0641300140000f4050641301904c064130000000000050641301904c06413c0f45f07f05d1641301904c0641300f40507f03d1641301904c0641301f05d07c07d1641301904c0641307f05d17c07c1641301904c0641307f07d17c1fc1641301904c0641307c0401600001041301904c0641317c07c1601f01041301904c064130000000000000041301904c064131600001000000041301904c064130000000000000041301904c0641340000f40507f03c1301904c0641300000000500003c1301904c0641345f07f05d17c07c1301904c0641340507f03d17c1fc1301904c0641305d07c07d1741fc1301904c0641305d17c07c1601f01301904c0641307d17c1fc1745f01301904c064130401600001000000301904c0641307c1601f01005800301904c064130000000000000000301904c064130001000000050000301904c064130000000000000000301904c0641300f40507f03d17c1f01904c0641300000500003d0141f01904c0641307f05d17c07c1741f01904c0641307f03d17c1fc1745f01904c0641307c07d1741fc1f45f01904c06413ffc07c1601f01005801904c06413ffc1fc1745f01f05801904c064130000001000000000001904c064130001f01005800004001904c064130000000000000000001904c0641300000000500003d0141904c064130000000000000000141904c0641300007f03d17c1fc1745904c0641300000003d0141fc0f45904c06413fffffc07c1741f01f45904c06413fffffc1fc1745f01f05904c064130000001fc1f45f07f05904c064130000001f01005800004104c06413ffffffff01f05807c04104c064130000000000000000000104c064130000000000004000000104c064130000000000000000000104c0641300000000003d0141fc0f04c064130000000000000140000f04c06413ffffffffc1fc1745f01f04c064130000000001fc0f45f07f04c064130000000001f01f45d07f04c06413fffffffffff01f05807c04c06413fffffffffff07f05d17c04c064130000000000000004000000c064130000000000007c04016000c064130000000000000000000000c064130000000000000000140000c064130000000000000000000000c064130000000000001fc0f45f07c064130000000000000000f40507c06413ffffffffffffff01f05d07c06413ffffffffffffff07f05d17c064130000000000000007f07d17c064130000000000000007c04016006413ffffffffffffffffc07c160064130000000000000000000000006413000000000000000000001000641300000000000000000000000064130000000000000000000f405064130000000000000000000000506413fffffffffffffffff07f05d164130000000000000000007f03d164130000000000000000007c07d16413fffffffffffffffffffc07c16413fffffffffffffffffffc1fc164130000000000000000000000010413000000000000000000001f0104130000000000000000000000000413000000000000000000000000041300000000000000000000000004130000000000000000000007f03c130000000000000000000000003c13ffffffffffffffffffffffc07c13ffffffffffffffffffffffc1fc13000000000000000000000001fc13000000000000000000000001f013fffffffffffffffffffffffff01300000000000000000000000000030000000000000000000000000003000000000000000000000000000300000000000000000000000000030000000000000000000000000003fffffffffffffffffffffffffc1f000000000000000000000000001f000000000000000000000000001fffffffffffffffffffffffffffffffffffffffffffffffffffffffff

private def mask : Example → Nat | .first => 0x15 | .second => 0x6413

def edge (g : Example) (y : Int) : Bool :=
  (mask g).testBit (y % v g).toNat

def reduce (d t : Int) : Int :=
  if t < 2 * d then t else d + t % d

def center (g : Example) (s t : Int) : Bool :=
  let p := reduce (det g) s
  let q := reduce (det g) t
  let i := ((u g * p + v g * q) / det g).toNat
  let j := ((u g * q + v g * p) / det g).toNat
  (table g).testBit (min i j * tileWidth g + max i j)

def outcome (g : Example) (x y : Int) : Bool :=
  if x < 0 ∨ y < 0 then false
  else if beta g x y < -cutoff g then edge g y
  else if alpha g x y < -cutoff g then edge g x
  else center g (alpha g x y) (beta g x y)

def next (g : Example) (f : Int → Int → Bool) (x y : Int) : Bool :=
  !(f (x - a g) (y - 5) || f (x - 5) (y - a g) ||
    f (x - (a g + 5)) (y - (a g + 5)))


private def rowsCheck (g : Example) (start count : Nat) : Bool :=
  (List.range' start count).all fun x =>
    (List.range (radius g + 1)).all fun y =>
      outcome g x y == next g (outcome g) x y

private theorem rows_append (g : Example) (s m n : Nat)
    (hm : rowsCheck g s m = true) (hn : rowsCheck g (s+m) n = true) :
    rowsCheck g s (m+n) = true := by
  unfold rowsCheck at *
  have h := List.range'_append (s := s) (m := m) (n := n) (step := 1)
  rw [Nat.one_mul] at h
  rw [← h, List.all_append, hm, hn]
  rfl

-- Check fixed-size batches so kernel evaluation uses bounded memory.
section FiniteCheck

set_option maxRecDepth 40000
set_option maxHeartbeats 0

private theorem firstRows0 : rowsCheck .first 0 8 = true := by decide +kernel
private theorem firstRows8 : rowsCheck .first 8 8 = true := by decide +kernel
private theorem firstRows16 : rowsCheck .first 16 8 = true := by decide +kernel
private theorem firstRows24 : rowsCheck .first 24 8 = true := by decide +kernel
private theorem firstRows32 : rowsCheck .first 32 8 = true := by decide +kernel
private theorem firstRows40 : rowsCheck .first 40 8 = true := by decide +kernel
private theorem firstRows48 : rowsCheck .first 48 8 = true := by decide +kernel
private theorem firstRows56 : rowsCheck .first 56 8 = true := by decide +kernel
private theorem firstRows64 : rowsCheck .first 64 8 = true := by decide +kernel
private theorem firstRows72 : rowsCheck .first 72 8 = true := by decide +kernel
private theorem firstRows80 : rowsCheck .first 80 8 = true := by decide +kernel
private theorem firstRows88 : rowsCheck .first 88 4 = true := by decide +kernel
private theorem secondRows0 : rowsCheck .second 0 8 = true := by decide +kernel
private theorem secondRows8 : rowsCheck .second 8 8 = true := by decide +kernel
private theorem secondRows16 : rowsCheck .second 16 8 = true := by decide +kernel
private theorem secondRows24 : rowsCheck .second 24 8 = true := by decide +kernel
private theorem secondRows32 : rowsCheck .second 32 8 = true := by decide +kernel
private theorem secondRows40 : rowsCheck .second 40 8 = true := by decide +kernel
private theorem secondRows48 : rowsCheck .second 48 8 = true := by decide +kernel
private theorem secondRows56 : rowsCheck .second 56 8 = true := by decide +kernel
private theorem secondRows64 : rowsCheck .second 64 8 = true := by decide +kernel
private theorem secondRows72 : rowsCheck .second 72 8 = true := by decide +kernel
private theorem secondRows80 : rowsCheck .second 80 8 = true := by decide +kernel
private theorem secondRows88 : rowsCheck .second 88 8 = true := by decide +kernel
private theorem secondRows96 : rowsCheck .second 96 8 = true := by decide +kernel
private theorem secondRows104 : rowsCheck .second 104 8 = true := by decide +kernel
private theorem secondRows112 : rowsCheck .second 112 8 = true := by decide +kernel
private theorem secondRows120 : rowsCheck .second 120 3 = true := by decide +kernel

private theorem firstRows : rowsCheck .first 0 92 = true := by
  have tail80 := rows_append .first 80 8 4 firstRows80 firstRows88
  have tail72 := rows_append .first 72 8 12 firstRows72 tail80
  have tail64 := rows_append .first 64 8 20 firstRows64 tail72
  have tail56 := rows_append .first 56 8 28 firstRows56 tail64
  have tail48 := rows_append .first 48 8 36 firstRows48 tail56
  have tail40 := rows_append .first 40 8 44 firstRows40 tail48
  have tail32 := rows_append .first 32 8 52 firstRows32 tail40
  have tail24 := rows_append .first 24 8 60 firstRows24 tail32
  have tail16 := rows_append .first 16 8 68 firstRows16 tail24
  have tail8 := rows_append .first 8 8 76 firstRows8 tail16
  have tail0 := rows_append .first 0 8 84 firstRows0 tail8
  exact tail0

private theorem secondRows : rowsCheck .second 0 123 = true := by
  have tail112 := rows_append .second 112 8 3 secondRows112 secondRows120
  have tail104 := rows_append .second 104 8 11 secondRows104 tail112
  have tail96 := rows_append .second 96 8 19 secondRows96 tail104
  have tail88 := rows_append .second 88 8 27 secondRows88 tail96
  have tail80 := rows_append .second 80 8 35 secondRows80 tail88
  have tail72 := rows_append .second 72 8 43 secondRows72 tail80
  have tail64 := rows_append .second 64 8 51 secondRows64 tail72
  have tail56 := rows_append .second 56 8 59 secondRows56 tail64
  have tail48 := rows_append .second 48 8 67 secondRows48 tail56
  have tail40 := rows_append .second 40 8 75 secondRows40 tail48
  have tail32 := rows_append .second 32 8 83 secondRows32 tail40
  have tail24 := rows_append .second 24 8 91 secondRows24 tail32
  have tail16 := rows_append .second 16 8 99 secondRows16 tail24
  have tail8 := rows_append .second 8 8 107 secondRows8 tail16
  have tail0 := rows_append .second 0 8 115 secondRows0 tail8
  exact tail0

end FiniteCheck

private theorem boundedCheck_correct (g : Example) :
    rowsCheck g 0 (radius g + 1) = true := by
  cases g
  · exact firstRows
  · exact secondRows

private theorem local_bounded (g : Example) (x y : Int) (hx : 0 ≤ x)
    (hy : 0 ≤ y) (hx' : x ≤ radius g) (hy' : y ≤ radius g) :
    outcome g x y = next g (outcome g) x y := by
  have h  := List.all_eq_true.mp (boundedCheck_correct g) x.toNat
    (List.mem_range'.mpr ⟨x.toNat, by omega, by simp⟩)
  have hh := List.all_eq_true.mp h y.toNat (List.mem_range.mpr (by omega))
  simpa [Int.toNat_of_nonneg hx, Int.toNat_of_nonneg hy] using hh

private theorem center_swap (g : Example) (s t : Int) :
    center g s t = center g t s := by
  simp [center, Nat.min_comm, Nat.max_comm]

theorem outcome_swap (g : Example) (x y : Int) : outcome g x y = outcome g y x := by
  by_cases hx : x < 0
  · simp [outcome, hx]
  by_cases hy : y < 0
  · simp [outcome, hy]
  have hn : ¬ (beta g x y < -cutoff g ∧ alpha g x y < -cutoff g) := by
    cases g <;> simp [alpha, beta, cutoff, u, v] at * <;> omega
  simp only [outcome, if_neg (show ¬ (x < 0 ∨ y < 0) by omega),
    if_neg (show ¬ (y < 0 ∨ x < 0) by omega)]
  change (if beta g x y < -cutoff g then edge g y
    else if alpha g x y < -cutoff g then edge g x
    else center g (alpha g x y) (beta g x y)) =
    (if alpha g x y < -cutoff g then edge g x
    else if beta g x y < -cutoff g then edge g y
    else center g (beta g x y) (alpha g x y))
  by_cases hB : beta g x y < -cutoff g
  · have hA : ¬ alpha g x y < -cutoff g := fun ha => hn ⟨hB, ha⟩
    simp only [hA, hB, if_false, if_true]
  · by_cases hA : alpha g x y < -cutoff g
    · simp only [hB, hA, if_false, if_true]
    · simp only [hB, hA, if_false, center_swap]

private theorem reduce_sub (d t : Int) (ht : 2 * d ≤ t) :
    reduce d (t - d) = reduce d t := by
  unfold reduce
  rw [if_neg (show ¬ t < 2 * d by omega)]
  split
  · rename_i h
    have hem : t % d = t - d - d := calc
      t % d = (t - d) % d := (Int.sub_emod_right t d).symm
      _ = (t - d - d) % d := (Int.sub_emod_right (t - d) d).symm
      _ = t - d - d := Int.emod_eq_of_lt (by omega) (by omega)
    omega
  · rw [Int.sub_emod_right]

private theorem outcome_shift (g : Example) (x y : Int)
    (hx : u g ≤ x) (hy : v g ≤ y) (h : 2 * det g ≤ alpha g x y) :
    outcome g (x - u g) (y - v g) = outcome g x y := by
  have hα : alpha g (x - u g) (y - v g) = alpha g x y - det g := by
    cases g <;> simp [alpha, u, v, det] <;> omega
  have hβ : beta g (x - u g) (y - v g) = beta g x y := by
    cases g <;> simp [beta, alpha, u, v] <;> omega
  have hd : 0 < det g := by cases g <;> decide
  have hcut : 0 ≤ cutoff g := by cases g <;> decide
  have hpos : 0 < u g ∧ 0 < v g := by cases g <;> decide
  simp only [outcome, if_neg (show ¬ (x - u g < 0 ∨ y - v g < 0) by omega),
    if_neg (show ¬ (x < 0 ∨ y < 0) by omega), hβ, hα]
  by_cases hb : beta g x y < -cutoff g
  · simp only [hb, if_true, edge, Int.sub_emod_right]
  · have h₁ : ¬ alpha g x y - det g < -cutoff g := by omega
    have h₂ : ¬ alpha g x y < -cutoff g := by omega
    simp only [hb, h₁, h₂, if_false, center, reduce_sub (det g) (alpha g x y) h]

/-- Translation towards the lower part of the board preserves the outcome
    once the first oblique coordinate reaches one period. -/
theorem lower_period (g : Example) (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : det g ≤ alpha g x y) :
    outcome g (x + u g) (y + v g) = outcome g x y := by
  have hα : alpha g (x + u g) (y + v g) = alpha g x y + det g := by
    cases g <;> simp [alpha, u, v, det] <;> omega
  have h' := outcome_shift g (x + u g) (y + v g) (by omega) (by omega) (by omega)
  simpa using h'.symm

theorem upper_period (g : Example) (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : det g ≤ beta g x y) :
    outcome g (x + v g) (y + u g) = outcome g x y := by
  rw [outcome_swap g (x + v g) (y + u g), lower_period g y x hy hx h, outcome_swap g y x]

private def Offset (g : Example) (i j : Int) : Prop :=
  i = 0 ∧ j = 0 ∨ i = a g ∧ j = 5 ∨ i = 5 ∧ j = a g ∨
    i = a g + 5 ∧ j = a g + 5

private theorem offset_bounds (g : Example) (i j : Int) (h : Offset g i j) :
    0 ≤ i ∧ i ≤ a g + 5 ∧ 0 ≤ j ∧ j ≤ a g + 5 ∧
      alpha g i j ≤ limit g - 2 * det g ∧ -guardWidth g ≤ beta g i j := by
  cases g <;> simp [Offset, a, u, v, alpha, beta, limit, det, guardWidth] at * <;> omega

private theorem beta_sub (g : Example) (x y i j : Int) :
    beta g (x-i) (y-j) = beta g x y - beta g i j := by
  cases g <;> simp [beta, alpha, u, v] <;> omega

private theorem alpha_sub (g : Example) (x y i j : Int) :
    alpha g (x-i) (y-j) = alpha g x y - alpha g i j := by
  exact beta_sub g y x j i

private theorem beta_shift (g : Example) :
    beta g (u g) (v g) = 0 := by
  cases g <;> decide

private theorem local_transfer (g : Example) (x y p q : Int)
    (h : ∀ i j, Offset g i j → outcome g (x-i) (y-j) = outcome g (p-i) (q-j))
    (hlocal : outcome g p q = next g (outcome g) p q) :
    outcome g x y = next g (outcome g) x y := by
  have origin := h 0 0 (Or.inl ⟨rfl, rfl⟩)
  rw [Int.sub_zero, Int.sub_zero, Int.sub_zero, Int.sub_zero] at origin
  unfold next at *
  rw [origin, h (a g) 5 (Or.inr (Or.inl ⟨rfl, rfl⟩)),
    h 5 (a g) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))),
    h (a g + 5) (a g + 5) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))]
  exact hlocal

private theorem local_swap (g : Example) (x y : Int)
    (h : outcome g y x = next g (outcome g) y x) :
    outcome g x y = next g (outcome g) x y := by
  rw [outcome_swap g x y, h]
  unfold next
  congr 1
  rw [outcome_swap g (y - a g) (x - 5),
    outcome_swap g (y - 5) (x - a g), outcome_swap g (y - (a g + 5)) (x - (a g + 5)),
    Bool.or_comm (outcome g (x - 5) (y - a g)) (outcome g (x - a g) (y - 5))]

private theorem far_right (g : Example) (x y : Int)
    (hA : limit g ≤ alpha g x y) (hB : -cutoff g - guardWidth g ≤ beta g x y)
    (ih : ∀ p q : Int, 0 ≤ p → 0 ≤ q → p + q < x + y →
      outcome g p q = next g (outcome g) p q) :
    outcome g x y = next g (outcome g) x y := by
  have hxy : a g + 5 ≤ x - u g ∧ a g + 5 ≤ y - v g := by
    cases g <;> simp [a, u, v, alpha, beta, cutoff, guardWidth, limit] at * <;> omega
  refine local_transfer g x y (x - u g) (y - v g) ?_ (ih _ _ (by cases g <;> simp [a] at * <;> omega)
    (by cases g <;> simp [a] at * <;> omega) (by cases g <;> simp [u, v] <;> omega))
  intro i j hij
  obtain ⟨_, hi, _, hj, hα, _⟩ := offset_bounds g i j hij
  rw [show x - u g - i = x - i - u g by omega, show y - v g - j = y - j - v g by omega]
  symm
  apply outcome_shift
  · omega
  · omega
  · rw [alpha_sub]
    omega

private theorem bottom_formula (g : Example) (x y : Int) (hx : 0 ≤ x)
    (h : beta g x y < -cutoff g) :
    outcome g x y = if y < 0 then false else edge g y := by
  by_cases hy : y < 0
  · simp [outcome, hy]
  · simp [outcome, hy, h, show ¬ x < 0 by omega]

private theorem deep_right (g : Example) (x y : Int) (hy : 0 ≤ y)
    (hB : beta g x y < -cutoff g - guardWidth g)
    (ih : ∀ p q : Int, 0 ≤ p → 0 ≤ q → p + q < x + y →
      outcome g p q = next g (outcome g) p q) :
    outcome g x y = next g (outcome g) x y := by
  by_cases tall : v g + (a g + 5) ≤ y
  · have hx : a g + 5 ≤ x - u g := by
      cases g <;> simp [a, u, v, alpha, beta, cutoff, guardWidth] at * <;> omega
    have hy' : a g + 5 ≤ y - v g := by omega
    refine local_transfer g x y (x-u g) (y-v g) ?_ (ih _ _
      (by cases g <;> simp [a] at * <;> omega)
      (by cases g <;> simp [a] at * <;> omega) (by cases g <;> simp [u, v] <;> omega))
    intro i j hij
    obtain ⟨_, hi, _, hj, _, hβ⟩ := offset_bounds g i j hij
    have original : beta g (x-i) (y-j) < -cutoff g := by rw [beta_sub]; omega
    have translated : beta g (x-u g-i) (y-v g-j) < -cutoff g := by
      rw [beta_sub, beta_sub, beta_shift]
      omega
    have hu : 0 ≤ u g := by cases g <;> decide
    rw [bottom_formula g _ _ (by omega) original, bottom_formula g _ _ (by omega) translated,
      if_neg (show ¬ y-j < 0 by cases g <;> simp [a, v] at * <;> omega),
      if_neg (show ¬ y-v g-j < 0 by cases g <;> simp [a] at * <;> omega)]
    rw [show y-v g-j = y-j-v g by omega]
    simp [edge, Int.sub_emod_right]
  · have hyBox : y ≤ radius g := by cases g <;> simp [a, v, radius] at * <;> omega
    have newB : beta g (radius g) y < -cutoff g - guardWidth g := by
      cases g <;> simp [a, v, u, beta, alpha, cutoff, guardWidth, radius] at * <;> omega
    refine local_transfer g x y (radius g) y ?_ (local_bounded g _ _ (by omega) hy (by omega) hyBox)
    intro i j hij
    obtain ⟨_, hi, _, _, _, hβ⟩ := offset_bounds g i j hij
    have hx : 0 ≤ x - i := by
      cases g <;> simp [a, u, v, alpha, beta, cutoff, guardWidth] at * <;> omega
    have hx' : 0 ≤ (radius g : Int) - i := by
      cases g <;> simp [radius, a] at * <;> omega
    rw [bottom_formula g _ _ hx (by rw [beta_sub]; omega),
      bottom_formula g _ _ hx' (by rw [beta_sub]; omega)]

theorem outcome_recurrence (g : Example) (x y : Int) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    outcome g x y = next g (outcome g) x y := by
  induction h : (x + y).toNat using Nat.strongRecOn generalizing x y with
  | ind n smaller =>
    have ih : ∀ p q : Int, 0 ≤ p → 0 ≤ q → p + q < x + y →
        outcome g p q = next g (outcome g) p q := by
      intro p q hp hq hsum
      exact smaller (p + q).toNat (by omega) p q hp hq rfl
    have swapped : ∀ p q : Int, 0 ≤ p → 0 ≤ q → p + q < y + x →
        outcome g p q = next g (outcome g) p q :=
      fun p q hp hq hsum => ih p q hp hq (by omega)
    by_cases hB : beta g x y < -cutoff g - guardWidth g
    · exact deep_right g x y hy hB ih
    by_cases hA : alpha g x y < -cutoff g - guardWidth g
    · exact local_swap g x y (deep_right g y x hx hA swapped)
    by_cases highA : limit g ≤ alpha g x y
    · exact far_right g x y highA (by omega) ih
    by_cases highB : limit g ≤ beta g x y
    · exact local_swap g x y (far_right g y x highB (by change -cutoff g - guardWidth g ≤ alpha g x y; omega) swapped)
    have hbox : x ≤ radius g ∧ y ≤ radius g := by
      cases g <;> simp [radius, limit, alpha, beta, u, v] at * <;> omega
    exact local_bounded g x y hx hy hbox.1 hbox.2

/-- Negative coordinates denote unavailable moves. On the board,
    a position is losing exactly when all legal options are winning. -/
def IsOutcome (g : Example) (f : Int → Int → Bool) : Prop :=
  (∀ x y, x < 0 ∨ y < 0 → f x y = false) ∧
    (∀ x y, 0 ≤ x → 0 ≤ y → f x y = next g f x y)

theorem outcome_isOutcome (g : Example) : IsOutcome g (outcome g) :=
  ⟨fun x y h => by simp [outcome, h], outcome_recurrence g⟩

theorem exact_outcome (g : Example) (f : Int → Int → Bool) (hf : IsOutcome g f) :
    f = outcome g := by
  funext x y
  induction h : (x + y).toNat using Nat.strongRecOn generalizing x y with
  | ind n smaller =>
    by_cases unavailable : x < 0 ∨ y < 0
    · rw [hf.1 x y unavailable, (outcome_isOutcome g).1 x y unavailable]
    have follows : ∀ i j, Offset g i j → 0 < i + j →
        f (x-i) (y-j) = outcome g (x-i) (y-j) := by
      intro i j hij positive
      by_cases unavail : x-i < 0 ∨ y-j < 0
      · rw [hf.1 _ _ unavail, (outcome_isOutcome g).1 _ _ unavail]
      exact smaller (x-i+(y-j)).toNat (by omega) (x-i) (y-j) rfl
    have ha : 0 < a g + 5 := by cases g <;> decide
    rw [hf.2 x y (by omega) (by omega), outcome_recurrence g x y (by omega) (by omega)]
    unfold next
    rw [follows (a g) 5 (Or.inr (Or.inl ⟨rfl, rfl⟩)) ha,
      follows 5 (a g) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) (by omega),
      follows (a g + 5) (a g + 5) (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) (by omega)]

theorem exists_unique_outcome (g : Example) : ∃ f, IsOutcome g f ∧ ∀ f', IsOutcome g f' → f' = f :=
  ⟨outcome g, outcome_isOutcome g, fun f hf => exact_outcome g f hf⟩

#print axioms outcome_recurrence
#print axioms exact_outcome

end PlanarSubtraction

