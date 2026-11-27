import WignerFiveCertificate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Interpreting the exact Wigner certificate

The cyclotomic arithmetic is evaluated in the complex numbers. An
unscaled Schur step gives the quadratic form on the remaining coordinates,
plus one square that is always nonnegative.
-/

open scoped BigOperators ComplexConjugate

namespace WignerFive

noncomputable section

def tau : ℝ := (Real.sqrt 5 - 1) / 2

def lowerEigenvalue : ℝ :=
  (2 - Real.sqrt 5 - Real.sqrt (15 + 6 * Real.sqrt 5)) / 2

theorem tau_sq : tau^2 + tau = 1 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  unfold tau
  nlinarith

theorem tau_pos : 0 < tau := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  unfold tau
  nlinarith

theorem lowerEigenvalue_poly :
    lowerEigenvalue^2 - (1-2*tau)*lowerEigenvalue - (4+5*tau) = 0 := by
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 15+6*Real.sqrt 5 by positivity)
  unfold tau lowerEigenvalue
  nlinarith

theorem lowerEigenvalue_lt_cutoff : lowerEigenvalue < -(139/50) := by
  have h5 := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have h5p := Real.sqrt_nonneg (5 : ℝ)
  have h5l : (559/250 : ℝ) < Real.sqrt 5 := by nlinarith
  have hr := Real.sq_sqrt (show (0 : ℝ) ≤ 15+6*Real.sqrt 5 by positivity)
  have hrp := Real.sqrt_nonneg (15+6*Real.sqrt (5 : ℝ))
  have hrl : (533/100 : ℝ) < Real.sqrt (15+6*Real.sqrt 5) := by nlinarith
  unfold lowerEigenvalue
  linarith

/-- Evaluation of the integral group ring at the chosen root of unity. -/
def Cyclotomic.eval (ζ : ℂ) (a : Cyclotomic) : ℂ :=
  a.c0 + a.c1 * ζ + a.c2 * ζ^2 + a.c3 * ζ^3 + a.c4 * ζ^4

@[simp] theorem Cyclotomic.eval_scalar (ζ : ℂ) (a : ℤ) :
    (Cyclotomic.scalar a).eval ζ = a := by simp [Cyclotomic.eval, Cyclotomic.scalar]

@[simp] theorem Cyclotomic.eval_add (ζ : ℂ) (a b : Cyclotomic) :
    (a+b).eval ζ = a.eval ζ + b.eval ζ := by
  have hc : a+b = ⟨a.c0+b.c0, a.c1+b.c1, a.c2+b.c2, a.c3+b.c3, a.c4+b.c4⟩ := rfl
  simp only [hc, Cyclotomic.eval, Int.cast_add]
  ring

@[simp] theorem Cyclotomic.eval_sub (ζ : ℂ) (a b : Cyclotomic) :
    (a-b).eval ζ = a.eval ζ - b.eval ζ := by
  have hc : a-b = ⟨a.c0-b.c0, a.c1-b.c1, a.c2-b.c2, a.c3-b.c3, a.c4-b.c4⟩ := rfl
  simp only [hc, Cyclotomic.eval, Int.cast_sub]
  ring

theorem Cyclotomic.eval_mul {ζ : ℂ} (hζ : ζ^5 = 1) (a b : Cyclotomic) :
    (a*b).eval ζ = a.eval ζ * b.eval ζ := by
  have hz6 : ζ^6 = ζ := by linear_combination ζ * hζ
  have hz7 : ζ^7 = ζ^2 := by linear_combination ζ^2 * hζ
  have hz8 : ζ^8 = ζ^3 := by linear_combination ζ^3 * hζ
  have hc : a*b =
    ⟨a.c0*b.c0 + a.c1*b.c4 + a.c2*b.c3 + a.c3*b.c2 + a.c4*b.c1,
      a.c0*b.c1 + a.c1*b.c0 + a.c2*b.c4 + a.c3*b.c3 + a.c4*b.c2,
      a.c0*b.c2 + a.c1*b.c1 + a.c2*b.c0 + a.c3*b.c4 + a.c4*b.c3,
      a.c0*b.c3 + a.c1*b.c2 + a.c2*b.c1 + a.c3*b.c0 + a.c4*b.c4,
      a.c0*b.c4 + a.c1*b.c3 + a.c2*b.c2 + a.c3*b.c1 + a.c4*b.c0⟩ := rfl
  simp only [hc, Cyclotomic.eval, Int.cast_add, Int.cast_mul]
  ring_nf
  simp only [hζ, hz6, hz7, hz8, mul_one]

theorem Cyclotomic.eval_rootPower {ζ : ℂ} (hζ : ζ^5 = 1) (i : ℕ) :
    (Cyclotomic.rootPower i).eval ζ = ζ^i := by
  have he : ζ^i = ζ^(i%5) := by
    conv_lhs => rw [← Nat.mod_add_div i 5]
    simp [pow_add, pow_mul, hζ]
  rw [he]
  unfold Cyclotomic.rootPower
  have hi : i % 5 < 5 := Nat.mod_lt _ (by decide)
  interval_cases h : i % 5 <;> simp [Cyclotomic.eval]

private theorem integer_sign {u b : ℤ}
    (h : (if 0 ≤ b then
        if 0 ≤ u then (0 < u || 0 < b) else u*u < 5*b*b
      else 0 < u && 5*b*b < u*u) = true) :
    0 < (u : ℝ) + (b : ℝ) * Real.sqrt 5 := by
  have hr : (Real.sqrt (5 : ℝ))^2 = 5 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt (5 : ℝ) := by positivity
  by_cases hb : 0 ≤ b
  · by_cases hu : 0 ≤ u
    · simp [hb, hu] at h
      have hb' : 0 ≤ (b : ℝ) := by exact_mod_cast hb
      have hu' : 0 ≤ (u : ℝ) := by exact_mod_cast hu
      rcases h with h | h
      · exact add_pos_of_pos_of_nonneg (by exact_mod_cast h) (by positivity)
      · have : 0 < (b : ℝ) := by exact_mod_cast h
        positivity
    · simp [hb, hu] at h
      have hb' : 0 ≤ (b : ℝ) := by exact_mod_cast hb
      have hu' : 0 ≤ -(u : ℝ) := neg_nonneg.mpr (by exact_mod_cast (lt_of_not_ge hu).le)
      have hc : (u : ℝ) * u < 5 * (b : ℝ) * b := by exact_mod_cast h
      have hc' : (-(u : ℝ))^2 < ((b : ℝ) * Real.sqrt 5)^2 := by
        rw [mul_pow, hr]
        nlinarith only [hc]
      have := (sq_lt_sq₀ hu' (mul_nonneg hb' hp.le)).mp hc'
      linarith
  · simp [hb] at h
    have hu' : 0 < (u : ℝ) := by exact_mod_cast h.1
    have hb' : 0 ≤ -(b : ℝ) := neg_nonneg.mpr (by exact_mod_cast (lt_of_not_ge hb).le)
    have hc : 5 * (b : ℝ) * b < (u : ℝ) * u := by exact_mod_cast h.2
    have hc' : (-(b : ℝ) * Real.sqrt 5)^2 < (u : ℝ)^2 := by
      rw [mul_pow, hr]
      nlinarith only [hc]
    have := (sq_lt_sq₀ (mul_nonneg hb' hp.le) hu'.le).mp hc'
    linarith

theorem Cyclotomic.eval_positive {ζ : ℂ}
    (h₁ : ζ + ζ^4 = (tau : ℂ)) (h₂ : ζ^2 + ζ^3 = -1 - (tau : ℂ))
    {x : Cyclotomic} (hp : x.positive = true) :
    0 < (x.eval ζ).re := by
  unfold Cyclotomic.positive at hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  obtain ⟨⟨h₁', h₂'⟩, h⟩ := hp
  have hsign := integer_sign h
  have he : x.eval ζ =
      ((x.c0 - x.c2 : ℤ) : ℂ) + ((x.c1 - x.c2 : ℤ) : ℂ) * (tau : ℂ) := by
    unfold Cyclotomic.eval
    rw [← h₁', ← h₂']
    push_cast
    linear_combination (x.c1 : ℂ) * h₁ + (x.c2 : ℂ) * h₂
  rw [he]
  simp only [Complex.add_re, Complex.intCast_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  unfold tau
  push_cast at hsign ⊢
  linarith

def zeta : ℂ := Complex.exp (((2*Real.pi/5 : ℝ) : ℂ) * Complex.I)

theorem zeta_fifth : zeta^5 = 1 := by
  unfold zeta
  rw [← Complex.exp_nat_mul]
  convert Complex.exp_two_pi_mul_I using 2
  push_cast
  ring

theorem zeta_conj : conj zeta = zeta^4 := by
  have h : zeta * conj zeta = 1 := by
    unfold zeta
    rw [← Complex.exp_conj, ← Complex.exp_add]
    have hphase (x : ℝ) : (x : ℂ) * Complex.I + conj ((x : ℂ) * Complex.I) = 0 := by simp
    rw [hphase, Complex.exp_zero]
  have hz : zeta ≠ 0 := Complex.exp_ne_zero _
  apply mul_left_cancel₀ hz
  rw [h, ← pow_succ', zeta_fifth]

theorem zeta_pair : zeta + zeta^4 = (tau : ℂ) := by
  rw [← zeta_conj, Complex.add_conj]
  apply congrArg Complex.ofReal
  unfold zeta tau
  rw [Complex.exp_ofReal_mul_I_re]
  rw [show 2*Real.pi/5 = 2*(Real.pi/5) by ring, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]

theorem zeta_pair2 : zeta^2 + zeta^3 = -1-(tau : ℂ) := by
  have h8 : zeta^8 = zeta^3 := by linear_combination zeta^3 * zeta_fifth
  have ht : (tau : ℂ)^2 + (tau : ℂ) = 1 := by exact_mod_cast tau_sq
  have hsq : (zeta + zeta^4)^2 = (tau : ℂ)^2 :=
    congrArg (fun x : ℂ => x^2) zeta_pair
  linear_combination hsq - h8 - 2*zeta_fifth + ht

def Cyclotomic.reverse (a : Cyclotomic) : Cyclotomic :=
  ⟨a.c0, a.c4, a.c3, a.c2, a.c1⟩

theorem Cyclotomic.reverse_eval (a : Cyclotomic) :
    conj (a.eval zeta) = a.reverse.eval zeta := by
  have h8 : (zeta^4)^2 = zeta^3 := by linear_combination zeta^3*zeta_fifth
  have h12 : (zeta^4)^3 = zeta^2 := by
    rw [← pow_mul]
    norm_num
    rw [show (12 : ℕ) = 5*2+2 by decide, pow_add, pow_mul, zeta_fifth]
    simp
  have h16 : (zeta^4)^4 = zeta := by
    rw [← pow_mul]
    norm_num
    rw [show (16 : ℕ) = 5*3+1 by decide, pow_add, pow_mul, zeta_fifth]
    simp
  simp only [Cyclotomic.eval, Cyclotomic.reverse, map_add, map_mul, map_pow,
    map_intCast, zeta_conj, h8, h12, h16]
  ring

set_option maxRecDepth 4096 in
private theorem phaseEntry_reverse_fin :
    ∀ (i : Fin 25) (x y : Fin 5),
      (phaseEntry i x y).reverse = phaseEntry i y x := by decide

private theorem sumEntry_reverse (m : Mask) {x y : ℕ} (hx : x < 5) (hy : y < 5) :
    (sumEntry m x y).reverse = sumEntry m y x := by
  unfold sumEntry
  refine List.foldl_rel
    (f := fun value i => if hasPoint m i then value + phaseEntry i x y else value)
    (g := fun value i => if hasPoint m i then value + phaseEntry i y x else value)
    (r := fun (a b : Cyclotomic) => a.reverse = b) ?_ ?_
  · rfl
  · intro i hi a b hab
    by_cases hm : hasPoint m i
    · have hp := phaseEntry_reverse_fin ⟨i, List.mem_range.mp hi⟩ ⟨x, hx⟩ ⟨y, hy⟩
      change (phaseEntry i x y).reverse = phaseEntry i y x at hp
      simp only [if_pos hm]
      change a.reverse + (phaseEntry i x y).reverse = b + phaseEntry i y x
      rw [hab, hp]
    · simpa only [if_neg hm] using hab

def quadratic (n : ℕ) (A : ℕ → ℕ → ℂ) (v : ℕ → ℂ) : ℂ :=
  ∑ i ∈ Finset.range n, conj (v i) * ∑ j ∈ Finset.range n, A i j * v j

def trailing (A : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ :=
  fun i j => A 0 0 * A (i+1) (j+1) - A (i+1) 0 * A 0 (j+1)

def Hermitian (A : ℕ → ℕ → ℂ) (n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, conj (A i j) = A j i

def phaseSum (m : Mask) (x y : ℕ) : ℂ := (sumEntry m x y).eval zeta

theorem phaseSum_hermitian (m : Mask) {n : ℕ} (hn : n ≤ 5) : Hermitian (phaseSum m) n := by
  intro i hi j hj
  unfold phaseSum
  rw [Cyclotomic.reverse_eval, sumEntry_reverse m (hi.trans_le hn) (hj.trans_le hn)]

theorem shiftedEntry_eval (m : Mask) (i j : ℕ) :
    (shiftedEntry m i j).eval zeta = 50 * phaseSum m i j + if i = j then 139 else 0 := by
  unfold shiftedEntry phaseSum
  rw [Cyclotomic.eval_add, Cyclotomic.eval_mul zeta_fifth]
  split <;> simp

theorem shiftedEntry_hermitian (m : Mask) {n : ℕ} (hn : n ≤ 5) :
    Hermitian (fun i j => (shiftedEntry m i j).eval zeta) n := by
  intro i hi j hj
  change conj ((shiftedEntry m i j).eval zeta) = (shiftedEntry m j i).eval zeta
  rw [shiftedEntry_eval, shiftedEntry_eval, map_add, map_mul, map_ofNat,
    phaseSum_hermitian m hn i hi j hj]
  by_cases h : i = j <;> simp [h, eq_comm, map_ofNat]

theorem trailing_hermitian {A : ℕ → ℕ → ℂ} {n : ℕ} (hA : Hermitian A (n+1)) :
    Hermitian (trailing A) n := by
  intro i hi j hj
  unfold trailing
  rw [map_sub, map_mul, map_mul, hA 0 (by omega) 0 (by omega),
    hA (i+1) (by omega) (j+1) (by omega),
    hA (i+1) (by omega) 0 (by omega), hA 0 (by omega) (j+1) (by omega)]
  ring

theorem quadratic_schur {n : ℕ} {A : ℕ → ℕ → ℂ} (hA : Hermitian A (n+1))
    (v : ℕ → ℂ) :
    A 0 0 * quadratic (n+1) A v =
      (Complex.normSq (A 0 0 * v 0 +
        ∑ j ∈ Finset.range n, A 0 (j+1) * v (j+1)) : ℂ) +
      quadratic n (trailing A) (fun i => v (i+1)) := by
  let b := ∑ j ∈ Finset.range n, A 0 (j+1) * v (j+1)
  let d := ∑ i ∈ Finset.range n, conj (v (i+1)) * A (i+1) 0
  let e := ∑ i ∈ Finset.range n, conj (v (i+1)) *
    ∑ j ∈ Finset.range n, A (i+1) (j+1) * v (j+1)
  have hb : conj b = d := by
    unfold b d
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_mul, hA 0 (by omega) (i+1) (by simpa using Nat.succ_lt_succ (Finset.mem_range.mp hi))]
    ring
  have h00 := hA 0 (by omega) 0 (by omega)
  have hQ : quadratic (n+1) A v =
      conj (v 0) * (A 0 0 * v 0 + b) + d * v 0 + e := by
    unfold quadratic b d e
    simp only [Finset.sum_range_succ', mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    ring
  have hT : quadratic n (trailing A) (fun i => v (i+1)) =
      A 0 0 * e - d * b := by
    unfold quadratic trailing d e
    conv_rhs => rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    unfold b
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hQ, hT, Complex.normSq_eq_conj_mul_self, map_add, map_mul, h00, hb]
  ring

theorem nonneg_of_pivots {ζ : ℂ}
    (h₅ : ζ^5 = 1) (h₁ : ζ+ζ^4 = (tau : ℂ)) (h₂ : ζ^2+ζ^3 = -1-(tau : ℂ))
    {n : ℕ} {entry : ℕ → ℕ → Cyclotomic} (hp : positivePivots n entry = true)
    (he : Hermitian (fun i j => (entry i j).eval ζ) n) (v : ℕ → ℂ) :
    0 ≤ (quadratic n (fun i j => (entry i j).eval ζ) v).re := by
  induction n generalizing entry v with
  | zero => simp [quadratic]
  | succ n ih =>
    simp only [positivePivots, Bool.and_eq_true] at hp
    have hpos := Cyclotomic.eval_positive h₁ h₂ hp.1
    let A : ℕ → ℕ → ℂ := fun i j => (entry i j).eval ζ
    have hs : (fun i j => (schurStep entry i j).eval ζ) = trailing A := by
      funext i j
      simp [schurStep, trailing, A, Cyclotomic.eval_mul h₅]
    have htail : 0 ≤ (quadratic n (trailing A) (fun i => v (i+1))).re := by
      rw [← hs]
      apply ih hp.2
      rw [hs]
      exact trailing_hermitian he
    have hreal : (A 0 0).im = 0 := by
      have h := congrArg Complex.im (he 0 (by omega) 0 (by omega))
      simp only [Complex.conj_im] at h
      change -(A 0 0).im = (A 0 0).im at h
      linarith
    have h := congrArg Complex.re (quadratic_schur he v)
    change (A 0 0 * quadratic (n+1) A v).re = _ at h
    rw [Complex.mul_re, hreal, zero_mul, sub_zero, Complex.add_re, Complex.ofReal_re] at h
    exact nonneg_of_mul_nonneg_right (h.trans_ge (add_nonneg (Complex.normSq_nonneg _) htail)) hpos

theorem certified_compression {m : Mask} {size : ℕ} (hm : (m, size) ∈ orbitRepresentatives)
    (v : ℕ → ℂ) :
    0 ≤ (quadratic (if m == winningMask then 4 else 5)
      (fun i j => (shiftedEntry m i j).eval zeta) v).re := by
  apply nonneg_of_pivots zeta_fifth zeta_pair zeta_pair2 (certified_pivots hm)
  apply shiftedEntry_hermitian
  split <;> decide

def winnerU : ℝ := 2*(1+tau)*(2+tau-lowerEigenvalue)
def winnerV : ℝ := -tau*(2-lowerEigenvalue)
def winnerW : ℝ := (2-lowerEigenvalue)*(2+tau-lowerEigenvalue)

theorem winnerV_ne_zero : winnerV ≠ 0 := by
  have h := lowerEigenvalue_lt_cutoff
  unfold winnerV
  exact mul_ne_zero (neg_ne_zero.mpr (ne_of_gt tau_pos)) (by linarith)

/-- The three distinct rows of the eigenvalue equation on the even
subspace `(u,v,w,w,v)` of the winning matrix. -/
theorem winning_eigen_equations :
    2*winnerU - 2*(1+tau)*winnerW = lowerEigenvalue*winnerU ∧
    (2+tau)*winnerV + tau*winnerW = lowerEigenvalue*winnerV ∧
    (-1-tau)*winnerU + tau*winnerV - (1+tau)*winnerW = lowerEigenvalue*winnerW := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [winnerU, winnerV, winnerW]
  · ring
  · ring
  · have ht : tau^2+tau-1=0 := sub_eq_zero.mpr tau_sq
    linear_combination (2+2*tau-lowerEigenvalue)*lowerEigenvalue_poly - 2*tau*ht

def winningKinds : Fin 5 → Fin 5 → Fin 4 :=
  ![![3,0,2,2,0], ![0,3,1,0,1], ![2,1,0,2,0], ![2,0,2,0,1], ![0,1,0,1,3]]

private def kindCoeff (i : Fin 4) : Cyclotomic :=
  ![Cyclotomic.scalar 0, ⟨0,1,0,0,1⟩, ⟨0,0,1,1,0⟩, Cyclotomic.scalar 2] i

def kindValue (i : Fin 4) : ℝ := ![0, tau, -1-tau, 2] i

private theorem kindCoeff_eval (i : Fin 4) : (kindCoeff i).eval zeta = (kindValue i : ℂ) := by
  fin_cases i <;>
    simp [kindCoeff, kindValue, Cyclotomic.eval, Cyclotomic.scalar, zeta_pair, zeta_pair2]

private theorem winning_entries :
    ∀ i j : Fin 5, sumEntry winningMask i j = kindCoeff (winningKinds i j) := by decide

theorem phaseSum_winning (i j : Fin 5) :
    phaseSum winningMask i j = (kindValue (winningKinds i j) : ℂ) := by
  unfold phaseSum
  rw [winning_entries]
  exact kindCoeff_eval _

def winningVector : Fin 5 → ℝ := ![winnerU, winnerV, winnerW, winnerW, winnerV]

theorem winning_eigenvector (i : Fin 5) :
    ∑ j : Fin 5, phaseSum winningMask i j * (winningVector j : ℂ) =
      (lowerEigenvalue : ℂ) * (winningVector i : ℂ) := by
  simp_rw [phaseSum_winning, ← Complex.ofReal_mul, ← Complex.ofReal_sum]
  exact congrArg Complex.ofReal (by
    obtain ⟨hu, hv, hw⟩ := winning_eigen_equations
    fin_cases i <;> simp [winningVector, winningKinds, kindValue, Fin.sum_univ_succ] <;>
      first | linarith only [hu] | linarith only [hv] | linarith only [hw])

def squaredLength (n : ℕ) (v : ℕ → ℂ) : ℝ :=
  ∑ i ∈ Finset.range n, Complex.normSq (v i)

theorem squaredLength_nonneg (n : ℕ) (v : ℕ → ℂ) : 0 ≤ squaredLength n v :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

def affineMatrix (a b : ℂ) (A : ℕ → ℕ → ℂ) : ℕ → ℕ → ℂ :=
  fun i j => a * A i j + if i = j then b else 0

private theorem affineMatrix_row (n : ℕ) (a b : ℂ) (A : ℕ → ℕ → ℂ) (v : ℕ → ℂ)
    {i : ℕ} (hi : i ∈ Finset.range n) :
    (∑ j ∈ Finset.range n, affineMatrix a b A i j * v j) =
      a * (∑ j ∈ Finset.range n, A i j * v j) + b * v i := by
  unfold affineMatrix
  simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
  congr 1
  simp [ite_mul, hi]

theorem quadratic_affineMatrix (n : ℕ) (a b : ℂ) (A : ℕ → ℕ → ℂ) (v : ℕ → ℂ) :
    quadratic n (affineMatrix a b A) v =
      a * quadratic n A v + b * (squaredLength n v : ℂ) := by
  unfold quadratic squaredLength
  rw [Complex.ofReal_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [affineMatrix_row n a b A v hi, Complex.normSq_eq_conj_mul_self]
  ring

theorem compression_bound {m : Mask} {size : ℕ} (hm : (m, size) ∈ orbitRepresentatives)
    (v : ℕ → ℂ) :
    let n := if m == winningMask then 4 else 5;
    -(139/50) * squaredLength n v ≤ (quadratic n (phaseSum m) v).re := by
  dsimp
  have h := certified_compression hm v
  have hmat : (fun i j => (shiftedEntry m i j).eval zeta) =
      affineMatrix 50 139 (phaseSum m) := by
    funext i j
    exact shiftedEntry_eval m i j
  rw [hmat, quadratic_affineMatrix] at h
  norm_num [Complex.add_re, Complex.mul_re] at h ⊢
  linarith

def winner (i : ℕ) : ℂ := if h : i < 5 then (winningVector ⟨i, h⟩ : ℂ) else 0

theorem winner_last_ne_zero : winner 4 ≠ 0 := by
  simpa [winner, winningVector] using (Complex.ofReal_ne_zero.mpr winnerV_ne_zero)

theorem winner_row {i : ℕ} (hi : i ∈ Finset.range 5) :
    (∑ j ∈ Finset.range 5, phaseSum winningMask i j * winner j) =
      (lowerEigenvalue : ℂ) * winner i := by
  have hi' := Finset.mem_range.mp hi
  rw [← Fin.sum_univ_eq_sum_range]
  simpa [winner, hi'] using winning_eigenvector ⟨i, hi'⟩

private theorem quadratic_last_zero {n : ℕ} {A : ℕ → ℕ → ℂ}
    {v : ℕ → ℂ} (hv : v n = 0) :
    quadratic (n+1) A v = quadratic n A v := by
  unfold quadratic
  rw [Finset.sum_range_succ]
  simp only [hv, map_zero, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_range_succ, hv, mul_zero, add_zero]

private theorem quadratic_sub_null {A : ℕ → ℕ → ℂ} {n : ℕ} (hA : Hermitian A n)
    {w : ℕ → ℂ} (hw : ∀ i ∈ Finset.range n, ∑ j ∈ Finset.range n, A i j * w j = 0)
    (v : ℕ → ℂ) (c : ℂ) :
    quadratic n A (fun i => v i - c*w i) = quadratic n A v := by
  have hcol (j : ℕ) (hj : j ∈ Finset.range n) :
      (∑ i ∈ Finset.range n, conj (w i) * A i j) = 0 := by
    rw [← map_zero (starRingEnd ℂ), ← hw j hj, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [map_mul, hA j (Finset.mem_range.mp hj) i (Finset.mem_range.mp hi), mul_comm]
  have hrow (i : ℕ) (hi : i ∈ Finset.range n) :
      (∑ j ∈ Finset.range n, A i j * (v j-c*w j)) =
        ∑ j ∈ Finset.range n, A i j * v j := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    simp_rw [show ∀ j, A i j * (c*w j) = c*(A i j * w j) by intro; ring]
    rw [← Finset.mul_sum, hw i hi, mul_zero, sub_zero]
  unfold quadratic
  simp only [map_sub, map_mul]
  calc
    _ = ∑ i ∈ Finset.range n, (conj (v i)-conj c*conj (w i)) *
        (∑ j ∈ Finset.range n, A i j * v j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hrow i hi]
    _ = (∑ i ∈ Finset.range n, conj (v i) * ∑ j ∈ Finset.range n, A i j * v j) -
        conj c * (∑ i ∈ Finset.range n, conj (w i) * ∑ j ∈ Finset.range n, A i j * v j) := by
      simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = _ := by
      have hz : (∑ i ∈ Finset.range n, conj (w i) * ∑ j ∈ Finset.range n, A i j * v j) = 0 := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_eq_zero
        intro j hj
        simp_rw [← mul_assoc]
        rw [← Finset.sum_mul, hcol j hj, zero_mul]
      rw [hz, mul_zero, sub_zero]

theorem representative_lower_bound {m : Mask} {size : ℕ}
    (hm : (m, size) ∈ orbitRepresentatives) (v : ℕ → ℂ) :
    lowerEigenvalue * squaredLength 5 v ≤ (quadratic 5 (phaseSum m) v).re := by
  have hcut := lowerEigenvalue_lt_cutoff
  by_cases he : m = winningMask
  · subst m
    let B := affineMatrix 1 (-(lowerEigenvalue : ℂ)) (phaseSum winningMask)
    have hB : Hermitian B 5 := by
      intro i hi j hj
      change conj (affineMatrix 1 (-(lowerEigenvalue : ℂ)) (phaseSum winningMask) i j) =
        affineMatrix 1 (-(lowerEigenvalue : ℂ)) (phaseSum winningMask) j i
      simp only [affineMatrix, one_mul, map_add]
      rw [phaseSum_hermitian _ (le_refl 5) i hi j hj]
      by_cases hh : i = j <;> simp [hh, eq_comm]
    have hnull (i : ℕ) (hi : i ∈ Finset.range 5) :
        (∑ j ∈ Finset.range 5, B i j * winner j) = 0 := by
      rw [affineMatrix_row 5 1 (-(lowerEigenvalue : ℂ)) _ _ hi, winner_row hi, one_mul]
      ring
    let c := v 4 / winner 4
    let u := fun i => v i - c * winner i
    have hz : u 4 = 0 := by
      simp only [u, c, div_mul_cancel₀ _ winner_last_ne_zero, sub_self]
    have hh := compression_bound hm u
    simp only [beq_self_eq_true, if_true] at hh
    have hs : 0 ≤ (quadratic 4 B u).re := by
      rw [quadratic_affineMatrix]
      simp [Complex.add_re, Complex.mul_re]
      nlinarith [mul_le_mul_of_nonneg_right hcut.le (squaredLength_nonneg 4 u)]
    have hq : 0 ≤ (quadratic 5 B v).re := by
      rw [← quadratic_sub_null hB hnull v c, show
        (fun i => v i - c*winner i) = u by rfl, quadratic_last_zero hz]
      exact hs
    change 0 ≤ (quadratic 5 (affineMatrix 1 (-(lowerEigenvalue : ℂ)) (phaseSum winningMask)) v).re at hq
    rw [quadratic_affineMatrix] at hq
    simp [Complex.add_re, Complex.mul_re] at hq
    linarith
  · have h := compression_bound hm v
    simp [he] at h
    exact (mul_le_mul_of_nonneg_right hcut.le (squaredLength_nonneg 5 v)).trans
      (by simpa only [neg_mul] using h)

theorem winning_quadratic :
    (quadratic 5 (phaseSum winningMask) winner).re =
      lowerEigenvalue * squaredLength 5 winner := by
  have h : quadratic 5 (phaseSum winningMask) winner =
      (lowerEigenvalue : ℂ) * (squaredLength 5 winner : ℂ) := by
    unfold quadratic squaredLength
    rw [Complex.ofReal_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [winner_row hi, Complex.normSq_eq_conj_mul_self]
    ring
  simpa [Complex.mul_re] using congrArg Complex.re h

/-- Maximizing a negative sum over subsets picks exactly the negative
entries, with arbitrary choices allowed at zeros. -/
theorem negativity_subset_bound {ι : Type*} [Fintype ι] (f : ι → ℝ) (T : Finset ι) :
    -(∑ u ∈ T, f u) ≤ ∑ u, max 0 (-f u) := by
  classical
  rw [← Finset.sum_neg_distrib]
  exact (Finset.sum_le_sum fun _ _ => le_max_right _ _).trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ T)
      (fun _ _ _ => le_max_left _ _))

theorem negativity_at_negative_support {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    ∃ T : Finset ι, -(∑ u ∈ T, f u) = ∑ u, max 0 (-f u) := by
  classical
  refine ⟨Finset.univ.filter (fun u => f u < 0), ?_⟩
  rw [← Finset.sum_neg_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u _
  by_cases h : f u < 0
  · simp [h, max_eq_right (by linarith : 0 ≤ -f u)]
  · simp [h, max_eq_left (by linarith [le_of_not_gt h] : -f u ≤ 0)]

end
end WignerFive
