import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open scoped BigOperators ComplexConjugate

/-!
# Strict visibility improvement along the qutrit SIC family

The variables of the averaged seed are its population at the missing
coordinate and its aligned off-diagonal coherence. In these coordinates
the depolarized targets lie on the line `c = 1 - 3*p`.
-/

namespace HesseSIC

noncomputable section

def alpha : ℝ := Real.pi / 9
def C : ℝ := Real.cos alpha
def S : ℝ := Real.sin alpha

def hesseVisibility : ℝ := (1 + 4 * C) / 6
def twoPopulation : ℝ := (9 - 8 * C) / 27
def twoCoherence : ℝ := (6 + 16 * C) / 27
def threePopulation : ℝ := 1 / 9

def threeWeight (x : ℝ) : ℝ :=
  (4 * C - 3) / (4 * C * (1 + 3 / x) - 12)

def visibility (x : ℝ) : ℝ :=
  1 - 3 * ((1 - threeWeight x) * twoPopulation + threeWeight x * threePopulation)

def phaseWeight (x y : ℝ) : ℝ :=
  (1 - C * y / (S * x)) / 2

private def labels : List ℕ := List.range 9

private def q (i : ℕ) := i / 3
private def p (i : ℕ) := i % 3

private def noncollinear (i j k : ℕ) : Bool :=
  let a := (q j + 3 - q i) * (p k + 3 - p i)
  let b := (q k + 3 - q i) * (p j + 3 - p i)
  a % 3 != b % 3

private def triples : List (ℕ × ℕ × ℕ) :=
  labels.flatMap fun i =>
    labels.flatMap fun j =>
      (labels.filter fun k => i < j && j < k && noncollinear i j k).map fun k => (i,j,k)

private def usesThreeCoordinates (i j k : ℕ) : Bool :=
  q i != q j && q j != q k && q i != q k

set_option maxRecDepth 4096 in
/-- Of the noncollinear triples, 54 use two missing coordinates and
the other 18 split equally into the conjugate phase classes. -/
theorem triple_counts :
    triples.length = 72 ∧
    (triples.filter fun (i,j,k) => !usesThreeCoordinates i j k).length = 54 ∧
    (triples.filter fun (i,j,k) =>
      usesThreeCoordinates i j k && (p i + p j + p k) % 3 == 1).length = 9 ∧
    (triples.filter fun (i,j,k) =>
      usesThreeCoordinates i j k && (p i + p j + p k) % 3 == 2).length = 9 := by decide

private theorem alpha_pos : 0 < alpha := by
  unfold alpha
  positivity

theorem three_quarters_lt_C : 3 / 4 < C := by
  have h := Real.cos_le_cos_of_nonneg_of_le_pi (le_of_lt alpha_pos)
    (show Real.pi / 6 ≤ Real.pi by linarith [Real.pi_pos])
    (show alpha ≤ Real.pi / 6 by unfold alpha; linarith [Real.pi_pos])
  rw [Real.cos_pi_div_six] at h
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hn := Real.sqrt_nonneg (3 : ℝ)
  unfold C
  nlinarith

theorem S_pos : 0 < S := by
  exact Real.sin_pos_of_pos_of_lt_pi alpha_pos (by unfold alpha; linarith [Real.pi_pos])

theorem C_le_one : C ≤ 1 := Real.cos_le_one _

theorem angle_range {θ : ℝ} (hθ : 0 ≤ θ) (hα : θ ≤ alpha) :
    C ≤ Real.cos θ ∧ 0 ≤ Real.sin θ ∧
    C * Real.sin θ ≤ S * Real.cos θ := by
  have ha : alpha ≤ Real.pi := by unfold alpha; linarith [Real.pi_pos]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi hθ ha hα
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi hθ (hα.trans ha)
  have hd := Real.sin_nonneg_of_nonneg_of_le_pi (sub_nonneg.mpr hα)
    (by linarith)
  rw [Real.sin_sub] at hd
  exact ⟨hc, hs, by unfold C S; linarith⟩

def phasePower (omitted i : Fin 3) : ℕ :=
  if i = omitted+1 then 2 else if i = omitted+2 then 0 else 1

def phaseGauge (omitted : Fin 3) (z : ℂ) (i : Fin 3) : ℂ :=
  z ^ phasePower omitted i

private theorem phasePower_step :
    ∀ omitted q : Fin 3, q ≠ omitted →
      phasePower omitted (q+2) = 1 + phasePower omitted (q+1) := by decide

theorem phaseGauge_unit {z : ℂ} (hz : z * conj z = 1) (omitted i : Fin 3) :
    phaseGauge omitted z i * conj (phaseGauge omitted z i) = 1 := by
  simp only [phaseGauge, map_pow, ← mul_pow, hz, one_pow]

/-- The two active coordinate pairs can be adjusted by the same diagonal
unitary. Its third pair is unconstrained. -/
theorem transport_coherence {omitted q : Fin 3} (hq : q ≠ omitted)
    {z : ℂ} (hz : z * conj z = 1) (u v : ℂ) :
    z * (phaseGauge omitted z (q+1) * u) *
      conj (phaseGauge omitted z (q+2) * v) = u * conj v := by
  have hs : phaseGauge omitted z (q+2) = z * phaseGauge omitted z (q+1) := by
    rw [phaseGauge, phasePower_step omitted q hq, pow_add, pow_one, ← phaseGauge]
  calc
    _ = (z * conj z) * (phaseGauge omitted z (q+1) *
          conj (phaseGauge omitted z (q+1))) * (u * conj v) := by
      rw [hs, map_mul, map_mul]
      ring
    _ = _ := by rw [hz, phaseGauge_unit hz, one_mul, one_mul]

/-- Diagonal transport preserves all inner products of basis vectors. -/
theorem transport_orthonormal {z : ℂ} (hz : z * conj z = 1)
    (omitted : Fin 3) (u v : Fin 3 → ℂ) :
    (∑ i, conj (phaseGauge omitted z i * u i) * (phaseGauge omitted z i * v i)) =
      ∑ i, conj (u i) * v i := by
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul]
  calc
    _ = (phaseGauge omitted z i * conj (phaseGauge omitted z i)) * (conj (u i) * v i) := by ring
    _ = _ := by rw [phaseGauge_unit hz, one_mul]

theorem cos_lt_one {θ : ℝ} (hθ : 0 < θ) (hα : θ ≤ alpha) : Real.cos θ < 1 := by
  have ha : alpha ≤ Real.pi := by unfold alpha; linarith [Real.pi_pos]
  have h := Real.strictAntiOn_cos
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (show θ ∈ Set.Icc 0 Real.pi from ⟨hθ.le, hα.trans ha⟩) hθ
  simpa only [Real.cos_zero] using h

/-- The two triples with conjugate seed coherences admit a real mixture. -/
theorem phase_interpolation {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hphase : C * y ≤ S * x) (hunit : x^2 + y^2 = 1) :
    0 ≤ phaseWeight x y ∧ phaseWeight x y ≤ 1 ∧
    phaseWeight x y * (x * C - y * S) +
      (1 - phaseWeight x y) * (x * C + y * S) = C / x ∧
    phaseWeight x y * (y * C + x * S) +
      (1 - phaseWeight x y) * (y * C - x * S) = 0 := by
  have hC : 0 ≤ C := by linarith [three_quarters_lt_C]
  have hd : 0 < S * x := mul_pos S_pos hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold phaseWeight
    linarith [((div_le_iff₀ hd).mpr (show C*y ≤ 1*(S*x) by simpa using hphase))]
  · unfold phaseWeight
    linarith [div_nonneg (mul_nonneg hC hy) hd.le]
  · have hw : 1 - 2 * phaseWeight x y = C*y/(S*x) := by unfold phaseWeight; ring
    calc
      _ = C*x + (1-2*phaseWeight x y)*y*S := by ring
      _ = C*x + C*y^2/x := by rw [hw]; field_simp [S_pos.ne', hx.ne']
      _ = C/x := by field_simp [hx.ne']; linear_combination C*hunit
  · have hw : 1 - 2 * phaseWeight x y = C*y/(S*x) := by unfold phaseWeight; ring
    calc
      _ = C*y - (1-2*phaseWeight x y)*x*S := by ring
      _ = 0 := by rw [hw]; field_simp [S_pos.ne', hx.ne']; ring

theorem weight_range {x : ℝ} (hx : C ≤ x) (hx1 : x ≤ 1) :
    0 < threeWeight x ∧ threeWeight x ≤ 1 / 4 := by
  have hC := three_quarters_lt_C
  have hx0 : 0 < x := by linarith
  have h : 3 ≤ 3 / x := (le_div_iff₀ hx0).mpr (by linarith)
  have hmul : 4*C*4 ≤ 4*C*(1+3/x) := by
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  have hn : 0 < 4*C-3 := by linarith
  have hd : 0 < 4*C*(1+3/x)-12 := by linarith
  exact ⟨div_pos hn hd, (div_le_iff₀ hd).mpr (by linarith)⟩

theorem weight_strict {x : ℝ} (hx : C ≤ x) (hx1 : x < 1) :
    threeWeight x < 1 / 4 := by
  have hC := three_quarters_lt_C
  have hx0 : 0 < x := by linarith
  have h : 3 < 3 / x := (lt_div_iff₀ hx0).mpr (by linarith)
  have hmul : 4*C*4 < 4*C*(1+3/x) := by
    apply mul_lt_mul_of_pos_left _ (by linarith)
    linarith
  unfold threeWeight
  exact (div_lt_iff₀ (by linarith : 0 < 4*C*(1+3/x)-12)).mpr (by linarith)

theorem visibility_improves {x : ℝ} (hx : C ≤ x) (hx1 : x < 1) :
    hesseVisibility < visibility x := by
  have hp : 0 < (8*C-6)/9 := by linarith [three_quarters_lt_C]
  have h := mul_pos hp (sub_pos.mpr (weight_strict hx hx1))
  have he : visibility x - hesseVisibility = (8*C-6)/9 * (1/4 - threeWeight x) := by
    unfold hesseVisibility visibility twoPopulation threePopulation
    ring
  linarith

theorem visibility_at_hesse : visibility 1 = hesseVisibility := by
  have hn : 4*C-3 ≠ 0 := by linarith [three_quarters_lt_C]
  have hw : threeWeight 1 = 1/4 := by
    unfold threeWeight
    have hd : 4*C*(1+3/(1 : ℝ))-12 = 4*(4*C-3) := by ring
    rw [hd]
    field_simp [hn]
  unfold visibility hesseVisibility twoPopulation threePopulation
  rw [hw]
  ring

theorem visibility_range {x : ℝ} (hx : C ≤ x) (hx1 : x ≤ 1) :
    visibility x ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨hwpos, hw⟩ := weight_range hx hx1
  have hc := three_quarters_lt_C
  have hC := C_le_one
  have hdiff : visibility x - hesseVisibility = (8*C-6)/9 * (1/4-threeWeight x) := by
    unfold visibility hesseVisibility twoPopulation threePopulation
    ring
  have hlow := mul_nonneg (by linarith : 0 ≤ (8*C-6)/9) (sub_nonneg.mpr hw)
  have hhigh : 0 ≤ (1-threeWeight x)*twoPopulation + threeWeight x*threePopulation := by
    unfold twoPopulation threePopulation
    exact add_nonneg (mul_nonneg (by linarith) (by linarith))
      (mul_nonneg hwpos.le (by norm_num))
  refine ⟨?_, ?_⟩
  · unfold hesseVisibility at hdiff
    linarith
  · unfold visibility
    linarith

/-- The population and (real) coherence of the mixture give the same
visibility, exactly, throughout the parameter range. -/
theorem blend_target {x : ℝ} (hx : C ≤ x) (hx1 : x ≤ 1) :
    (1 - threeWeight x) * twoPopulation + threeWeight x * threePopulation =
      (1 - visibility x) / 3 ∧
    (1 - threeWeight x) * twoCoherence + threeWeight x * (8*C/(9*x)) =
      visibility x := by
  constructor
  · unfold visibility
    ring
  · have hC := three_quarters_lt_C
    have hx0 : 0 < x := by linarith
    have h : 3 ≤ 3 / x := (le_div_iff₀ hx0).mpr (by linarith)
    have hmul : 4*C*4 ≤ 4*C*(1+3/x) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      linarith
    have hd : 0 < 4*C*(1+3/x)-12 := by linarith
    have hw : threeWeight x * (4*C*(1+3/x)-12) = 4*C-3 := by
      unfold threeWeight
      exact div_mul_cancel₀ _ hd.ne'
    unfold visibility twoCoherence twoPopulation threePopulation
    linarith only [show
      (1 - threeWeight x) * ((6+16*C)/27) +
        threeWeight x*(8*C/(9*x)) -
        (1-3*((1-threeWeight x)*((9-8*C)/27)+threeWeight x*(1/9))) =
        (threeWeight x*(4*C*(1+3/x)-12) - (4*C-3)) * (2/27) by ring_nf,
      hw]

structure Seed where
  population : ℝ
  coherenceRe : ℝ
  coherenceIm : ℝ

def mix (w : ℝ) (a b : Seed) : Seed :=
  ⟨(1-w)*a.population + w*b.population,
   (1-w)*a.coherenceRe + w*b.coherenceRe,
   (1-w)*a.coherenceIm + w*b.coherenceIm⟩

def target (v : ℝ) : Seed := ⟨(1-v)/3, v, 0⟩

def twoCoordinates : Seed := ⟨twoPopulation, twoCoherence, 0⟩

def threeCoordinates (x y : ℝ) (s : ℝ) : Seed :=
  ⟨threePopulation, (8/9)*(x*C-y*s), (8/9)*(y*C+x*s)⟩

theorem coordinates_from_hesse_split {p c : ℝ}
    (hp : (3/4)*p + (1/4)*(1/9) = (1-hesseVisibility)/3)
    (hc : (3/4)*c + (1/4)*(8*C/9) = hesseVisibility) :
    p = twoPopulation ∧ c = twoCoherence := by
  unfold hesseVisibility at hp hc
  constructor
  · unfold twoPopulation
    linarith
  · unfold twoCoherence
    linarith

theorem mix_phase_coordinates {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hphase : C*y ≤ S*x) (hunit : x^2+y^2=1) :
    mix (phaseWeight x y) (threeCoordinates x y (-S)) (threeCoordinates x y S) =
      ⟨threePopulation, 8*C/(9*x), 0⟩ := by
  obtain ⟨_, _, hre, him⟩ := phase_interpolation hx hy hphase hunit
  simp only [mix, threeCoordinates, Seed.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · ring
  · linear_combination (8/9 : ℝ)*hre
  · linear_combination (8/9 : ℝ)*him

/-- The three seed measurements yield a depolarized target for the
entire interval, via two mixtures with nonnegative coefficients. -/
theorem explicit_target {θ : ℝ} (h₀ : 0 ≤ θ) (h₁ : θ ≤ alpha) :
    let x := Real.cos θ
    let y := Real.sin θ
    phaseWeight x y ∈ Set.Icc (0 : ℝ) 1 ∧
    threeWeight x ∈ Set.Icc (0 : ℝ) 1 ∧
    mix (threeWeight x) twoCoordinates
      (mix (phaseWeight x y) (threeCoordinates x y (-S)) (threeCoordinates x y S)) =
      target (visibility x) := by
  dsimp
  obtain ⟨hx, hy, hs⟩ := angle_range h₀ h₁
  have hx0 : 0 < Real.cos θ := by linarith [three_quarters_lt_C]
  have hu : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hw := weight_range hx (Real.cos_le_one θ)
  have hp := phase_interpolation hx0 hy hs hu
  have ht := blend_target hx (Real.cos_le_one θ)
  refine ⟨⟨hp.1, hp.2.1⟩, ⟨hw.1.le, by linarith [hw.2]⟩, ?_⟩
  rw [mix_phase_coordinates hx0 hy hs hu]
  simp only [mix, twoCoordinates, target, Seed.mk.injEq]
  exact ⟨ht.1, ht.2, by ring⟩

/-- Any convex set of seed measurements that contains the three
constructed prototypes contains a target strictly above the Hesse value. -/
theorem strict_family_of_prototypes {θ : ℝ} (h₀ : 0 < θ) (h₁ : θ ≤ alpha)
    {admissible : Set Seed}
    (hmix : ∀ {w : ℝ} {a b : Seed}, w ∈ Set.Icc (0 : ℝ) 1 →
      a ∈ admissible → b ∈ admissible → mix w a b ∈ admissible)
    (h₂ : twoCoordinates ∈ admissible)
    (hminus : threeCoordinates (Real.cos θ) (Real.sin θ) (-S) ∈ admissible)
    (hplus : threeCoordinates (Real.cos θ) (Real.sin θ) S ∈ admissible) :
    ∃ v ∈ Set.Icc (0 : ℝ) 1, hesseVisibility < v ∧ target v ∈ admissible := by
  obtain ⟨hp, hw, htarget⟩ := explicit_target h₀.le h₁
  obtain ⟨hx, _, _⟩ := angle_range h₀.le h₁
  refine ⟨visibility (Real.cos θ), visibility_range hx (Real.cos_le_one θ),
    visibility_improves hx (cos_lt_one h₀ h₁), ?_⟩
  rw [← htarget]
  exact hmix hw h₂ (hmix hp hminus hplus)

end
end HesseSIC
