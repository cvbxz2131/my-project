import DominatorFourCert
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Combinatorics.SimpleGraph.Coloring
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases

/-! The minimum order of a graph whose three domination and coloring
parameters all equal four. -/

namespace DominatorFour

open Classical

section GraphParameters

variable {V : Type*} (G : SimpleGraph V)

def Closed (u v : V) : Prop := u = v ∨ G.Adj u v

def Dominates (D : Finset V) : Prop :=
  ∀ v, ∃ u ∈ D, Closed G u v

def DominatorColoring {k : ℕ} (c : G.Coloring (Fin k)) : Prop :=
  ∀ v, ∃ i, (∃ w, c w = i) ∧ ∀ w, c w = i → Closed G v w

def HasDominatorColoring (k : ℕ) : Prop :=
  ∃ c : G.Coloring (Fin k), DominatorColoring G c

def NoDominatingTriple : Prop :=
  ∀ a b c, ¬ ∀ v, Closed G a v ∨ Closed G b v ∨ Closed G c v

variable [Fintype V]

private theorem domination_feasible : ∃ n, ∃ s : Finset V, s.card = n ∧ Dominates G s :=
  ⟨Fintype.card V, Finset.univ, Finset.card_univ,
    fun v => ⟨v, Finset.mem_univ v, Or.inl rfl⟩⟩

private theorem coloring_feasible : ∃ k, HasDominatorColoring G k := by
  let f := Fintype.equivFin V
  let c : G.Coloring (Fin (Fintype.card V)) :=
    SimpleGraph.Coloring.mk f (fun h he => G.ne_of_adj h (f.injective he))
  refine ⟨Fintype.card V, c, fun v => ⟨c v, ⟨v, rfl⟩, ?_⟩⟩
  intro w h
  exact Or.inl (f.injective h.symm)

noncomputable def dominationNumber : ℕ := Nat.find (domination_feasible G)

noncomputable def dominatorChromaticNumber : ℕ := Nat.find (coloring_feasible G)

theorem dominationNumber_le {s : Finset V} (h : Dominates G s) :
    dominationNumber G ≤ s.card :=
  Nat.find_min' (domination_feasible G) ⟨s, rfl, h⟩

theorem dominatorChromaticNumber_le {k : ℕ} (h : HasDominatorColoring G k) :
    dominatorChromaticNumber G ≤ k :=
  Nat.find_min' (coloring_feasible G) h

theorem noDominatingTriple_of_four_le (h : 4 ≤ dominationNumber G) :
    NoDominatingTriple G := by
  classical
  intro a b c hcover
  have hd : Dominates G ({a, b, c} : Finset V) := by
    intro v
    rcases hcover v with ha | hb | hc
    · exact ⟨a, by simp, ha⟩
    · exact ⟨b, by simp, hb⟩
    · exact ⟨c, by simp, hc⟩
  exact (by decide : ¬ 4 ≤ (3 : ℕ))
    (h.trans ((dominationNumber_le G hd).trans Finset.card_le_three))

private theorem four_le_of_noDominatingTriple [Nonempty V] (h : NoDominatingTriple G) :
    4 ≤ dominationNumber G := by
  classical
  by_contra! hlt
  obtain ⟨s, hc, hs⟩ := Nat.find_spec (domination_feasible G)
  change s.card = dominationNumber G at hc
  have h3 : s.card ≤ 3 := by omega
  let v₀ : V := Classical.choice ‹Nonempty V›
  have hsub : ∃ a b c, s ⊆ ({a, b, c} : Finset V) := by
    interval_cases hn : s.card
    · exact ⟨v₀, v₀, v₀, by simp [Finset.card_eq_zero.mp hn]⟩
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hn
      exact ⟨v, v, v, by simp⟩
    · obtain ⟨v, w, _, rfl⟩ := Finset.card_eq_two.mp hn
      exact ⟨v, w, w, by simp⟩
    · obtain ⟨u, v, w, _, _, _, rfl⟩ := Finset.card_eq_three.mp hn
      exact ⟨u, v, w, Finset.Subset.rfl⟩
  obtain ⟨a, b, c, habc⟩ := hsub
  apply h a b c
  intro v
  obtain ⟨u, hu, huv⟩ := hs v
  have hu' : u = a ∨ u = b ∨ u = c := by simpa using habc hu
  rcases hu' with rfl | rfl | rfl
  · exact Or.inl huv
  · exact Or.inr (Or.inl huv)
  · exact Or.inr (Or.inr huv)

end GraphParameters

section Recoloring

variable {V : Type*} {G : SimpleGraph V}

/-- If the fourth color is necessary, each color has a vertex with a
neighbor in every other color. Otherwise recolor that independent class. -/
theorem seesOtherColors (f : G.Coloring (Fin 4)) (hχ : ¬ G.Colorable 3) (i : Fin 4) :
    ∃ x, f x = i ∧ ∀ j : Fin 4, j ≠ i → ∃ y, f y = j ∧ G.Adj x y := by
  classical
  by_contra! h
  let newColor : V → Fin 4 := fun v =>
    if hv : f v = i then (h v hv).choose else f v
  have avoids (v : V) : newColor v ≠ i := by
    by_cases hv : f v = i
    · simpa [newColor, hv] using (h v hv).choose_spec.1
    · simp [newColor, hv]
  have proper {v w : V} (ha : G.Adj v w) : newColor v ≠ newColor w := by
    intro heq
    by_cases hv : f v = i <;> by_cases hw : f w = i
    · exact f.valid ha (hv.trans hw.symm)
    · have hj : f w = (h v hv).choose := by
        simpa [newColor, hv, hw] using heq.symm
      exact (h v hv).choose_spec.2 w hj ha
    · have hj : f v = (h w hw).choose := by
        simpa [newColor, hv, hw] using heq
      exact (h w hw).choose_spec.2 v hj (G.symm ha)
    · exact f.valid ha (by simpa [newColor, hv, hw] using heq)
  let swap := Equiv.swap i (3 : Fin 4)
  have fits (v : V) : (swap (newColor v)).val < 3 := by
    have hv : swap (newColor v) ≠ 3 := by
      intro he
      exact avoids v (swap.injective (he.trans (Equiv.swap_apply_left i 3).symm))
    have hne : (swap (newColor v)).val ≠ 3 := fun he => hv (Fin.ext he)
    have hlt := (swap (newColor v)).isLt
    omega
  apply hχ
  refine ⟨SimpleGraph.Coloring.mk (fun v => (swap (newColor v)).castLT (fits v)) ?_⟩
  intro v w ha he
  exact proper ha (swap.injective (Fin.ext (congrArg (fun i : Fin 3 => i.val) he)))

end Recoloring

section BlockVertices

abbrev BlockVertex (p : Profile) := Σ i : Fin 4, Fin (p.size i)

def rank {p : Profile} (v : BlockVertex p) : ℕ := p.offset v.1 + v.2.val

private theorem rank_lt {p : Profile} (v : BlockVertex p) : rank v < p.order := by
  obtain ⟨i, u⟩ := v
  have hu := u.isLt
  fin_cases i <;> simp [rank, Profile.offset, Profile.order, Profile.size] at hu ⊢ <;> omega

private theorem rank_injective (p : Profile) : Function.Injective (rank (p := p)) := by
  rintro ⟨i, u⟩ ⟨j, v⟩ h
  have hu := u.isLt
  have hv := v.isLt
  fin_cases i <;> fin_cases j <;> simp [rank, Profile.offset, Profile.size] at h hu hv ⊢ <;> omega

private theorem block_card (p : Profile) : Fintype.card (BlockVertex p) = p.order := by
  simp [BlockVertex, Fintype.card_sigma, Fin.sum_univ_succ, Profile.size, Profile.order,
    Nat.add_assoc]

private theorem exists_rank {p : Profile} {i : ℕ} (hi : i < p.order) :
    ∃ v : BlockVertex p, rank v = i := by
  let f : BlockVertex p → Fin p.order := fun v => ⟨rank v, rank_lt v⟩
  have hf : Function.Injective f := fun _ _ h => rank_injective p (congrArg Fin.val h)
  have hc : Fintype.card (BlockVertex p) = Fintype.card (Fin p.order) := by
    rw [block_card, Fintype.card_fin]
  obtain ⟨v, hv⟩ := ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hc⟩).2 ⟨i, hi⟩
  exact ⟨v, congrArg Fin.val hv⟩

private theorem mem_indices {p : Profile} {k : Fin 4} {i : ℕ} :
    i ∈ indices p k ↔ ∃ v : BlockVertex p, v.1 = k ∧ rank v = i := by
  rw [indices, List.mem_range'_1]
  constructor
  · rintro ⟨hl, hu⟩
    refine ⟨⟨k, ⟨i - p.offset k, by omega⟩⟩, rfl, ?_⟩
    change p.offset k + (i - p.offset k) = i
    omega
  · rintro ⟨⟨k, v⟩, rfl, rfl⟩
    have h := v.isLt
    change p.offset k ≤ p.offset k + v.val ∧ p.offset k + v.val < p.offset k + p.size k
    omega

private theorem mem_colors (k : Fin 4) : k ∈ colors := by
  fin_cases k <;> decide

private def firstVertex (p : Profile) (hp : ∀ k, 0 < p.size k) (k : Fin 4) : BlockVertex p :=
  ⟨k, ⟨0, hp k⟩⟩

@[simp] private theorem rank_firstVertex (p : Profile) (hp : ∀ k, 0 < p.size k) (k : Fin 4) :
    rank (firstVertex p hp k) = p.offset k := by
  simp [rank, firstVertex]

private theorem address_lt {i j : ℕ} (hi : i < 11) (hj : j < 11) : address i j < 121 := by
  unfold address
  omega

private theorem address_injective_mod_swap {i j u v : ℕ}
    (hi : i < 11) (hj : j < 11) (hu : u < 11) (hv : v < 11)
    (h : address i j = address u v) : (i = u ∧ j = v) ∨ (i = v ∧ j = u) := by
  simp only [address, Nat.min_def, Nat.max_def] at h
  split_ifs at h <;> omega

private noncomputable def asBits {p : Profile} (G : SimpleGraph (BlockVertex p)) : BitVec 121 :=
  (BitVec.ofBoolListLE (List.ofFn fun i : Fin 121 =>
    decide (∃ a b : BlockVertex p, address (rank a) (rank b) = i.val ∧ G.Adj a b))).cast
      (by rw [List.length_ofFn])

private theorem edge_asBits {p : Profile} (hp : p.order ≤ 11) (G : SimpleGraph (BlockVertex p))
    (a b : BlockVertex p) : edge (asBits G) (rank a) (rank b) = true ↔ G.Adj a b := by
  have hsmall (x : BlockVertex p) : rank x < 11 := (rank_lt x).trans_le hp
  have hindex := address_lt (hsmall a) (hsmall b)
  simp only [edge, asBits, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos hindex, Option.getD_some,
    decide_eq_true_eq]
  constructor
  · rintro ⟨u, v, he, huv⟩
    rcases address_injective_mod_swap (hsmall u) (hsmall v) (hsmall a) (hsmall b) he with
      ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [rank_injective p ha, rank_injective p hb] at huv
      exact huv
    · rw [rank_injective p ha, rank_injective p hb] at huv
      exact G.symm huv
  · intro h
    exact ⟨a, b, rfl, h⟩

private theorem covers_asBits {p : Profile} (hp : p.order ≤ 11)
    (G : SimpleGraph (BlockVertex p)) (a b : BlockVertex p) :
    covers (asBits G) (rank a) (rank b) = true ↔ Closed G a b := by
  simp [covers, Closed, (rank_injective p).eq_iff, edge_asBits hp G]

private theorem certificate_of_graph {p : Profile} (horder : p.order ≤ 11)
    (hpos : ∀ k, 0 < p.size k) (G : SimpleGraph (BlockVertex p))
    (hproper : ∀ v w, v.1 = w.1 → ¬ G.Adj v w)
    (hstar : ∀ i, i ≠ 0 → G.Adj (firstVertex p hpos 0) (firstVertex p hpos i))
    (hdom : ∀ v, ∃ k, ∀ w : BlockVertex p, w.1 = k → Closed G v w)
    (hno : NoDominatingTriple G) :
    properBits p (asBits G) = true ∧ hasStar p (asBits G) = true ∧
      dominatorBits p (asBits G) = true ∧ noTripleBits p (asBits G) = true := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro k _
    apply List.all_eq_true.mpr
    intro a ha
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨u, hu, rfl⟩ := mem_indices.mp ha
    obtain ⟨v, hv, rfl⟩ := mem_indices.mp hb
    have he := (edge_asBits horder G u v).not.mpr (hproper u v (hu.trans hv.symm))
    simpa using (Bool.eq_false_iff.mpr he)
  · have hs (i : Fin 4) (hi : i ≠ 0) :
        edge (asBits G) (p.offset 0) (p.offset i) = true := by
      simpa using (edge_asBits horder G _ _).mpr (hstar i hi)
    have h1 := hs 1 (by decide)
    have h2 := hs 2 (by decide)
    have h3 := hs 3 (by decide)
    change edge (asBits G) 0 p.a = true at h1
    change edge (asBits G) 0 (p.a + p.b) = true at h2
    change edge (asBits G) 0 (p.a + p.b + p.c) = true at h3
    simp [hasStar, h1, h2, h3]
  · apply List.all_eq_true.mpr
    intro a ha
    obtain ⟨v, rfl⟩ := exists_rank (List.mem_range.mp ha)
    obtain ⟨k, hk⟩ := hdom v
    refine List.any_eq_true.mpr ⟨k, mem_colors k, List.all_eq_true.mpr ?_⟩
    intro b hb
    obtain ⟨w, hw, rfl⟩ := mem_indices.mp hb
    exact (covers_asBits horder G v w).mpr (hk w hw)
  · apply List.all_eq_true.mpr
    rintro ⟨i, j, k⟩ ht
    obtain ⟨hi, hj, hk⟩ := triple_in_range ht
    obtain ⟨a, rfl⟩ := exists_rank hi
    obtain ⟨b, rfl⟩ := exists_rank hj
    obtain ⟨c, rfl⟩ := exists_rank hk
    obtain ⟨v, hv⟩ := not_forall.mp (hno a b c)
    refine List.any_eq_true.mpr ⟨rank v, List.mem_range.mpr (rank_lt v), ?_⟩
    have hn := hv
    simp only [not_or] at hn
    have ha := Bool.eq_false_iff.mpr ((covers_asBits horder G a v).not.mpr hn.1)
    have hb := Bool.eq_false_iff.mpr ((covers_asBits horder G b v).not.mpr hn.2.1)
    have hc := Bool.eq_false_iff.mpr ((covers_asBits horder G c v).not.mpr hn.2.2)
    simp [ha, hb, hc]

end BlockVertices

section MinimumOrder

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- A graph with a dominator four-coloring, chromatic number four, and
domination number at least four has at least twelve vertices. -/
theorem order_ge_twelve_of_coloring (f : G.Coloring (Fin 4))
    (hdom : DominatorColoring G f) (hχ : ¬ G.Colorable 3)
    (hγ : 4 ≤ dominationNumber G) : 12 ≤ Fintype.card V := by
  classical
  by_contra! hcard
  let count (i : Fin 4) := Fintype.card {v : V // f v = i}
  let reorder := Tuple.sort count
  let c : G.Coloring (Fin 4) :=
    SimpleGraph.Coloring.mk (fun v => reorder.symm (f v))
      (fun h he => f.valid h (reorder.symm.injective he))
  let size (i : Fin 4) := Fintype.card {v : V // c v = i}
  let p : Profile := ⟨size 0, size 1, size 2, size 3⟩
  have psize (i : Fin 4) : p.size i = size i := by fin_cases i <;> rfl
  have sortedSize (i : Fin 4) : p.size i = count (reorder i) := by
    rw [psize i]
    apply Fintype.card_congr
    apply Equiv.subtypeEquivRight
    intro v
    change reorder.symm (f v) = i ↔ f v = reorder i
    exact reorder.symm_apply_eq
  have sorted : Monotone p.size := by
    intro i j h
    rw [sortedSize i, sortedSize j]
    exact Tuple.monotone_sort count h
  obtain ⟨center, hc, hn⟩ := seesOtherColors c hχ 0
  let rep (i : Fin 4) : {v : V // c v = i} :=
    if hi : i = 0 then ⟨center, hc.trans hi.symm⟩
    else ⟨(hn i hi).choose, (hn i hi).choose_spec.1⟩
  have star (i : Fin 4) (hi : i ≠ 0) : G.Adj (rep 0).val (rep i).val := by
    simpa only [rep, dif_pos rfl, dif_neg hi] using (hn i hi).choose_spec.2
  have positive (i : Fin 4) : 0 < p.size i := by
    rw [psize i]
    exact Fintype.card_pos_iff.mpr ⟨rep i⟩
  let block (i : Fin 4) : Fin (p.size i) ≃ {v : V // c v = i} :=
    let e := (Fintype.equivFinOfCardEq (psize i).symm).symm
    (Equiv.swap ⟨0, positive i⟩ (e.symm (rep i))).trans e
  have blockFirst (i : Fin 4) : block i ⟨0, positive i⟩ = rep i := by
    simp only [block, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]
  let e : BlockVertex p ≃ V :=
    (Equiv.sigmaCongrRight block).trans (Equiv.sigmaFiberEquiv (⇑c))
  have color_e (v : BlockVertex p) : c (e v) = v.1 := (block v.1 v.2).property
  have first_e (i : Fin 4) : e (firstVertex p positive i) = (rep i).val := by
    exact congrArg Subtype.val (blockFirst i)
  have order : p.order = Fintype.card V := (block_card p).symm.trans (Fintype.card_congr e)
  have small : p.order ≤ 11 := by omega
  let H := G.comap (⇑e)
  have closes (a b : BlockVertex p) : Closed H a b ↔ Closed G (e a) (e b) := by
    simp [Closed, H, e.injective.eq_iff]
  have goodColor (a b : BlockVertex p) (he : a.1 = b.1) : ¬ H.Adj a b := by
    intro ha
    exact c.valid ha (by rw [color_e, color_e, he])
  have goodStar (i : Fin 4) (hi : i ≠ 0) :
      H.Adj (firstVertex p positive 0) (firstVertex p positive i) := by
    change G.Adj (e (firstVertex p positive 0)) (e (firstVertex p positive i))
    rw [first_e, first_e]
    exact star i hi
  have goodDom (v : BlockVertex p) : ∃ i, ∀ w : BlockVertex p, w.1 = i → Closed H v w := by
    obtain ⟨i, _, hi⟩ := hdom (e v)
    refine ⟨reorder.symm i, fun w hw => (closes _ _).mpr (hi _ ?_)⟩
    apply reorder.symm.injective
    exact (color_e w).trans hw
  have noTriple : NoDominatingTriple H := by
    intro a b c h
    apply noDominatingTriple_of_four_le G hγ (e a) (e b) (e c)
    intro v
    obtain ⟨v, rfl⟩ := e.surjective v
    simpa only [closes] using h v
  obtain ⟨hproper, hstar, hcolor, hno⟩ :=
    certificate_of_graph small positive H goodColor goodStar goodDom noTriple
  exact no_small_profile p (positive 0) (sorted (by decide : (0 : Fin 4) ≤ 1))
    (sorted (by decide : (1 : Fin 4) ≤ 2)) (sorted (by decide : (2 : Fin 4) ≤ 3))
    small (asBits H) hproper hstar hcolor hno

theorem order_ge_twelve (G : SimpleGraph V)
    (hγ : dominationNumber G = 4) (hχ : G.chromaticNumber = 4)
    (hχd : dominatorChromaticNumber G = 4) : 12 ≤ Fintype.card V := by
  have hno : ¬ G.Colorable 3 := by
    intro h
    have hh := SimpleGraph.chromaticNumber_le_iff_colorable.mpr h
    rw [hχ] at hh
    exact (by decide : ¬ (4 : ℕ∞) ≤ 3) hh
  have hex := Nat.find_spec (coloring_feasible G)
  change HasDominatorColoring G (dominatorChromaticNumber G) at hex
  rw [hχd] at hex
  obtain ⟨c, hc⟩ := hex
  exact order_ge_twelve_of_coloring c hc hno hγ.ge

end MinimumOrder

section PublishedConstruction

abbrev ExampleVertex := Fin 4 × Fin 3

/-- Two copies of K(3,3), with their four distinguished vertices joined
into a clique. This is Figure 2 of Kalarkop, Kaemawichanurat and Rangarajan. -/
def exampleGraph : SimpleGraph ExampleVertex where
  Adj u v := u.1 ≠ v.1 ∧ (u.1.val / 2 = v.1.val / 2 ∨ u.2 = 0 ∧ v.2 = 0)
  symm := fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.elim (fun e => Or.inl e.symm)
    (fun e => Or.inr ⟨e.2, e.1⟩)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance exampleAdjDecidable : DecidableRel exampleGraph.Adj := fun u v => by
  change Decidable (u.1 ≠ v.1 ∧ (u.1.val / 2 = v.1.val / 2 ∨ u.2 = 0 ∧ v.2 = 0))
  infer_instance

private def partner (i : Fin 4) : Fin 4 := ![1, 0, 3, 2] i

private theorem partner_spec : ∀ i : Fin 4, i ≠ partner i ∧ i.val / 2 = (partner i).val / 2 := by
  decide

private def exampleColor : exampleGraph.Coloring (Fin 4) :=
  SimpleGraph.Coloring.mk Prod.fst (fun h => h.1)

private theorem exampleDominatorColoring : DominatorColoring exampleGraph exampleColor := by
  intro u
  refine ⟨partner u.1, ⟨(partner u.1, 0), rfl⟩, fun v hv => Or.inr ?_⟩
  change v.1 = partner u.1 at hv
  exact ⟨(partner_spec u.1).1.trans_eq hv.symm, Or.inl
    ((partner_spec u.1).2.trans (congrArg (fun i : Fin 4 => i.val / 2) hv.symm))⟩

private theorem exampleNoThreeColors : ¬ exampleGraph.Colorable 3 := by
  rintro ⟨f⟩
  have h : Function.Injective (fun i : Fin 4 => f (i, (0 : Fin 3))) := by
    intro i j h
    by_contra hij
    exact f.valid (show exampleGraph.Adj (i, 0) (j, 0) from ⟨hij, Or.inr ⟨rfl, rfl⟩⟩) h
  have hc := Fintype.card_le_of_injective _ h
  norm_num at hc

private theorem exampleConnected : exampleGraph.Connected := by
  apply (SimpleGraph.connected_iff_exists_forall_reachable (G := exampleGraph)).mpr
  refine ⟨(0, 0), fun v => ?_⟩
  let w : ExampleVertex := (partner v.1, 0)
  have ha : exampleGraph.Adj v w := ⟨(partner_spec v.1).1, Or.inl (partner_spec v.1).2⟩
  have hw : exampleGraph.Reachable (0, 0) w := by
    by_cases h : (0 : Fin 4) = partner v.1
    · have he : ((0, 0) : ExampleVertex) = w := Prod.ext h rfl
      rw [he]
    · exact (show exampleGraph.Adj (0, 0) w from ⟨h, Or.inr ⟨rfl, rfl⟩⟩).reachable
  exact hw.trans ha.reachable.symm

private theorem exampleDominationLe : dominationNumber exampleGraph ≤ 4 := by
  classical
  let cores := (Finset.univ : Finset (Fin 4)).image
    (fun i => ((i, 0) : ExampleVertex))
  have hc : cores.card ≤ 4 := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := (Finset.univ : Finset (Fin 4)))
        (f := fun i => ((i, 0) : ExampleVertex)))
  apply le_trans (dominationNumber_le exampleGraph ?_) hc
  intro v
  refine ⟨(partner v.1, 0), Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩, Or.inr ?_⟩
  exact ⟨(partner_spec v.1).1.symm, Or.inl (partner_spec v.1).2.symm⟩

private instance {u v : ExampleVertex} : Decidable (Closed exampleGraph u v) :=
  inferInstanceAs (Decidable (u = v ∨ exampleGraph.Adj u v))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem exampleNoDominatingTriple : NoDominatingTriple exampleGraph := by
  have h : ∀ a b c : ExampleVertex, ¬ ∀ v,
      Closed exampleGraph a v ∨ Closed exampleGraph b v ∨ Closed exampleGraph c v := by decide
  exact h

theorem exists_order_twelve :
    ∃ G : SimpleGraph ExampleVertex, G.Connected ∧ Fintype.card ExampleVertex = 12 ∧
      dominationNumber G = 4 ∧ G.chromaticNumber = 4 ∧ dominatorChromaticNumber G = 4 := by
  refine ⟨exampleGraph, exampleConnected, by simp [ExampleVertex],
    le_antisymm exampleDominationLe (four_le_of_noDominatingTriple _ exampleNoDominatingTriple),
    ?_, ?_⟩
  · exact (SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable (n := 3)).mpr
      ⟨⟨exampleColor⟩, exampleNoThreeColors⟩
  · apply le_antisymm (dominatorChromaticNumber_le _ ⟨exampleColor, exampleDominatorColoring⟩)
    by_contra! h
    have h3 : dominatorChromaticNumber exampleGraph ≤ 3 := by omega
    obtain ⟨c, _⟩ := Nat.find_spec (coloring_feasible exampleGraph)
    apply exampleNoThreeColors (SimpleGraph.Colorable.mono h3 ⟨c⟩)

end PublishedConstruction

#print axioms order_ge_twelve
#print axioms exists_order_twelve

end DominatorFour
