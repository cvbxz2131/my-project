import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Tauto
import Std.Tactic.BVDecide

/-!
# Two-domination of toroidal grids

An eligible vertex outside the chosen set must have two distinct chosen
neighbors. Vertex deletion restricts the eligible set, and edge deletion
restricts the adjacency relation.
-/

namespace TorusTwoDomination

open Classical

noncomputable section

section FiniteGraph

variable {V : Type*}

def IsTwoDominating (adj : V → V → Prop) (U D : Finset V) : Prop :=
  D ⊆ U ∧ ∀ v ∈ U, v ∉ D → ∃ a ∈ D, ∃ b ∈ D, a ≠ b ∧ adj v a ∧ adj v b

theorem self_dominates (adj : V → V → Prop) (U : Finset V) :
    IsTwoDominating adj U U :=
  ⟨Finset.Subset.rfl, fun _ hv hn => (hn hv).elim⟩

private theorem feasible (adj : V → V → Prop) (U : Finset V) :
    ∃ k : ℕ, ∃ D : Finset V, D.card = k ∧ IsTwoDominating adj U D :=
  ⟨U.card, U, rfl, self_dominates adj U⟩

def dominationNumber (adj : V → V → Prop) (U : Finset V) : ℕ :=
  Nat.find (feasible adj U)

theorem exists_minimum (adj : V → V → Prop) (U : Finset V) :
    ∃ D : Finset V, D.card = dominationNumber adj U ∧ IsTwoDominating adj U D :=
  Nat.find_spec (feasible adj U)

theorem number_le {adj : V → V → Prop} {U D : Finset V}
    (hD : IsTwoDominating adj U D) : dominationNumber adj U ≤ D.card :=
  Nat.find_min' (feasible adj U) ⟨D, rfl, hD⟩

theorem le_number {adj : V → V → Prop} {U : Finset V} {k : ℕ}
    (h : ∀ D, IsTwoDominating adj U D → k ≤ D.card) : k ≤ dominationNumber adj U := by
  obtain ⟨D, hcard, hD⟩ := exists_minimum adj U
  rw [← hcard]
  exact h D hD

theorem map_dominates {W : Type*}
    {adj : V → V → Prop} {adj' : W → W → Prop} (e : V ≃ W)
    (hAdj : ∀ x y, adj x y ↔ adj' (e x) (e y)) {U D : Finset V}
    (hD : IsTwoDominating adj U D) : IsTwoDominating adj' (U.map e.toEmbedding) (D.map e.toEmbedding) := by
  refine ⟨Finset.map_subset_map.mpr hD.1, ?_⟩
  intro w hw hnot
  obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
  have hnot' : v ∉ D := fun h => hnot (Finset.mem_map.mpr ⟨v, h, rfl⟩)
  obtain ⟨a, ha, b, hb, hab, hva, hvb⟩ := hD.2 v hv hnot'
  exact ⟨e a, Finset.mem_map.mpr ⟨a, ha, rfl⟩,
    e b, Finset.mem_map.mpr ⟨b, hb, rfl⟩, fun h => hab (e.injective h),
    (hAdj v a).mp hva, (hAdj v b).mp hvb⟩

theorem number_congr {W : Type*}
    {adj : V → V → Prop} {adj' : W → W → Prop}
    (U : Finset V) (e : V ≃ W) (hAdj : ∀ x y, adj x y ↔ adj' (e x) (e y)) :
    dominationNumber adj' (U.map e.toEmbedding) = dominationNumber adj U := by
  apply le_antisymm
  · obtain ⟨D, hcard, hD⟩ := exists_minimum adj U
    have h := number_le (map_dominates e hAdj hD)
    simpa only [Finset.card_map, hcard] using h
  · obtain ⟨D, hcard, hD⟩ := exists_minimum adj' (U.map e.toEmbedding)
    have hm := map_dominates e.symm (fun x y => by simpa using (hAdj (e.symm x) (e.symm y)).symm) hD
    have hU : (U.map e.toEmbedding).map e.symm.toEmbedding = U := by
      ext x
      simp
    rw [hU] at hm
    simpa only [Finset.card_map, hcard] using number_le hm

variable [DecidableEq V]

/-- A chosen set avoiding the deleted vertex still dominates after deletion. -/
theorem dominates_erase {adj : V → V → Prop} {U D : Finset V} {v : V}
    (hD : IsTwoDominating adj U D) (hv : v ∉ D) :
    IsTwoDominating adj (U.erase v) D := by
  refine ⟨fun x hx => Finset.mem_erase.mpr ⟨fun h => hv (h ▸ hx), hD.1 hx⟩, ?_⟩
  intro x hx
  exact hD.2 x (Finset.mem_of_mem_erase hx)

/-- Inserting the deleted vertex gives a dominating set in the original graph. -/
theorem dominates_insert {adj : V → V → Prop} {U D : Finset V} {v : V}
    (hv : v ∈ U) (hD : IsTwoDominating adj (U.erase v) D) :
    IsTwoDominating adj U (insert v D) := by
  refine ⟨Finset.insert_subset_iff.mpr ⟨hv, fun _ hx => Finset.mem_of_mem_erase (hD.1 hx)⟩, ?_⟩
  intro x hx hn
  have hne : x ≠ v := fun h => hn (h.symm ▸ Finset.mem_insert_self v D)
  obtain ⟨a, ha, b, hb, hab, hxa, hxb⟩ :=
    hD.2 x (Finset.mem_erase.mpr ⟨hne, hx⟩) (fun h => hn (Finset.mem_insert_of_mem h))
  exact ⟨a, Finset.mem_insert_of_mem ha, b, Finset.mem_insert_of_mem hb, hab, hxa, hxb⟩

/-- Move an omitted vertex of a minimum set to a prescribed vertex. -/
theorem minimum_omits_of_transitive {adj : V → V → Prop} {U : Finset V} {v : V}
    (hv : v ∈ U) (hproper : IsTwoDominating adj U (U.erase v))
    (hmove : ∀ x ∈ U, ∃ e : V ≃ V, e x = v ∧ U.map e.toEmbedding = U ∧
      ∀ a b, adj a b ↔ adj (e a) (e b)) :
    ∃ D : Finset V, D.card = dominationNumber adj U ∧ IsTwoDominating adj U D ∧ v ∉ D := by
  obtain ⟨D, hcard, hD⟩ := exists_minimum adj U
  have hlt : D.card < U.card := (hcard.trans_le (number_le hproper)).trans_lt
    (Finset.card_lt_card (Finset.erase_ssubset hv))
  obtain ⟨x, hx, hxD⟩ : ∃ x ∈ U, x ∉ D := by
    by_contra! h
    exact (not_lt_of_ge (Finset.card_le_card (fun z hz => h z hz))) hlt
  obtain ⟨e, hxe, hU, hAdj⟩ := hmove x hx
  have hmap := map_dominates e hAdj hD
  rw [hU] at hmap
  refine ⟨D.map e.toEmbedding, by rw [Finset.card_map, hcard], hmap, ?_⟩
  intro hbad
  obtain ⟨y, hy, hye⟩ := Finset.mem_map.mp hbad
  exact hxD (e.injective (hye.trans hxe.symm) ▸ hy)

/-- Deleting edges incident to a vertex omitted by a minimum set can
raise the two-domination number by at most one. -/
theorem star_bounds_of_minimum {adj adj' : V → V → Prop} {U D : Finset V} {v : V}
    (hv : v ∈ U) (hD : IsTwoDominating adj U D)
    (hmin : D.card = dominationNumber adj U) (hnot : v ∉ D)
    (hsub : ∀ x y, adj' x y → adj x y)
    (hkeep : ∀ x y, x ≠ v → y ≠ v → adj x y → adj' x y) :
    dominationNumber adj U ≤ dominationNumber adj' U ∧
      dominationNumber adj' U ≤ dominationNumber adj U + 1 := by
  constructor
  · apply le_number
    intro S hS
    apply number_le (D := S)
    refine ⟨hS.1, ?_⟩
    intro x hx hn
    obtain ⟨a, ha, b, hb, hab, hxa, hxb⟩ := hS.2 x hx hn
    exact ⟨a, ha, b, hb, hab, hsub _ _ hxa, hsub _ _ hxb⟩
  · have hi : IsTwoDominating adj' U (insert v D) := by
      refine ⟨Finset.insert_subset_iff.mpr ⟨hv, hD.1⟩, ?_⟩
      intro x hx hn
      have hxv : x ≠ v := fun he => hn (he.symm ▸ Finset.mem_insert_self v D)
      obtain ⟨a, ha, b, hb, hab, hxa, hxb⟩ :=
        hD.2 x hx (fun h => hn (Finset.mem_insert_of_mem h))
      have hav : a ≠ v := fun he => hnot (he ▸ ha)
      have hbv : b ≠ v := fun he => hnot (he ▸ hb)
      exact ⟨a, Finset.mem_insert_of_mem ha, b, Finset.mem_insert_of_mem hb,
        hab, hkeep _ _ hxv hav hxa, hkeep _ _ hxv hbv hxb⟩
    simpa [Finset.card_insert_of_notMem hnot, hmin] using number_le hi

end FiniteGraph

abbrev Vertex (m n : ℕ) := Fin m × Fin n

section Torus

variable {m n : ℕ} [NeZero m] [NeZero n]

def offset (i : Fin 4) : Vertex m n := ![(1, 0), (-1, 0), (0, 1), (0, -1)] i

def neighbor (v : Vertex m n) (i : Fin 4) : Vertex m n := v + offset i

def Adj (v w : Vertex m n) : Prop := ∃ i : Fin 4, neighbor v i = w

def domain (v : Option (Vertex m n)) : Finset (Vertex m n) :=
  match v with
  | none => Finset.univ
  | some u => Finset.univ.erase u

def number (v : Option (Vertex m n)) : ℕ := dominationNumber Adj (domain v)

def translate (d : Vertex m n) : Vertex m n ≃ Vertex m n where
  toFun x := x + d
  invFun x := x - d
  left_inv x := add_sub_cancel_right x d
  right_inv x := sub_add_cancel x d

theorem adj_translate (d : Vertex m n) (x y : Vertex m n) :
    Adj x y ↔ Adj (translate d x) (translate d y) := by
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by simpa [translate, neighbor, add_right_comm] using congrArg (· + d) hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i, add_right_cancel (by simpa [translate, neighbor, add_right_comm] using hi)⟩

theorem map_domain (d : Vertex m n) (v : Option (Vertex m n)) :
    (domain v).map (translate d).toEmbedding = domain (v.map (translate d)) := by
  cases v <;> ext z <;> simp [domain]

theorem delete_value (v : Vertex m n) : number (some v) = number (some (0 : Vertex m n)) := by
  have h := number_congr (domain (some v)) (translate (-v)) (adj_translate (-v))
  rw [map_domain] at h
  simpa [number, translate] using h.symm

theorem offset_injective (hm : 3 ≤ m) (hn : 3 ≤ n) :
    Function.Injective (offset (m := m) (n := n)) := by
  have hm1 : (1 : Fin m) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (show 1 < m by omega)] at h'
  have hn1 : (1 : Fin n) ≠ 0 := by
    intro h
    have h' := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (show 1 < n by omega)] at h'
  have hm2 : (1 : Fin m) ≠ -1 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_neg'] at h'
    change 1 % m = (m - 1 % m) % m at h'
    rw [Nat.mod_eq_of_lt (show 1 < m by omega), Nat.mod_eq_of_lt (show m - 1 < m by omega)] at h'
    omega
  have hn2 : (1 : Fin n) ≠ -1 := by
    intro h
    have h' := congrArg Fin.val h
    rw [Fin.val_neg'] at h'
    change 1 % n = (n - 1 % n) % n at h'
    rw [Nat.mod_eq_of_lt (show 1 < n by omega), Nat.mod_eq_of_lt (show n - 1 < n by omega)] at h'
    omega
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [offset, Prod.mk.injEq, eq_comm]

theorem neighbor_injective (hm : 3 ≤ m) (hn : 3 ≤ n) (v : Vertex m n) :
    Function.Injective (neighbor v) := fun _ _ h => offset_injective hm hn (add_left_cancel h)

theorem min_omits (hm : 3 ≤ m) (hn : 3 ≤ n) (v : Vertex m n) :
    ∃ D : Finset (Vertex m n), D.card = number (none : Option (Vertex m n)) ∧
      IsTwoDominating Adj (domain none) D ∧ v ∉ D := by
  let U : Finset (Vertex m n) := Finset.univ
  have hv : v ∈ U := Finset.mem_univ _
  have hd : IsTwoDominating Adj U (U.erase v) := by
    refine ⟨Finset.erase_subset _ _, ?_⟩
    intro z hz hnD
    have he : z = v := by
      by_contra hh
      exact hnD (Finset.mem_erase.mpr ⟨hh, hz⟩)
    subst z
    have h1 : neighbor v 0 ≠ v := by
      intro h
      have h' : offset (m := m) (n := n) 0 = 0 := add_left_cancel (h.trans (add_zero v).symm)
      have hc := congrArg (fun q : Vertex m n => q.1.val) h'
      simp [offset, Nat.mod_eq_of_lt (show 1 < m by omega)] at hc
    have h2 : neighbor v 2 ≠ v := by
      intro h
      have h' : offset (m := m) (n := n) 2 = 0 := add_left_cancel (h.trans (add_zero v).symm)
      have hc := congrArg (fun q : Vertex m n => q.2.val) h'
      simp [offset, Nat.mod_eq_of_lt (show 1 < n by omega)] at hc
    exact ⟨neighbor v 0, Finset.mem_erase.mpr ⟨h1, Finset.mem_univ _⟩,
      neighbor v 2, Finset.mem_erase.mpr ⟨h2, Finset.mem_univ _⟩,
      fun hh => (by decide : (0 : Fin 4) ≠ 2) (neighbor_injective hm hn v hh),
      ⟨0, rfl⟩, ⟨2, rfl⟩⟩
  apply minimum_omits_of_transitive hv hd
  intro x _
  let e : Vertex m n ≃ Vertex m n := translate (v - x)
  refine ⟨e, by simp [e, translate, add_sub_cancel], ?_, adj_translate (v - x)⟩
  ext z
  simp [U]

theorem deletion_le (hm : 3 ≤ m) (hn : 3 ≤ n) (v : Vertex m n) :
    number (some v) ≤ number (none : Option (Vertex m n)) := by
  obtain ⟨D, hc, hd, hnD⟩ := min_omits hm hn v
  exact hc ▸ number_le (dominates_erase hd hnD)

theorem star_deletion_bound (hm : 3 ≤ m) (hn : 3 ≤ n) (v : Vertex m n)
    (R : Vertex m n → Vertex m n → Prop)
    (hR : ∀ x y, R x y → x = v ∨ y = v) :
    number (none : Option (Vertex m n)) ≤
      dominationNumber (fun x y => Adj x y ∧ ¬ R x y) (domain none) ∧
    dominationNumber (fun x y => Adj x y ∧ ¬ R x y) (domain none) ≤
      number (none : Option (Vertex m n)) + 1 := by
  obtain ⟨D, hmin, hd, hv⟩ := min_omits hm hn v
  exact star_bounds_of_minimum (v := v) (Finset.mem_univ _) hd hmin hv
    (fun _ _ h => h.1)
    (fun _ _ hx hy h => ⟨h, fun h' => (hR _ _ h').elim hx hy⟩)

end Torus

section Certificates

variable {m n : ℕ}

/-- Vertex (a,b) is recorded at bit a*n+b. -/
def rank (v : Vertex m n) : ℕ := (finProdFinEquiv v).val

def fromBits (x : BitVec (m * n)) : Finset (Vertex m n) :=
  (Finset.univ.filter fun i : Fin (m * n) => x.getLsbD i = true).map
    finProdFinEquiv.symm.toEmbedding

def encode (D : Finset (Vertex m n)) : BitVec (m * n) :=
  (BitVec.ofBoolListLE (List.ofFn fun i => decide (finProdFinEquiv.symm i ∈ D))).cast
    (by simp)

@[simp] theorem mem_fromBits (x : BitVec (m * n)) (v : Vertex m n) :
    v ∈ fromBits x ↔ x.getLsbD (rank v) = true := by
  constructor
  · intro hv
    obtain ⟨i, hi, hv⟩ := Finset.mem_map.mp hv
    change finProdFinEquiv.symm i = v at hv
    subst v
    simpa only [rank, Equiv.apply_symm_apply] using (Finset.mem_filter.mp hi).2
  · intro hv
    exact Finset.mem_map.mpr ⟨finProdFinEquiv v, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hv⟩, finProdFinEquiv.symm_apply_apply v⟩

theorem fromBits_encode (D : Finset (Vertex m n)) : fromBits (encode D) = D := by
  ext v
  simp only [mem_fromBits, encode, rank, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, dif_pos (finProdFinEquiv v).isLt,
    Option.getD_some, decide_eq_true_eq]
  change finProdFinEquiv.symm (finProdFinEquiv v) ∈ D ↔ v ∈ D
  rw [Equiv.symm_apply_apply]

def twoFlags (p : Fin 4 → Bool) : Bool :=
  (p 0 && p 1) || (p 0 && p 2) || (p 0 && p 3) ||
  (p 1 && p 2) || (p 1 && p 3) || (p 2 && p 3)

private theorem twoFlags_iff (p : Fin 4 → Bool) :
    twoFlags p = true ↔ ∃ i j, i ≠ j ∧ p i = true ∧ p j = true := by
  have h : ∀ q : Fin 4 → Bool, twoFlags q = true ↔
      ∃ i j, i ≠ j ∧ q i = true ∧ q j = true := by decide
  exact h p

variable [NeZero m] [NeZero n]

def okAt (hole : Option (Vertex m n)) (keep : Vertex m n → Vertex m n → Bool)
    (x : BitVec (m * n)) (v : Vertex m n) : Bool :=
  if hole = some v then !x.getLsbD (rank v)
  else x.getLsbD (rank v) ||
    twoFlags (fun i => keep v (neighbor v i) && x.getLsbD (rank (neighbor v i)))

def maskOK (hole : Option (Vertex m n)) (keep : Vertex m n → Vertex m n → Bool)
    (x : BitVec (m * n)) : Bool :=
  (List.ofFn (fun i : Fin (m * n) => finProdFinEquiv.symm i)).all (okAt hole keep x)

omit [NeZero m] [NeZero n] in
private theorem mem_domain_iff (hole : Option (Vertex m n)) (v : Vertex m n) :
    v ∈ domain hole ↔ hole ≠ some v := by
  cases hole <;> simp [domain, eq_comm]

theorem maskOK_iff (hm : 3 ≤ m) (hn : 3 ≤ n) (hole : Option (Vertex m n))
    (keep : Vertex m n → Vertex m n → Bool) (x : BitVec (m * n)) :
    maskOK hole keep x = true ↔
      IsTwoDominating (fun v w => Adj v w ∧ keep v w = true) (domain hole) (fromBits x) := by
  have hall (v : Vertex m n) :
      v ∈ List.ofFn (fun i : Fin (m * n) => finProdFinEquiv.symm i) :=
    List.mem_ofFn.mpr ⟨finProdFinEquiv v, finProdFinEquiv.symm_apply_apply v⟩
  constructor
  · intro h
    have hcheck (v : Vertex m n) : okAt hole keep x v = true := List.all_eq_true.mp h v (hall v)
    refine ⟨?_, ?_⟩
    · intro v hv
      rw [mem_domain_iff]
      intro hd
      have hbad := hcheck v
      simp [okAt, hd, (mem_fromBits x v).mp hv] at hbad
    · intro v hv hnv
      have hd := (mem_domain_iff _ _).mp hv
      have hfalse : x.getLsbD (rank v) = false := Bool.eq_false_iff.mpr (mt (mem_fromBits _ _).mpr hnv)
      have ht : twoFlags (fun i => keep v (neighbor v i) && x.getLsbD (rank (neighbor v i))) = true := by
        simpa [okAt, hd, hfalse] using hcheck v
      obtain ⟨i, j, hij, hi, hj⟩ := (twoFlags_iff _).mp ht
      obtain ⟨hki, hxi⟩ := Bool.and_eq_true_iff.mp hi
      obtain ⟨hkj, hxj⟩ := Bool.and_eq_true_iff.mp hj
      exact ⟨neighbor v i, (mem_fromBits _ _).mpr hxi, neighbor v j, (mem_fromBits _ _).mpr hxj,
        fun he => hij (neighbor_injective hm hn v he), ⟨⟨i, rfl⟩, hki⟩, ⟨⟨j, rfl⟩, hkj⟩⟩
  · intro h
    apply List.all_eq_true.mpr
    intro v _
    by_cases hd : hole = some v
    · have hv : v ∉ fromBits x := fun hh => (mem_domain_iff _ _).mp (h.1 hh) hd
      have hfalse : x.getLsbD (rank v) = false := Bool.eq_false_iff.mpr (mt (mem_fromBits _ _).mpr hv)
      simp [okAt, hd, hfalse]
    · by_cases hv : v ∈ fromBits x
      · simp [okAt, hd, (mem_fromBits _ _).mp hv]
      · obtain ⟨a, ha, b, hb, hab, ⟨⟨i, hi⟩, hki⟩, ⟨⟨j, hj⟩, hkj⟩⟩ :=
          h.2 v ((mem_domain_iff _ _).mpr hd) hv
        subst a
        subst b
        have ht := (twoFlags_iff (fun l => keep v (neighbor v l) &&
          x.getLsbD (rank (neighbor v l)))).mpr
          ⟨i, j, fun he => hab (congrArg (neighbor v) he),
            Bool.and_eq_true_iff.mpr ⟨hki, (mem_fromBits _ _).mp ha⟩,
            Bool.and_eq_true_iff.mpr ⟨hkj, (mem_fromBits _ _).mp hb⟩⟩
        simp [okAt, hd, ht]

end Certificates

private def countNat (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (f k).toNat + countNat f k

private theorem countNat_le (f : ℕ → Bool) (k : ℕ) : countNat f k ≤ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [countNat]
    exact Nat.add_comm 1 k ▸ Nat.add_le_add (Bool.toNat_le _) ih

private def weightBits (x : BitVec w) : ℕ → BitVec w
  | 0 => 0
  | k + 1 => (if x.getLsbD k then 1 else 0) + weightBits x k

private theorem weightBits_toNat (x : BitVec w) (k : ℕ) (hk : k ≤ w) :
    (weightBits x k).toNat = countNat x.getLsbD k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hb : (if x.getLsbD k then (1 : BitVec w) else 0).toNat =
        (x.getLsbD k).toNat := by
      cases h : x.getLsbD k
      · rfl
      · change 1 % 2 ^ w = 1
        exact Nat.mod_eq_of_lt (lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := w)))
    rw [weightBits, BitVec.toNat_add, hb, ih (by omega)]
    change countNat x.getLsbD (k + 1) % 2 ^ w = countNat x.getLsbD (k + 1)
    exact Nat.mod_eq_of_lt ((countNat_le _ _).trans_lt (hk.trans_lt Nat.lt_two_pow_self))

private theorem card_filter_bits (f : ℕ → Bool) (k : ℕ) :
    (Finset.univ.filter fun i : Fin k => f i = true).card = countNat f k := by
  have hc : (Finset.univ.filter fun i : Fin k => f i = true).card =
      ∑ i : Fin k, (if f i = true then 1 else 0 : ℕ) :=
    Finset.natCast_card_filter (R := ℕ) (fun i : Fin k => f i = true) Finset.univ
  rw [hc]
  clear hc
  have hbit (i : ℕ) : (if f i = true then 1 else 0 : ℕ) = (f i).toNat := by
    cases f i <;> rfl
  simp_rw [hbit]
  induction k with
  | zero => simp [countNat]
  | succ k ih =>
    simp only [Fin.sum_univ_castSucc, Fin.val_castSucc, Fin.val_last, countNat, ih, Nat.add_comm]

theorem card_fromBits (x : BitVec (m * n)) :
    (fromBits x).card = (weightBits x (m * n)).toNat := by
  rw [fromBits, Finset.card_map, card_filter_bits, weightBits_toNat _ _ le_rfl]

section Bounds

variable {m n : ℕ} [NeZero m] [NeZero n]

private theorem lower_of_mask (hm : 3 ≤ m) (hn : 3 ≤ n) (hole : Option (Vertex m n))
    (keep : Vertex m n → Vertex m n → Bool) {k : ℕ} (hk : k < 2 ^ (m * n))
    (h : ∀ x, maskOK hole keep x = true → BitVec.ofNat (m * n) k ≤ weightBits x (m * n)) :
    k ≤ dominationNumber (fun v w => Adj v w ∧ keep v w = true) (domain hole) := by
  apply le_number
  intro D hD
  have hOK : maskOK hole keep (encode D) = true :=
    (maskOK_iff hm hn hole keep _).mpr (by simpa only [fromBits_encode] using hD)
  have hb := BitVec.le_def.mp (h _ hOK)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk, ← card_fromBits, fromBits_encode] at hb
  exact hb

private theorem upper_of_mask (hm : 3 ≤ m) (hn : 3 ≤ n) (hole : Option (Vertex m n))
    (keep : Vertex m n → Vertex m n → Bool) (x : BitVec (m * n)) {k : ℕ}
    (h : maskOK hole keep x = true) (hc : (weightBits x (m * n)).toNat = k) :
    dominationNumber (fun v w => Adj v w ∧ keep v w = true) (domain hole) ≤ k := by
  have hb := number_le ((maskOK_iff hm hn hole keep x).mp h)
  rwa [card_fromBits, hc] at hb

end Bounds

@[local simp] private theorem zero_vertex {m n : ℕ} [NeZero m] [NeZero n] :
    (0 : Vertex m n) = (0, 0) := rfl

attribute [local simp] Fin.ext_iff

local macro "verify_mask_bound" loc:Lean.Parser.Tactic.location : tactic =>
  `(tactic| (
    simp [maskOK, List.ofFn_succ, List.ofFn_zero, okAt, twoFlags, rank, neighbor,
      offset, finProdFinEquiv, Fin.divNat, Fin.modNat, Fin.val_add, Fin.val_neg'] $loc
    simp only [weightBits]
    bv_decide))

private theorem four_seven_bits (x : BitVec 28)
    (h : maskOK (none : Option (Vertex 4 7)) (fun _ _ => true) x = true) :
    (12 : BitVec 28) ≤ weightBits x 28 := by
  verify_mask_bound at h

private theorem number_le_punctured_add_one {m n : ℕ} [NeZero m] [NeZero n] (v : Vertex m n) :
    number (none : Option (Vertex m n)) ≤ number (some v) + 1 := by
  obtain ⟨D, hcard, hD⟩ := exists_minimum Adj (domain (some v))
  have h := number_le (dominates_insert (Finset.mem_univ v) hD)
  exact h.trans ((Finset.card_insert_le v D).trans_eq (congrArg (· + 1) hcard))

/-- The 28-vertex counterexample to Chen and Zhang's Problem 1. -/
theorem four_seven_counterexample :
    number (none : Option (Vertex 4 7)) = 12 ∧ ∀ v : Vertex 4 7, number (some v) = 11 := by
  have lower : 12 ≤ number (none : Option (Vertex 4 7)) := by
    simpa [number] using lower_of_mask (by decide) (by decide) (none : Option (Vertex 4 7))
      (fun _ _ => true) (k := 12) (by decide) four_seven_bits
  have upper : number (some (0 : Vertex 4 7)) ≤ 11 := by
    simpa [number] using upper_of_mask (by decide) (by decide) (some (0 : Vertex 4 7))
      (fun _ _ => true) 45393188 (k := 11) (by decide) (by decide)
  have step := number_le_punctured_add_one (0 : Vertex 4 7)
  refine ⟨by omega, fun v => ?_⟩
  rw [delete_value]
  omega

/-- Single-vertex deletion preserves two-domination. -/
def Stable (m n : ℕ) [NeZero m] [NeZero n] : Prop :=
  ∀ v : Vertex m n, number (some v) = number (none : Option (Vertex m n))

section SmallTori

variable {m n : ℕ} [NeZero m] [NeZero n]

private theorem values_of_certificates (hm : 3 ≤ m) (hn : 3 ≤ n)
    (x : BitVec (m * n)) {k : ℕ} (hk : k < 2 ^ (m * n))
    (hOK : maskOK (none : Option (Vertex m n)) (fun _ _ => true) x = true)
    (hcard : (weightBits x (m * n)).toNat = k)
    (hLower : ∀ y, maskOK (some (0 : Vertex m n)) (fun _ _ => true) y = true →
      BitVec.ofNat (m * n) k ≤ weightBits y (m * n)) :
    number (none : Option (Vertex m n)) = k ∧ ∀ v : Vertex m n, number (some v) = k := by
  have hupper : number (none : Option (Vertex m n)) ≤ k := by
    simpa [number] using upper_of_mask hm hn none (fun _ _ => true) x hOK hcard
  have hlower : k ≤ number (some (0 : Vertex m n)) := by
    simpa [number] using lower_of_mask hm hn (some (0 : Vertex m n)) (fun _ _ => true) hk hLower
  have hd := deletion_le hm hn (0 : Vertex m n)
  refine ⟨by omega, fun v => ?_⟩
  rw [delete_value]
  omega

private theorem stable_of_values {k : ℕ}
    (h : number (none : Option (Vertex m n)) = k ∧ ∀ v : Vertex m n, number (some v) = k) :
    Stable m n := fun v => (h.2 v).trans h.1.symm

local macro "verify_small_values" k:term:max x:term:max w:term:max : tactic =>
  `(tactic| (
    refine values_of_certificates (by decide) (by decide) $x (k := $k)
      (by decide) (by decide) (by decide) ?_
    intro y hy
    change BitVec $w at y
    change ($k : BitVec $w) ≤ weightBits y $w
    verify_mask_bound at hy))

private theorem stable_three_three : Stable 3 3 := by
  apply stable_of_values
  verify_small_values 3 84 9

private theorem stable_three_four : Stable 3 4 := by
  apply stable_of_values
  verify_small_values 5 364 12

private theorem stable_three_five : Stable 3 5 := by
  apply stable_of_values
  verify_small_values 6 5426 15

private theorem three_six_values :
    number (none : Option (Vertex 3 6)) = 6 ∧ ∀ v : Vertex 3 6, number (some v) = 6 := by
  verify_small_values 6 38052 18

private theorem stable_three_six : Stable 3 6 :=
  stable_of_values three_six_values

private theorem stable_three_seven : Stable 3 7 := by
  apply stable_of_values
  verify_small_values 8 153956 21

private theorem stable_three_eight : Stable 3 8 := by
  apply stable_of_values
  verify_small_values 9 2443666 24

private theorem stable_three_nine : Stable 3 9 := by
  apply stable_of_values
  verify_small_values 9 19211556 27

private theorem stable_four_four : Stable 4 4 := by
  apply stable_of_values
  verify_small_values 7 5406 16

private theorem stable_four_five : Stable 4 5 := by
  apply stable_of_values
  verify_small_values 8 173394 20

private theorem stable_four_six : Stable 4 6 := by
  apply stable_of_values
  verify_small_values 10 1414324 24

private theorem stable_five_five : Stable 5 5 := by
  apply stable_of_values
  verify_small_values 10 3556568 25

private theorem adj_swap_forward (v w : Vertex m n) (h : Adj v w) : Adj v.swap w.swap := by
  obtain ⟨i, rfl⟩ := h
  refine ⟨i + 2, ?_⟩
  fin_cases i <;> rfl

private theorem adj_swap (v w : Vertex m n) : Adj v w ↔ Adj v.swap w.swap :=
  ⟨adj_swap_forward v w, fun h => by simpa only [Prod.swap_swap] using adj_swap_forward _ _ h⟩

private theorem number_swap (hole : Option (Vertex m n)) :
    number (hole.map Prod.swap) = number hole := by
  let e : Vertex m n ≃ Vertex n m := Equiv.prodComm _ _
  have hm : (domain hole).map e.toEmbedding = domain (hole.map Prod.swap) := by
    cases hole <;> ext z <;> simp [domain, e]
  simpa only [number, hm] using number_congr (domain hole) e adj_swap

private theorem stable_swap (h : Stable n m) : Stable m n := by
  intro v
  have hv := h v.swap
  rw [← number_swap (some v), ← number_swap (none : Option (Vertex m n))]
  exact hv

private theorem stable_lt_twenty_eight_sorted (hm : 3 ≤ m) (hn : 3 ≤ n) (hmn : m ≤ n)
    (ha : m * n < 28) : Stable m n := by
  have hm' : m ≤ 5 := by
    by_contra! hh
    have hb := Nat.mul_le_mul hh (show 6 ≤ n by omega)
    omega
  have hn' : n ≤ 9 := by
    by_contra! hh
    have hb := Nat.mul_le_mul hm hh
    omega
  interval_cases m <;> interval_cases n <;>
    first
    | omega
    | exact stable_three_three
    | exact stable_three_four
    | exact stable_three_five
    | exact stable_three_six
    | exact stable_three_seven
    | exact stable_three_eight
    | exact stable_three_nine
    | exact stable_four_four
    | exact stable_four_five
    | exact stable_four_six
    | exact stable_five_five

/-- Every toroidal grid with fewer than 28 vertices is stable. -/
theorem stable_lt_twenty_eight (hm : 3 ≤ m) (hn : 3 ≤ n) (ha : m * n < 28) :
    Stable m n := by
  rcases le_total m n with h | h
  · exact stable_lt_twenty_eight_sorted hm hn h ha
  · exact stable_swap (stable_lt_twenty_eight_sorted hn hm h (by simpa [Nat.mul_comm] using ha))

end SmallTori

theorem four_seven_unstable : ¬ Stable 4 7 := by
  intro h
  have hh := h 0
  rw [four_seven_counterexample.1, four_seven_counterexample.2] at hh
  omega

private abbrev cutStraight (x y : Vertex 3 6) : Prop :=
  (x = 0 ∧ (y = (0, 1) ∨ y = (0, 5))) ∨ (y = 0 ∧ (x = (0, 1) ∨ x = (0, 5)))

private def keepStraight (x y : Vertex 3 6) : Bool := !(decide (cutStraight x y))

attribute [local simp] keepStraight cutStraight

private theorem three_six_cut_bits (x : BitVec 18)
    (h : maskOK (none : Option (Vertex 3 6)) keepStraight x = true) :
    (7 : BitVec 18) ≤ weightBits x 18 := by
  verify_mask_bound at h

/-- Cutting the two edges of the straight path from (0,1) through (0,0)
to (0,5) increases two-domination from six to seven. -/
theorem straight_path_sharp :
    number (none : Option (Vertex 3 6)) = 6 ∧
    dominationNumber (fun x y => Adj x y ∧ ¬ cutStraight x y) (domain none) = 7 := by
  have hcut (x y : Vertex 3 6) (h : cutStraight x y) : x = 0 ∨ y = 0 :=
    h.elim (fun hx => Or.inl hx.1) (fun hy => Or.inr hy.1)
  have hu := (star_deletion_bound (by decide) (by decide) (0 : Vertex 3 6) cutStraight hcut).2
  rw [three_six_values.1] at hu
  have hkeep (x y : Vertex 3 6) : keepStraight x y = true ↔ ¬ cutStraight x y := by
    simp [keepStraight]
    tauto
  have hl : 7 ≤ dominationNumber (fun x y => Adj x y ∧ ¬ cutStraight x y) (domain none) := by
    simpa only [hkeep] using lower_of_mask (by decide) (by decide) (none : Option (Vertex 3 6))
      keepStraight (k := 7) (by decide) three_six_cut_bits
  exact ⟨three_six_values.1, le_antisymm hu hl⟩

#print axioms TorusTwoDomination.four_seven_counterexample
#print axioms TorusTwoDomination.stable_lt_twenty_eight
#print axioms TorusTwoDomination.star_deletion_bound
#print axioms TorusTwoDomination.straight_path_sharp

end
end TorusTwoDomination
