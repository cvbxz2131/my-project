import Std

/-!
The three-event optimization in Dickey and Rosenberg, Conjecture 20(ii).
Source: https://arxiv.org/html/2602.07426v1#Thmtheorem20

For a tree of internal height at most three, each entry in the branch list
counts the internal children of one internal child of the root. Leaves need
no event. A positive entry forces its branch root to time 2 and all the
internal grandchildren to time 3. The global root has time 1. Thus if some
entry is positive, all three times are used automatically.
-/

set_option autoImplicit false
namespace ThreeEvents

/-- The time of each internal child of the root, in branch order. -/
def ValidTimes : List Nat → List Nat → Prop
  | [], [] => True
  | g :: gs, t :: ts => (t = 2 ∨ g = 0 ∧ t = 3) ∧ ValidTimes gs ts
  | _, _ => False

def schedules : List Nat → List (List Nat)
  | [] => [[]]
  | 0 :: gs => (schedules gs).map (2 :: ·) ++ (schedules gs).map (3 :: ·)
  | (_ + 1) :: gs => (schedules gs).map (2 :: ·)

theorem mem_schedules (gs ts : List Nat) :
    ts ∈ schedules gs ↔ ValidTimes gs ts := by
  induction gs generalizing ts with
  | nil => cases ts <;> simp [schedules, ValidTimes]
  | cons g gs ih =>
    cases g <;> cases ts <;> simp [schedules, ValidTimes, ih, or_and_right] <;> grind

theorem schedules_nodup (gs : List Nat) : (schedules gs).Nodup := by
  have prepend (t : Nat) (xs : List (List Nat)) (h : xs.Nodup) :
      (xs.map (t :: ·)).Nodup := by
    simpa [List.Nodup, List.pairwise_map] using h
  induction gs with
  | nil => simp [schedules]
  | cons g gs ih =>
    cases g with
    | zero =>
      refine List.nodup_append.mpr ⟨prepend 2 _ ih, prepend 3 _ ih, ?_⟩
      intro a ha b hb
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp ha
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hb
      simp
    | succ g => exact prepend 2 _ ih

theorem schedules_length (gs : List Nat) :
    (schedules gs).length = 2 ^ gs.count 0 := by
  induction gs with
  | nil => simp [schedules]
  | cons g gs ih =>
    cases g <;> simp [schedules, ih, Nat.pow_succ, Nat.mul_two]

/-- The tree has `1 + r + q` internal vertices, with `r` children per
internal vertex when its ordinary leaves are included. -/
def Fits (r q : Nat) (gs : List Nat) : Prop :=
  gs.length ≤ r ∧ (∀ g ∈ gs, g ≤ r) ∧ gs.length + gs.sum = r + q

/-- A positive excess forces a branch that uses all three events. -/
theorem has_internal_grandchild {r q : Nat} {gs : List Nat}
    (hq : 0 < q) (h : Fits r q gs) : ∃ g ∈ gs, 0 < g := by
  rcases h with ⟨hlen, _, hsize⟩
  exact Nat.sum_pos_iff_exists_pos.mp (by omega)

def deepBranches : List Nat → Nat
  | [] => 0
  | 0 :: gs => deepBranches gs
  | (_ + 1) :: gs => deepBranches gs + 1

private theorem count_branches (gs : List Nat) :
    deepBranches gs + gs.count 0 = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases g <;> simp [deepBranches] <;> omega

private theorem grandchildren_bound (r : Nat) (gs : List Nat)
    (h : ∀ g ∈ gs, g ≤ r) : gs.sum ≤ r * deepBranches gs := by
  induction gs with
  | nil => simp [deepBranches]
  | cons g gs ih =>
    have hg := h g (by simp)
    have htail := ih (fun j hj => h j (List.mem_cons_of_mem _ hj))
    cases g with
    | zero => simpa [deepBranches] using htail
    | succ k =>
      simp only [List.sum_cons, deepBranches, Nat.mul_succ]
      omega

/-- For positive `q`, this is the ceiling of `q/r`. -/
def needed (r q : Nat) : Nat := (q - 1) / r + 1

theorem upper_bound {r q : Nat} (hr : 0 < r) (hq : 0 < q) {gs : List Nat}
    (h : Fits r q gs) : (schedules gs).length ≤ 2 ^ (r - needed r q) := by
  rcases h with ⟨hlen, hbranches, hsize⟩
  have hcapacity := grandchildren_bound r gs hbranches
  have hdeep : needed r q ≤ deepBranches gs := by
    unfold needed
    have hmul : q - 1 < deepBranches gs * r := by
      rw [Nat.mul_comm]
      omega
    have hdiv := (Nat.div_lt_iff_lt_mul hr).mpr hmul
    omega
  have hc := count_branches gs
  rw [schedules_length]
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- Fill one branch at a time, with a final positive branch even when it is full. -/
def packed (r q : Nat) : List Nat :=
  List.replicate ((q - 1) / r) r ++
    ([(q - 1) % r + 1] ++ List.replicate (r - needed r q) 0)

theorem achieves_bound {r q : Nat} (hr : 0 < r) (hq : 0 < q) (hmax : q ≤ r * r) :
    Fits r q (packed r q) ∧
      (schedules (packed r q)).length = 2 ^ (r - needed r q) := by
  have ha : (q - 1) / r < r :=
    (Nat.div_lt_iff_lt_mul hr).mpr (by omega)
  have hb : (q - 1) % r < r := Nat.mod_lt _ hr
  have hd : needed r q ≤ r := by unfold needed; omega
  have hlen : (packed r q).length = r := by
    simp [packed]
    unfold needed
    omega
  have hsum : (packed r q).sum = q := by
    have hqr := Nat.div_add_mod' (q - 1) r
    simp [packed]
    omega
  constructor
  · refine ⟨by simp [hlen], ?_, by rw [hlen, hsum]⟩
    intro g hg
    simp only [packed, List.mem_append] at hg
    rcases hg with h | h | h
    · simp [List.eq_of_mem_replicate h]
    · have heq : g = (q - 1) % r + 1 := List.mem_singleton.mp h
      omega
    · rw [List.eq_of_mem_replicate h]
      omega
  · rw [schedules_length]
    have hr0 : r ≠ 0 := by omega
    simp [packed, List.count_replicate, hr0]

theorem optimal_three_events {r q : Nat} (hr : 2 ≤ r) (hq : 0 < q) (hmax : q ≤ r * r) :
    (∃ gs, Fits r q gs ∧ (schedules gs).length = 2 ^ (r - needed r q)) ∧
      ∀ gs, Fits r q gs → (schedules gs).length ≤ 2 ^ (r - needed r q) :=
  ⟨⟨packed r q, achieves_bound (by omega) hq hmax⟩,
    fun _ h => upper_bound (by omega) hq h⟩

#print axioms optimal_three_events
#print axioms mem_schedules
#print axioms schedules_nodup
end ThreeEvents
