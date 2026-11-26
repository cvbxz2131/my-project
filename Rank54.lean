import Std

/-!
AutoGraphForge, audit ranks 54 and 55 (equivalent statements).
Source: https://github.com/JanPastorek/AutoGraphForge/blob/4d1a8afc99447cacd2328cca20e47b6493e8dbc5/2026_ITAT_paper/tab_audit.tex#L59-L60
Rohan Arun previously refuted the same conjecture with a 16-vertex tree
and established unboundedness at burning number three (November 2026):
https://doi.org/10.5281/zenodo.24383172
This file formalizes a related family with a 15-vertex witness.
Proposed: every nontrivial connected simple graph satisfies γP + 5 ≤ 3b.
Construct a star on k base vertices and attach two private leaves to each base.
For k ≥ 2 this graph has power domination number k and burning number 3.
Only Lean's standard library is used.
-/

set_option autoImplicit false
namespace Rank54
variable {V : Type}

/-- A vertex is power-observed if it is in the closed neighborhood of the
initial seeds, or an observed neighbor can force it as its last unseen neighbor. -/
inductive Observed (adj : V → V → Prop) (seeds : List V) : V → Prop where
  | seed {v} : v ∈ seeds → Observed adj seeds v
  | neighbor {u v} : u ∈ seeds → adj u v → Observed adj seeds v
  | force {u v} : Observed adj seeds u → adj u v →
      (∀ w, adj u w → w ≠ v → Observed adj seeds w) → Observed adj seeds v

/-- Ignitions are listed newest first. Every previously burning vertex spreads
fire one edge per round. A new ignition does not spread until the next round. -/
def Burned (adj : V → V → Prop) : List V → V → Prop
  | [], _ => False
  | x :: past, v => v = x ∨ Burned adj past v ∨ ∃ u, Burned adj past u ∧ adj u v

def Legal (adj : V → V → Prop) : List V → Prop
  | [] => True
  | x :: past => Legal adj past ∧ ¬ Burned adj past x

def MinimumLength (P : List V → Prop) (k : Nat) : Prop :=
  (∃ xs, xs.length = k ∧ P xs) ∧ ∀ xs, P xs → k ≤ xs.length

def HasPowerNumber (adj : V → V → Prop) :=
  MinimumLength (fun xs => ∀ v, Observed adj xs v)

def HasBurningNumber (adj : V → V → Prop) :=
  MinimumLength (fun xs => Legal adj xs ∧ ∀ v, Burned adj xs v)

inductive Vertex (k : Nat) where
  | base (i : Fin k)
  | leaf (i : Fin k) (side : Bool)
  deriving DecidableEq

open Vertex
variable {k : Nat}

def owner : Vertex k → Fin k
  | base i | leaf i _ => i

def Adj : Vertex k → Vertex k → Prop
  | base i, base j => i ≠ j ∧ (i.val = 0 ∨ j.val = 0)
  | base i, leaf j _ => i = j
  | leaf i _, base j => i = j
  | leaf _ _, leaf _ _ => False

private theorem leaf_parent {u : Vertex k} {i : Fin k} {s : Bool}
    (h : Adj u (leaf i s)) : u = base i := by
  cases u with
  | base j => exact congrArg base h
  | leaf j t => exact False.elim h

/-- First reaching either private leaf requires a seed in its group.
If it were reached by forcing, its sibling must already have been observed. -/
private theorem seen_leaf_group {xs : List (Vertex k)} {v : Vertex k}
    (h : Observed Adj xs v) (i : Fin k) :
    ∀ s, v = leaf i s → i.val ∈ xs.map (fun x => (owner x).val) := by
  induction h with
  | seed hm =>
    rintro s rfl
    exact List.mem_map_of_mem hm
  | neighbor hm edge =>
    rintro s rfl
    rw [leaf_parent edge] at hm
    exact List.mem_map_of_mem hm
  | @force u v _ edge _ _ ih =>
    rintro s rfl
    have parent := leaf_parent edge
    subst u
    have different : leaf i (!s) ≠ leaf i s := by cases s <;> simp
    exact ih (leaf i (!s)) rfl different (!s) rfl

private theorem count_groups (n : Nat) (xs : List Nat)
    (h : ∀ i < n, i ∈ xs) : n ≤ xs.length := by
  induction n generalizing xs with
  | zero => omega
  | succ n ih =>
    have hn := h n (by omega)
    have shorter := ih (xs.erase n) (by
      intro i hi
      exact (List.mem_erase_of_ne (by omega : i ≠ n)).2 (h i (by omega)))
    have positive : 0 < xs.length := by cases xs <;> simp_all
    rw [List.length_erase_of_mem hn] at shorter
    omega

def bases (k : Nat) : List (Vertex k) := (List.finRange k).map base

theorem power_exact (k : Nat) : HasPowerNumber (@Adj k) k := by
  constructor
  · refine ⟨bases k, by simp [bases], ?_⟩
    have hb (i : Fin k) : base i ∈ bases k := List.mem_map_of_mem (List.mem_finRange i)
    intro v
    cases v with
    | base i => exact .seed (hb i)
    | leaf i s => exact .neighbor (hb i) rfl
  · intro xs observes
    have lower := count_groups k (xs.map (fun x => (owner x).val)) (by
      intro i hi
      let j : Fin k := ⟨i, hi⟩
      exact seen_leaf_group (observes (leaf j false)) j false rfl)
    simpa using lower

private theorem burned_one {adj : V → V → Prop} {a v : V} :
    Burned adj [a] v ↔ v = a := by simp [Burned]

private theorem burned_two {adj : V → V → Prop} {a b v : V} :
    Burned adj [b, a] v ↔ v = b ∨ v = a ∨ adj a v := by simp [Burned]

theorem burning_exact (k : Nat) (hk : 2 ≤ k) : HasBurningNumber (@Adj k) 3 := by
  let z : Fin k := ⟨0, by omega⟩
  let j : Fin k := ⟨1, by omega⟩
  have hjz : j ≠ z := by intro h; have := congrArg Fin.val h; simp [j, z] at this
  constructor
  · refine ⟨[leaf j true, leaf j false, base z], rfl, ?_, ?_⟩
    · simp [Legal, Burned, Adj, Ne.symm hjz]
    · have centersLit (i : Fin k) : Burned Adj [leaf j false, base z] (base i) := by
        apply burned_two.mpr
        by_cases h : i = z
        · exact Or.inr (Or.inl (congrArg base h))
        · exact Or.inr (Or.inr ⟨Ne.symm h, Or.inl rfl⟩)
      intro v
      cases v with
      | base i => exact Or.inr (Or.inl (centersLit i))
      | leaf i s => exact Or.inr (Or.inr ⟨base i, centersLit i, rfl⟩)
  · rintro history ⟨_, covers⟩
    cases history with
    | nil => exact False.elim (covers (base z))
    | cons newest rest =>
      cases rest with
      | nil =>
        have same := (burned_one.mp (covers (leaf z false))).trans
          (burned_one.mp (covers (leaf z true))).symm
        simp at same
      | cons first tail =>
        cases tail with
        | cons _ _ => simp
        | nil =>
          have missed : ∃ i : Fin k, i ≠ owner first := by
            by_cases h : z = owner first
            · exact ⟨j, h ▸ hjz⟩
            · exact ⟨z, h⟩
          obtain ⟨i, hi⟩ := missed
          have mustBeNewest (s : Bool) : leaf i s = newest := by
            rcases burned_two.mp (covers (leaf i s)) with h | h | edge
            · exact h
            · exact False.elim (hi (congrArg owner h))
            · exact False.elim (hi (by rw [leaf_parent edge]; rfl))
          have same := (mustBeNewest false).trans (mustBeNewest true).symm
          simp at same

/- Graph hypotheses of the public conjecture. -/
inductive Reach (adj : V → V → Prop) (a : V) : V → Prop where
  | here : Reach adj a a
  | step {b c} : Reach adj a b → adj b c → Reach adj a c

private theorem joinReach {A : V → V → Prop} {a b c : V}
    (h : Reach A a b) (t : Reach A b c) : Reach A a c := by
  induction t with
  | here => exact h
  | step _ edge ih => exact .step ih edge

theorem adj_symmetric (u v : Vertex k) (h : Adj u v) : Adj v u := by
  cases u <;> cases v <;> simp_all [Adj, or_comm, eq_comm]

theorem adj_loopless (v : Vertex k) : ¬ Adj v v := by cases v <;> simp [Adj]

theorem connected (k : Nat) (hk : 0 < k) (u v : Vertex k) : Reach Adj u v := by
  let z : Fin k := ⟨0, hk⟩
  have toBase (i : Fin k) : Reach Adj (base z) (base i) := by
    by_cases h : z = i
    · exact h ▸ Reach.here
    · exact .step .here ⟨h, Or.inl rfl⟩
  have fromHub (w : Vertex k) : Reach Adj (base z) w := by
    cases w with
    | base i => exact toBase i
    | leaf i s => exact .step (toBase i) rfl
  have reverse {a b : Vertex k} (r : Reach Adj a b) : Reach Adj b a := by
    induction r with
    | here => exact .here
    | step _ edge ih => exact joinReach (.step .here (adj_symmetric _ _ edge)) ih
  exact joinReach (reverse (fromHub u)) (fromHub v)

def vertices (k : Nat) : List (Vertex k) :=
  bases k ++ (List.finRange k).map (fun i => leaf i false) ++
    (List.finRange k).map (fun i => leaf i true)

theorem enumerates (v : Vertex k) : v ∈ vertices k := by
  cases v with
  | base i => simp [vertices, bases, List.mem_finRange]
  | leaf i s => cases s <;> simp [vertices, bases, List.mem_finRange]

/-- The public rank-54 claim, written without subtraction to avoid truncating
natural subtraction. Finite, simple, nontrivial and connected are all explicit. -/
def PublishedBound : Prop :=
  ∀ (V : Type) (A : V → V → Prop),
    (∃ vs : List V, ∀ v, v ∈ vs) → (∀ v, ¬ A v v) →
    (∀ u v, A u v → A v u) → (∀ u v, Reach A u v) → (∃ u v : V, u ≠ v) →
    ∀ p b, HasPowerNumber A p → HasBurningNumber A b → p + 5 ≤ 3 * b

theorem fifteen_vertices : (vertices 5).length = 15 ∧ (vertices 5).Nodup := by decide

theorem family_counterexample (k : Nat) (h : 5 ≤ k) :
    HasPowerNumber (@Adj k) k ∧ HasBurningNumber (@Adj k) 3 ∧ ¬ (k + 5 ≤ 3 * 3) :=
  ⟨power_exact k, burning_exact k (by omega), by omega⟩

/-- Even with burning number fixed at three, the power number has no finite cap. -/
theorem unbounded_at_three (cap : Nat) : ∃ k : Nat,
    HasBurningNumber (@Adj k) 3 ∧ HasPowerNumber (@Adj k) k ∧ cap < k :=
  ⟨cap + 2, burning_exact (cap + 2) (by omega), power_exact (cap + 2), by omega⟩

theorem not_published_bound : ¬ PublishedBound := by
  intro bound
  have bad := bound (Vertex 5) Adj ⟨vertices 5, enumerates⟩ adj_loopless adj_symmetric
    (connected 5 (by decide)) ⟨leaf 0 false, leaf 0 true, by decide⟩
    5 3 (power_exact 5) (burning_exact 5 (by decide))
  omega

#print axioms family_counterexample
#print axioms unbounded_at_three
#print axioms not_published_bound
end Rank54
