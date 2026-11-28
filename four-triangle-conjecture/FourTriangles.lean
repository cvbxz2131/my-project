import Std

/-!
Finite distance-label classification for the seven-point case of Palsson and
Yu's Conjecture 4.1. The Euclidean implications are proved in README.md.
-/

namespace FourTriangles

abbrev Edge := Nat × Nat
abbrev Shape := Nat × Nat × Nat

/-- Lower triangular entries in lexicographic order. -/
def edges (n : Nat) : List Edge :=
  (List.range n).flatMap fun i => (List.range i).map fun j => (i, j)

def label (xs : Array Nat) (i j : Nat) : Nat :=
  let hi := max i j
  xs.getD (hi * (hi - 1) / 2 + min i j) 6

def shape (a b c : Nat) : Shape :=
  let lo := min a (min b c)
  let hi := max a (max b c)
  (lo, a + b + c - lo - hi, hi)

structure Prefix where
  labels : Array Nat
  shapes : List Shape
  used : Nat

def start : Prefix := ⟨#[], [], 0⟩

def addLabel (st : Prefix) (e : Edge) (color : Nat) : Prefix :=
  let newShapes := (List.range e.2).map fun k =>
    shape color (label st.labels e.1 k) (label st.labels e.2 k)
  ⟨st.labels.push color, (newShapes ++ st.shapes).eraseDups, max st.used (color + 1)⟩

def available (st : Prefix) : Nat := min (st.used + 1) 6

def circleBound (xs : Array Nat) (n : Nat) : Bool :=
  (edges n).all fun (a, b) =>
    let others := (List.range n).filter fun k => k != a && k != b
    let radii := others.map fun k => (label xs a k, label xs b k)
    radii.all fun r => decide (radii.count r ≤ 2)

def noEquidistantFour (xs : Array Nat) (n : Nat) : Bool :=
  (edges n).all fun (a, b) =>
    (edges b).all fun (c, d) =>
      let r := label xs a b
      !(label xs a c == r && label xs a d == r &&
        label xs b c == r && label xs b d == r && label xs c d == r)

/-- Test the number of types on each edge insertion and the geometric
    constraints on each completed vertex prefix. -/
def validPrefix (e : Edge) (st : Prefix) : Bool :=
  decide (st.shapes.length ≤ 4) &&
    (if e.2 + 1 == e.1 then
      circleBound st.labels (e.1 + 1) && noEquidistantFour st.labels (e.1 + 1)
    else true)

def incidence (st : Prefix) : Bool :=
  (List.range st.used).all fun c =>
    decide (2 ≤ (st.shapes.filter fun (a,b,d) => a == c || b == c || d == c).length)

def bisectorVertices (xs : Array Nat) (a b : Nat) : List Nat :=
  (List.range 7).filter fun p => p != a && p != b && label xs p a == label xs p b

def doubleBisectorVertices (xs : Array Nat) (a b c d : Nat) : List Nat :=
  (bisectorVertices xs a b).filter fun p =>
    p != c && p != d && label xs p c == label xs p d

def bisectorObstruction (xs : Array Nat) : Bool :=
  (edges 7).any fun (a, b) =>
    let on := bisectorVertices xs a b
    on.any fun c =>
      on.any fun d =>
        decide (c < d) && decide (2 ≤ (doubleBisectorVertices xs a b c d).length)

/-- Try to follow edges of label zero, starting at vertex zero. The generated
    order is checked independently below. -/
def walk (xs : Array Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, prev, curr =>
    let next := ((List.range 7).find? fun p =>
      p != prev && p != curr && label xs curr p == 0).getD curr
    curr :: walk xs fuel curr next

def cycleOrder (xs : Array Nat) : List Nat := walk xs 7 7 0

def isCyclicOrder (xs : Array Nat) (order : List Nat) : Bool :=
  order.length == 7 && decide order.Nodup &&
    order.all (fun i => decide (i < 7)) &&
    [1,2,3].all fun step =>
      let r := label xs (order.getD 0 0) (order.getD step 0)
      (List.range 7).all fun i =>
        label xs (order.getD i 0) (order.getD ((i + step) % 7) 0) == r

def classified (st : Prefix) : Bool :=
  (st.used == 3 && isCyclicOrder st.labels (cycleOrder st.labels)) ||
    (st.used == 4 && bisectorObstruction st.labels)

/-- First-appearance labels are accepted by following a single path. -/
def follow (st : Prefix) : List Edge → List Nat → Option Prefix
  | [], [] => some st
  | e :: es, c :: cs =>
    let next := addLabel st e c
    if decide (c < available st) && validPrefix e next then follow next es cs
    else none
  | _, _ => none

/-- Search every path allowed by the same one-edge transition as follow. -/
def certify (st : Prefix) : List Edge → Bool
  | [] => decide (st.used < 3) || !incidence st || classified st
  | e :: es =>
    (List.range (available st)).all fun c =>
      let next := addLabel st e c
      !validPrefix e next || certify next es

private theorem certify_sound (st : Prefix) (es : List Edge) (cs : List Nat)
    (last : Prefix) (hcheck : certify st es = true) (hpath : follow st es cs = some last) :
    certify last [] = true := by
  induction es generalizing st cs with
  | nil =>
    cases cs <;> simp [follow] at hpath
    subst last
    exact hcheck
  | cons e es ih =>
    cases cs with
    | nil => simp [follow] at hpath
    | cons c cs =>
      simp only [follow] at hpath
      split at hpath
      · rename_i h
        have h' : c < available st ∧ validPrefix e (addLabel st e c) = true := by
          simpa using h
        have hall := List.all_eq_true.mp hcheck c (List.mem_range.mpr h'.1)
        have hnext : certify (addLabel st e c) es = true := by
          simpa [h'.2] using hall
        exact ih _ _ hnext hpath
      · contradiction

private theorem follow_labels (st : Prefix) (es : List Edge) (cs : List Nat)
    (last : Prefix) (hpath : follow st es cs = some last) :
    last.labels.toList = st.labels.toList ++ cs := by
  induction es generalizing st cs with
  | nil =>
    cases cs <;> simp [follow] at hpath
    subst last
    simp
  | cons e es ih =>
    cases cs with
    | nil => simp [follow] at hpath
    | cons c cs =>
      simp only [follow] at hpath
      split at hpath
      · simpa [addLabel, List.append_assoc] using ih _ _ hpath
      · contradiction

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
private theorem checked : certify start (edges 7) = true := by
  native_decide

/-- Every admitted seven-vertex matrix with at least three labels and two
    shape incidences per label is cyclic with three labels or contains the
    bisector obstruction with four labels. -/
theorem finite_classification (xs : List Nat) (last : Prefix)
    (hpath : follow start (edges 7) xs = some last)
    (hmany : 3 ≤ last.used) (hinc : incidence last = true) :
    (last.used = 3 ∧ isCyclicOrder xs.toArray (cycleOrder xs.toArray) = true) ∨
      (last.used = 4 ∧ bisectorObstruction xs.toArray = true) := by
  have h := certify_sound start (edges 7) xs last checked hpath
  have hEq : last.labels = xs.toArray := by
    have heq := follow_labels start (edges 7) xs last hpath
    simpa [start] using congrArg List.toArray heq
  have hn : ¬ last.used < 3 := by omega
  simpa [certify, hn, hinc, classified, hEq] using h


/-- A seven-cycle whose shifts preserve all distance labels. -/
def CyclicOrder (xs : Array Nat) (order : List Nat) : Prop :=
  order.length = 7 ∧ order.Nodup ∧ (∀ p ∈ order, p < 7) ∧
    ∀ step, 1 ≤ step → step ≤ 3 → ∀ i, i < 7 →
      label xs (order.getD i 0) (order.getD ((i + step) % 7) 0) =
        label xs (order.getD 0 0) (order.getD step 0)

theorem cyclicOrder_of_check (xs : Array Nat) (order : List Nat)
    (h : isCyclicOrder xs order = true) : CyclicOrder xs order := by
  simp only [isCyclicOrder, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, and_assoc] at h
  rcases h with ⟨hl, hn, hbound, hs⟩
  refine ⟨hl, hn, fun p hp => of_decide_eq_true (List.all_eq_true.mp hbound p hp), ?_⟩
  intro step lo hi i ih
  have hstep : step ∈ ([1, 2, 3] : List Nat) := by
    have h' : step = 1 ∨ step = 2 ∨ step = 3 := by omega
    simpa using h'
  exact beq_iff_eq.mp (List.all_eq_true.mp (List.all_eq_true.mp hs step hstep)
    i (List.mem_range.mpr ih))

theorem mem_edges {n a b : Nat} : (a,b) ∈ edges n ↔ a < n ∧ b < a := by
  simp [edges, List.mem_flatMap, List.mem_map]

theorem mem_bisectorVertices {xs : Array Nat} {a b p : Nat} :
    p ∈ bisectorVertices xs a b ↔
      p < 7 ∧ p ≠ a ∧ p ≠ b ∧ label xs p a = label xs p b := by
  simp [bisectorVertices, and_assoc]

theorem mem_doubleBisectorVertices {xs : Array Nat} {a b c d p : Nat} :
    p ∈ doubleBisectorVertices xs a b c d ↔
      p ∈ bisectorVertices xs a b ∧ p ≠ c ∧ p ≠ d ∧ label xs p c = label xs p d := by
  simp [doubleBisectorVertices, and_assoc]

/-- An impossible configuration for Euclidean distance labels. Four vertices
    lie on one bisector, and two of them also bisect the same pair on that line. -/
def BisectorConfiguration (xs : Array Nat) : Prop :=
  ∃ a b c d p q : Nat, a < 7 ∧ b < a ∧ c < d ∧
    c ∈ bisectorVertices xs a b ∧ d ∈ bisectorVertices xs a b ∧ p ≠ q ∧
    p ∈ doubleBisectorVertices xs a b c d ∧ q ∈ doubleBisectorVertices xs a b c d

private theorem two_members (ys : List Nat) (hlen : 2 ≤ ys.length) (hn : ys.Nodup) :
    ∃ p q : Nat, p ≠ q ∧ p ∈ ys ∧ q ∈ ys := by
  cases ys with
  | nil => simp at hlen
  | cons p ys =>
    cases ys with
    | nil => simp at hlen
    | cons q ys =>
      refine ⟨p, q, ?_, by simp, by simp⟩
      intro he
      exact (List.nodup_cons.mp hn).1 (by simp [he])

theorem bisectorConfiguration_of_check (xs : Array Nat)
    (h : bisectorObstruction xs = true) : BisectorConfiguration xs := by
  obtain ⟨⟨a,b⟩, hab, hz⟩ := List.any_eq_true.mp h
  obtain ⟨c, hc, hcs⟩ := List.any_eq_true.mp hz
  obtain ⟨d, hd, hds⟩ := List.any_eq_true.mp hcs
  have hcd : c < d ∧ 2 ≤ (doubleBisectorVertices xs a b c d).length := by
    simpa using hds
  have hn : (doubleBisectorVertices xs a b c d).Nodup :=
    List.filter_sublist.nodup (List.filter_sublist.nodup List.nodup_range)
  obtain ⟨p,q,hpq,hp,hq⟩ := two_members _ hcd.2 hn
  obtain ⟨ha, hb⟩ := mem_edges.mp hab
  exact ⟨a,b,c,d,p,q,ha,hb,hcd.1,hc,hd,hpq,hp,hq⟩

/-- For admitted distance matrices avoiding the bisector configuration,
    the only outcome with at least three distances is a cyclic order with
    exactly three distance labels. -/
theorem cyclic_of_no_bisector (xs : List Nat) (last : Prefix)
    (hpath : follow start (edges 7) xs = some last)
    (hmany : 3 ≤ last.used) (hinc : incidence last = true)
    (hplane : ¬ BisectorConfiguration xs.toArray) :
    last.used = 3 ∧ CyclicOrder xs.toArray (cycleOrder xs.toArray) := by
  rcases finite_classification xs last hpath hmany hinc with ⟨hc, hcyclic⟩ | ⟨_, hbad⟩
  · exact ⟨hc, cyclicOrder_of_check _ _ hcyclic⟩
  · exact (hplane (bisectorConfiguration_of_check _ hbad)).elim

#print axioms finite_classification
#print axioms cyclic_of_no_bisector


end FourTriangles

