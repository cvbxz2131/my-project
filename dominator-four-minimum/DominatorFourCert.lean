import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Std.Tactic.BVDecide
import Lean.Elab.Tactic.BVDecide.Frontend.LRAT

/-! Finite certificates for the minimum order of a D(4) graph. -/

namespace DominatorFour

structure Profile where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ

def Profile.size (p : Profile) (i : Fin 4) : ℕ :=
  ![p.a, p.b, p.c, p.d] i

def Profile.offset (p : Profile) (i : Fin 4) : ℕ :=
  ![0, p.a, p.a + p.b, p.a + p.b + p.c] i

def Profile.order (p : Profile) : ℕ :=
  p.a + p.b + p.c + p.d

/-- The edge between i and j occupies bit 11*min(i,j)+max(i,j). -/
def address (i j : ℕ) : ℕ :=
  11 * min i j + max i j

def edge (bits : BitVec 121) (i j : ℕ) : Bool :=
  bits.getLsbD (address i j)

def covers (bits : BitVec 121) (i j : ℕ) : Bool :=
  (i == j) || edge bits i j

def colors : List (Fin 4) := [0, 1, 2, 3]

def indices (p : Profile) (i : Fin 4) : List ℕ :=
  List.range' (p.offset i) (p.size i)

def properBits (p : Profile) (bits : BitVec 121) : Bool :=
  colors.all fun k => (indices p k).all fun i =>
    (indices p k).all fun j => !edge bits i j

def hasStar (p : Profile) (bits : BitVec 121) : Bool :=
  edge bits 0 p.a && edge bits 0 (p.a + p.b) && edge bits 0 (p.a + p.b + p.c)

def dominatorBits (p : Profile) (bits : BitVec 121) : Bool :=
  (List.range p.order).all fun i => colors.any fun k => (indices p k).all (covers bits i)

def triples (n : ℕ) : List (ℕ × ℕ × ℕ) :=
  (List.range n).flatMap fun k =>
    (List.range k).flatMap fun j =>
      (List.range j).map fun i => (i, j, k)

def noTripleBits (p : Profile) (bits : BitVec 121) : Bool :=
  (triples p.order).all fun (i, j, k) =>
    (List.range p.order).any fun v =>
      !(covers bits i v || covers bits j v || covers bits k v)

open Std.Sat

def targetKey (i : ℕ) (k : Fin 4) : ℕ := 121 + 4 * i + k.val

def missedKey (a b c v : ℕ) : ℕ := 165 + 1331 * a + 121 * b + 11 * c + v

def properClauses (p : Profile) : CNF ℕ :=
  colors.flatMap fun k => (indices p k).flatMap fun i =>
    (indices p k).map fun j => [(address i j, false)]

def starClauses (p : Profile) : CNF ℕ :=
  [[(address 0 p.a, true)], [(address 0 (p.a + p.b), true)],
    [(address 0 (p.a + p.b + p.c), true)]]

def colorClauses (p : Profile) : CNF ℕ :=
  (List.range p.order).flatMap fun i =>
    (colors.map fun k => (targetKey i k, true)) ::
    (colors.flatMap fun k => ((indices p k).filter (· != i)).map fun j =>
      [(targetKey i k, false), (address i j, true)])

def tripleClauses (p : Profile) : CNF ℕ :=
  (triples p.order).flatMap fun (a, b, c) =>
    ((List.range p.order).map fun v => (missedKey a b c v, true)) ::
    ((List.range p.order).flatMap fun v =>
      if v = a ∨ v = b ∨ v = c then [[(missedKey a b c v, false)]]
      else [[(missedKey a b c v, false), (address a v, false)],
        [(missedKey a b c v, false), (address b v, false)],
        [(missedKey a b c v, false), (address c v, false)]])

def profileCNF (p : Profile) : CNF ℕ :=
  properClauses p ++ starClauses p ++ colorClauses p ++ tripleClauses p

/-- A valuation of the edge literals and the two kinds of witness literals. -/
def valuation (p : Profile) (bits : BitVec 121) (k : ℕ) : Bool :=
  if k < 121 then bits.getLsbD k
  else if k < 165 then
    let i := (k - 121) / 4
    let color := Fin.ofNat 4 ((k - 121) % 4)
    (indices p color).all (covers bits i)
  else
    let z := k - 165
    let v := z % 11
    !(covers bits (z / 1331) v || covers bits (z / 121 % 11) v ||
      covers bits (z / 11 % 11) v)

private theorem val_edge {p : Profile} {bits : BitVec 121} {i j : ℕ}
    (hi : i < 11) (hj : j < 11) :
    valuation p bits (address i j) = edge bits i j := by
  have ha : address i j < 121 := by unfold address; omega
  simp only [valuation, if_pos ha, edge]

private theorem val_target {p : Profile} {bits : BitVec 121} {i : ℕ}
    (hi : i < 11) (k : Fin 4) :
    valuation p bits (targetKey i k) = (indices p k).all (covers bits i) := by
  have hk := k.isLt
  have ha : ¬ targetKey i k < 121 := by unfold targetKey; omega
  have hb : targetKey i k < 165 := by unfold targetKey; omega
  have hdiv : (targetKey i k - 121) / 4 = i := by unfold targetKey; omega
  have hmod : Fin.ofNat 4 ((targetKey i k - 121) % 4) = k := by
    apply Fin.ext
    change ((targetKey i k - 121) % 4) % 4 = k.val
    unfold targetKey
    omega
  simp only [valuation, if_neg ha, if_pos hb, hdiv, hmod]

private theorem val_missed {p : Profile} {bits : BitVec 121} {a b c v : ℕ}
    (hb : b < 11) (hc : c < 11) (hv : v < 11) :
    valuation p bits (missedKey a b c v) =
      !(covers bits a v || covers bits b v || covers bits c v) := by
  have h1 : ¬ missedKey a b c v < 121 := by unfold missedKey; omega
  have h2 : ¬ missedKey a b c v < 165 := by unfold missedKey; omega
  let z := missedKey a b c v - 165
  have ha' : z / 1331 = a := by dsimp [z, missedKey]; omega
  have hb' : z / 121 % 11 = b := by dsimp [z, missedKey]; omega
  have hc' : z / 11 % 11 = c := by dsimp [z, missedKey]; omega
  have hv' : z % 11 = v := by dsimp [z, missedKey]; omega
  change (if missedKey a b c v < 121 then _ else if missedKey a b c v < 165 then _ else
    !(covers bits (z / 1331) (z % 11) || covers bits (z / 121 % 11) (z % 11) ||
      covers bits (z / 11 % 11) (z % 11))) = _
  simp only [if_neg h1, if_neg h2, ha', hb', hc', hv']

private theorem index_lt {p : Profile} {k : Fin 4} {i : ℕ} (hi : i ∈ indices p k) :
    i < p.order := by
  have h := (List.mem_range'_1.mp hi).2
  fin_cases k <;> simp [Profile.size, Profile.offset, Profile.order] at h ⊢ <;> omega

theorem triple_in_range {n a b c : ℕ} (h : (a, b, c) ∈ triples n) :
    a < n ∧ b < n ∧ c < n := by
  rw [triples, List.mem_flatMap] at h
  obtain ⟨z, hz, h⟩ := h
  rw [List.mem_flatMap] at h
  obtain ⟨y, hy, hmap⟩ := h
  obtain ⟨x, hx, he⟩ := List.mem_map.mp hmap
  simp only [Prod.mk.injEq] at he
  rcases he with ⟨rfl, rfl, rfl⟩
  rw [List.mem_range] at hx hy hz
  exact ⟨hx.trans (hy.trans hz), hy.trans hz, hz⟩

private theorem satisfied_literal {a : ℕ → Bool} {i : ℕ} {sign : Bool}
    {c : CNF.Clause ℕ} (h : (i, sign) ∈ c) (he : a i = sign) : c.eval a = true := by
  exact List.any_eq_true.mpr ⟨(i, sign), h, by simp [he]⟩

theorem sat_of_bits {p : Profile} {bits : BitVec 121} (hsmall : p.order ≤ 11)
    (hd : 0 < p.d) (hproper : properBits p bits = true) (hstar : hasStar p bits = true)
    (hcolor : dominatorBits p bits = true) (htriple : noTripleBits p bits = true) :
    (profileCNF p).Sat (valuation p bits) := by
  simp only [CNF.sat_def, profileCNF, CNF.eval_append, Bool.and_eq_true, and_assoc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply List.all_eq_true.mpr
    intro C hC
    rw [properClauses, List.mem_flatMap] at hC
    obtain ⟨k, hk, hC⟩ := hC
    rw [List.mem_flatMap] at hC
    obtain ⟨i, hi, hC⟩ := hC
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hC
    have h := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp hproper k hk) i hi) j hj
    have hf : edge bits i j = false := by simpa using h
    exact satisfied_literal (List.mem_singleton_self _)
      ((val_edge ((index_lt hi).trans_le hsmall) ((index_lt hj).trans_le hsmall)).trans hf)
  · simp only [hasStar, Bool.and_eq_true, and_assoc] at hstar
    have h' := hsmall
    change p.a + p.b + p.c + p.d ≤ 11 at h'
    have ha : p.a < 11 := by omega
    have hb : p.a + p.b < 11 := by omega
    have hc : p.a + p.b + p.c < 11 := by omega
    simp [starClauses, val_edge (by decide : 0 < 11) ha,
      val_edge (by decide : 0 < 11) hb, val_edge (by decide : 0 < 11) hc,
      hstar.1, hstar.2.1, hstar.2.2]
  · apply List.all_eq_true.mpr
    intro C hC
    rw [colorClauses, List.mem_flatMap] at hC
    obtain ⟨i, hi, hC⟩ := hC
    have hi' := (List.mem_range.mp hi).trans_le hsmall
    rcases List.mem_cons.mp hC with h | h
    · subst C
      obtain ⟨k, hk, hw⟩ := List.any_eq_true.mp (List.all_eq_true.mp hcolor i hi)
      exact satisfied_literal (List.mem_map.mpr ⟨k, hk, rfl⟩) ((val_target hi' k).trans hw)
    · obtain ⟨k, _, h⟩ := List.mem_flatMap.mp h
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp h
      obtain ⟨hj, hne⟩ := List.mem_filter.mp hj
      have hne' : i ≠ j := Ne.symm (by simpa using hne)
      by_cases ht : valuation p bits (targetKey i k) = true
      · have h := List.all_eq_true.mp ((val_target hi' k).symm.trans ht) j hj
        have he : edge bits i j = true := by simpa [covers, hne'] using h
        exact satisfied_literal (by simp) ((val_edge hi' ((index_lt hj).trans_le hsmall)).trans he)
      · exact satisfied_literal (by simp) (Bool.eq_false_iff.mpr ht)
  · apply List.all_eq_true.mpr
    intro C hC
    rw [tripleClauses, List.mem_flatMap] at hC
    obtain ⟨⟨a, b, c⟩, ht, hC⟩ := hC
    obtain ⟨ha, hb, hc⟩ := triple_in_range ht
    rcases List.mem_cons.mp hC with h | h
    · subst C
      obtain ⟨v, hv, hw⟩ := List.any_eq_true.mp (List.all_eq_true.mp htriple (a, b, c) ht)
      exact satisfied_literal (List.mem_map.mpr ⟨v, hv, rfl⟩)
        ((val_missed (hb.trans_le hsmall) (hc.trans_le hsmall)
          ((List.mem_range.mp hv).trans_le hsmall)).trans hw)
    · obtain ⟨v, hv, hC⟩ := List.mem_flatMap.mp h
      have hv' := (List.mem_range.mp hv).trans_le hsmall
      have hval := val_missed (p := p) (bits := bits) (a := a)
        (hb.trans_le hsmall) (hc.trans_le hsmall) hv'
      by_cases he : v = a ∨ v = b ∨ v = c
      · simp only [he, if_true, List.mem_singleton] at hC
        subst C
        apply satisfied_literal (List.mem_singleton_self _)
        rw [hval]
        rcases he with h | h | h <;> simp [covers, h]
      · simp only [he, if_false, List.mem_cons, List.not_mem_nil, or_false] at hC
        by_cases hs : valuation p bits (missedKey a b c v) = true
        · have nh := hval.symm.trans hs
          simp only [Bool.not_eq_true', Bool.or_eq_false_iff, and_assoc] at nh
          have nedge (u : ℕ) (hu : covers bits u v = false) : edge bits u v = false := by
            rw [covers, Bool.or_eq_false_iff] at hu
            exact hu.2
          rcases hC with rfl | rfl | rfl
          · exact satisfied_literal (by simp) ((val_edge (ha.trans_le hsmall) hv').trans (nedge a nh.1))
          · exact satisfied_literal (by simp) ((val_edge (hb.trans_le hsmall) hv').trans (nedge b nh.2.1))
          · exact satisfied_literal (by simp) ((val_edge (hc.trans_le hsmall) hv').trans (nedge c nh.2.2))
        · rcases hC with rfl | rfl | rfl <;>
            exact satisfied_literal (by simp) (Bool.eq_false_iff.mpr hs)

open Lean Elab Tactic Meta
open Lean.Elab.Tactic.BVDecide.Frontend

local syntax (name := checkProfileCertificateSyntax) "check_profile_certificate" : tactic

/-- Ask the bundled solver for a proof and check its LRAT certificate in Lean. -/
@[tactic checkProfileCertificateSyntax]
private unsafe def checkProfileCertificate : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let formulaType := mkApp (mkConst ``CNF [.zero]) (mkConst ``Nat)
  let formula ← mkFreshExprMVar formulaType
  let unsatType := mkApp2 (mkConst ``CNF.Unsat [.zero]) (mkConst ``Nat) formula
  unless ← isDefEq unsatType target do
    throwError "expected a concrete CNF unsatisfiability goal, found {target}"
  let formula ← instantiateMVars formula
  let data ← evalExpr (CNF Nat) formulaType formula
  let trace ← IO.FS.withTempFile fun handle path => do
    handle.flush
    let ctx ← TacticContext.new path {}
    let .ok cert ← runExternal data ctx.solver path true 10 false .proof
      | throwError "the profile constraints are satisfiable"
    IO.ofExcept (Std.Tactic.BVDecide.LRAT.parseLRATProof cert.toUTF8)
  let certName ← Term.mkAuxName `_lrat_certificate
  let certType := mkApp (mkConst ``Array [.zero]) (mkConst ``Std.Tactic.BVDecide.LRAT.IntAction)
  addAndCompile (.defnDecl {
    name := certName, levelParams := [], type := certType, value := toExpr trace,
    hints := .abbrev, safety := .safe })
  let checkName ← Term.mkAuxName `_lrat_checked
  let checked := mkApp2 (mkConst ``Std.Tactic.BVDecide.LRAT.check) (mkConst certName) formula
  addAndCompile (.defnDecl {
    name := checkName, levelParams := [], type := mkConst ``Bool, value := checked,
    hints := .abbrev, safety := .safe })
  let proof := mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst checkName)
    (toExpr true) (← mkEqRefl (toExpr true))
  goal.assign (mkApp3 (mkConst ``Std.Tactic.BVDecide.LRAT.check_sound)
    (mkConst certName) formula proof)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 10000000 in
private theorem small_profiles_unsat (p : Profile) (ha : 0 < p.a)
    (hab : p.a ≤ p.b) (hbc : p.b ≤ p.c) (hcd : p.c ≤ p.d)
    (hsmall : p.order ≤ 11) : (profileCNF p).Unsat := by
  rcases p with ⟨a, b, c, d⟩
  change a + b + c + d ≤ 11 at hsmall
  change 0 < a at ha
  change a ≤ b at hab
  change b ≤ c at hbc
  change c ≤ d at hcd
  have ha' : a ≤ 2 := by omega
  have hb' : b ≤ 3 := by omega
  have hc' : c ≤ 4 := by omega
  have hd' : d ≤ 8 := by omega
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d <;>
    first | omega | check_profile_certificate

theorem no_small_profile (p : Profile) (ha : 0 < p.a) (hab : p.a ≤ p.b)
    (hbc : p.b ≤ p.c) (hcd : p.c ≤ p.d) (hsmall : p.order ≤ 11) (bits : BitVec 121)
    (hproper : properBits p bits = true) (hstar : hasStar p bits = true)
    (hcolor : dominatorBits p bits = true) (hno : noTripleBits p bits = true) : False := by
  have hd : 0 < p.d := ha.trans_le (hab.trans (hbc.trans hcd))
  have hs := (small_profiles_unsat p ha hab hbc hcd hsmall) (valuation p bits)
  have ht := (CNF.sat_def _ _).mp (sat_of_bits hsmall hd hproper hstar hcolor hno)
  exact Bool.false_ne_true (hs.symm.trans ht)
end DominatorFour
