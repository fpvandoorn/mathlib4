/-
Copyright (c) 2026 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.SetTheory.Ordinal.CantorNormalForm
public import Mathlib.SetTheory.Ordinal.Veblen

/-!
# Fundamental sequences and the fast-growing hierarchy
-/

set_option linter.unusedVariables false
@[expose] public noncomputable section

open Order
universe u

/- Set the last element of `l` to `x` (sends `[]` to `[]`). -/
def List.setLast {α} (l : List α) (x : α) : List α :=
  l.set (l.length - 1) x

namespace Ordinal

variable {o : Ordinal.{u}}

lemma not_isSuccPrelimit_or_eq_zero_iff :
    ¬ IsSuccPrelimit o ∨ o = 0 ↔ ¬ IsSuccLimit o := by
  simp_rw [Ordinal.isSuccLimit_iff, not_and_or, or_comm, not_ne_iff]

lemma not_isSuccPrelimit_iff :
    ¬ IsSuccPrelimit o ↔ ¬ IsSuccLimit o ∧ o ≠ 0 := by
  simp_rw [← not_isSuccPrelimit_or_eq_zero_iff, or_and_right, ne_eq, and_not_self, or_false,
    iff_self_and, not_imp_not]
  rintro rfl
  exact isSuccPrelimit_zero

theorem lt_omega0_opow_of_lt_epsilon0 (h : o < ε₀) : o < ω ^ o := by
  contrapose! h
  exact epsilon0_le_of_omega0_opow_le h

/-- Send finite ordinals to their corresponding natural numbers. Send infinite ordinals to 0 -/
def toNat (o : Ordinal) : ℕ :=
  if h : o < ω then lt_omega0.mp h |>.choose else 0

lemma coe_toNat (h : o < ω) : o.toNat = o := by
  simp_rw [toNat, dif_pos h, ← (lt_omega0.mp h).choose_spec]

lemma toNat_coe (n : ℕ) : (n : Ordinal).toNat = n := by
  rw [← Nat.cast_injective (R := Ordinal) |>.eq_iff, coe_toNat (nat_lt_omega0 n)]


namespace CNF

/-- The last element in the CNF-expansion of `CNF ω o` -/
def last (o : Ordinal) : Ordinal × Ordinal :=
  (CNF ω o).getLast?.getD (0, 0)

-- /-- The last element in the CNF-expansion of `CNF ω o` -/
-- def last' (o : Ordinal) : Ordinal × ℕ :=
--   (CNF ω o).getLast?.elim (0, 0) fun (p, b) ↦ (p, b.toNat)

lemma last_fsnd_pos (o : Ordinal) : 0 < (last o).2 ↔ o ≠ 0 := by sorry
lemma omega_pow_last_fst_le (o : Ordinal) : ω ^ (last o).1 ≤ o := by sorry
lemma last_fst_le (o : Ordinal) : (last o).1 ≤ o := by sorry
lemma last_fst_lt (h : o < ε₀) : (last o).1 < o := by sorry

lemma isSuccLimit_iff (o : Ordinal) :
  IsSuccLimit o ↔ (CNF ω o).getLast?.any fun (p, c) ↦ p > 0 := by sorry

def _root_.Ordinal.fromCNF (b : Ordinal.{u}) (c : List (Ordinal.{u} × Ordinal.{u})) : Ordinal.{u} :=
  c.foldr (fun p r ↦ b ^ p.1 * p.2 + r) 0

theorem CNF_coe (b o : Ordinal) : .fromCNF b (CNF b o) = o := CNF.foldr b o

lemma last_pow_lt (o : Ordinal) :
  ((ω).CNF o).getLast?.all fun (p, b) ↦ p < o := by sorry


end CNF


/-- Fundamental sequence for a limit ordinal with countable cofinality -/
structure IsFundSeq (o : Ordinal.{u}) (f : ℕ → Ordinal.{u}) : Prop where
  monotone : Monotone f
  lsub : lsub f = o

namespace IsFundSeq

variable {o : Ordinal.{u}} {f : ℕ → Ordinal.{u}}
protected lemma lt (h : IsFundSeq o f) (i : ℕ) : f i < o := by
  simp_rw [← h.lsub, lt_lsub]

end IsFundSeq

/-- All limit ordinals below `o` have an associated fundamental sequence.
We totalize the function `seq`. -/
class FundSequences (c : Ordinal.{u}) where
  seq : Ordinal.{u} → ℕ → Ordinal.{u}
  isFundSeq : ∀ o < c, IsSuccLimit o → IsFundSeq o (seq o)

export FundSequences (seq isFundSeq)

section FundSequences

variable {c c' : Ordinal.{u}} [FundSequences c] {o : Ordinal.{u}}

lemma seq_lt (hc : o < c) (ho : IsSuccLimit o) (i : ℕ) : c.seq o i < o :=
  c.isFundSeq o hc ho |>.lt i

namespace FundSequences

protected def omega : FundSequences ω where
  seq o i := 0
  isFundSeq o hc ho := (omega0_le_of_isSuccLimit ho).not_gt hc |>.elim

-- /-- Fundamental sequence up to `ε₀` -/
-- def fundSeqOmegaPow : Ordinal.{u} → ℕ → Ordinal.{u}

-- open Classical in
-- def replaceLast : (c : Ordinal.{u}) → (i : ℕ) →
--     (f : (q : Ordinal.{u}) → (∀ p < min c q, Ordinal.{u}) → Ordinal.{u} × Ordinal.{u}) →
--     Ordinal.{u}
--   | c, i, f =>
--     let (p, b) := CNF.last c
--     let l := CNF ω c
--     /- (ω^p)[i] -/
--     let c : Ordinal × Ordinal :=
--       f p fun o ho ↦ replaceLast o i _
--     if b = 0 then 0 else
--     if b > 1 then fromCNF ω <| l.take (l.length - 1) ++ [(p, b - 1), c] else
--     fromCNF ω <| l.take (l.length - 1) ++ [c]
-- termination_by c => c

open Classical in
/-- Fundamental sequence up to `ε₀` -/
def fundSeqEpsilon0 : Ordinal.{u} → ℕ → Ordinal.{u}
  | o, i =>
    let (p, b) := CNF.last o
    let l := CNF ω o
    /- (ω^p)[i] -/
    let c :=
      if IsSuccLimit p then
      /- ω^(p[i]) if that is well-defined -/
      if h : p < o then ω ^ fundSeqEpsilon0 p i else 0
      /- ω^(p - 1) * i -/
      else ω ^ p.pred * i
    if b = 0 then 0 else
    if b > 1 then fromCNF ω l.dropLast + ω ^ p * b.pred + c else
    fromCNF ω l.dropLast + c
termination_by o => o

protected def epsilon0 : FundSequences ε₀ where
  seq := fundSeqEpsilon0
  isFundSeq o hc ho := sorry

open Classical in
/-- Fundamental sequence up to `Γ₀` -/
def fundSeqGamma0 : Ordinal.{u} → ℕ → Ordinal.{u}
  | o, i =>
    -- let (p, b) := CNF.last o -- this isn't defeq?
    let p := (CNF.last o).1
    let b := (CNF.last o).2
    let l := CNF ω o
    let q := invVeblen₁ p
    let r := invVeblen₂ p
    /- (ω^p)[i] -/
    let c :=
      if r = 0 then
      if IsSuccLimit p then
      if h : q < o then veblen (fundSeqGamma0 q i) 0 else 0 else
      (veblen q.pred)^[i] 0
      else if IsSuccLimit r then
      have : r < o := invVeblen₂_lt p |>.trans_le <| CNF.omega_pow_last_fst_le o
      veblen q (fundSeqGamma0 r i) else
      (veblen q)^[i] (succ (veblen q r.pred))
    if b = 0 then 0 else
    if b > 1 then fromCNF ω l.dropLast + ω ^ p * b.pred + c else
    fromCNF ω l.dropLast + c
termination_by o => o

protected def Gamma0 : FundSequences Γ₀ where
  seq := fundSeqGamma0
  isFundSeq o hc ho := sorry


protected def lt (hc' : c' ≤ c) : FundSequences c' where
  seq o i := c.seq o i
  isFundSeq o hc ho := isFundSeq o (hc.trans_le hc') ho

end FundSequences

end FundSequences

open Classical in
/-- The fast growing hierarchy up to (but excluding) ordinal `c`. -/
def fastGrowing (c : Ordinal.{u}) [FundSequences c] : Ordinal.{u} → ℕ → ℕ
  | o, i =>
    if hc : o < c ∧ o ≠ 0 then
    if ho : IsSuccLimit o then
      have : c.seq o i < o := c.seq_lt hc.1 ho i
      fastGrowing c (c.seq o i) i
    else
      have : o.pred < o :=
        pred_lt_iff_not_isSuccPrelimit.mpr (not_isSuccPrelimit_iff.mpr ⟨ho, hc.2⟩)
      (fastGrowing c o.pred)^[i] i
    else
      Nat.succ i
termination_by o => o



end Ordinal
