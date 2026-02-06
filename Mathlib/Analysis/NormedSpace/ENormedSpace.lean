/-
Copyright (c) 2026 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# ENormedSpace

An extended-normed space is a module over `ℝ≥0` with a continuous function `‖·‖ₑ` into `ℝ≥0∞`
that satisfies the axioms of a norm:
- ‖x + y‖ₑ ≤ ‖x‖ₑ + ‖y‖ₑ
- ‖x‖ₑ = 0 ↔ x = 0
-
-/

@[expose] public noncomputable section

open ENNReal
open scoped NNReal

/-- An enormed space is an additive monoid endowed with a continuous enorm. -/
class ENormedSpace (E : Type*) [TopologicalSpace E] [ESeminormedAddCommMonoid E] extends
    Module ℝ≥0 E, ContinuousConstSMul ℝ≥0 E where
  enorm_smul_eq_smul : ∀ (c : ℝ≥0) (x : E), ‖c • x‖ₑ = c • ‖x‖ₑ

export ENormedSpace (enorm_smul_eq_smul)
attribute [simp] enorm_smul_eq_smul

instance : ENormedSpace ℝ≥0∞ where
  enorm_smul_eq_smul := by simp
  continuous_const_smul t := ENNReal.continuous_const_mul (by simp)

instance : ENormedAddCommMonoid ℝ≥0 where
  enorm := ofNNReal
  enorm_zero := by simp
  enorm_eq_zero := by simp
  enorm_add_le := by simp
  continuous_enorm := by fun_prop

@[simp] lemma NNReal.enorm_def {r : ℝ≥0} : ‖r‖ₑ = ofNNReal r := rfl

instance : ENormedSpace ℝ≥0 where
  enorm_smul_eq_smul c x := by simp [ENNReal.smul_def]

variable {ε E : Type*} [TopologicalSpace ε] [ESeminormedAddCommMonoid ε] [ENormedSpace ε]

instance [NormedAddCommGroup E] [NormedSpace ℝ E] : ENormedSpace E where
  enorm_smul_eq_smul := by
    simp_rw [enorm_eq_nnnorm, ENNReal.smul_def, NNReal.smul_def, nnnorm_smul]; simp

instance : ENormSMulClass ℝ≥0 ε where
  enorm_smul := enorm_smul_eq_smul
