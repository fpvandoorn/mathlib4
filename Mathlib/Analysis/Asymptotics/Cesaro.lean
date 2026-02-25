/-
Copyright (c) 2026 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.RCLike.Basic
import all Mathlib.Order.Filter.AtTopBot.Tendsto -- for to_additive


/-!
# Asymptotics of Cesaro sums

-/

public section

open Filter Asymptotics Topology Finset

theorem Asymptotics.IsLittleO.sum_range {α : Type*} [NormedAddCommGroup α] {f : ℕ → α} {g : ℕ → ℝ}
    (h : f =o[atTop] g) (hg : 0 ≤ g) (h'g : Tendsto (fun n => ∑ i ∈ range n, g i) atTop atTop) :
    (fun n => ∑ i ∈ range n, f i) =o[atTop] fun n => ∑ i ∈ range n, g i := by
  have A : ∀ i, ‖g i‖ = g i := fun i => Real.norm_of_nonneg (hg i)
  have B : ∀ n, ‖∑ i ∈ range n, g i‖ = ∑ i ∈ range n, g i := fun n => by
    rwa [Real.norm_eq_abs, abs_sum_of_nonneg']
  apply isLittleO_iff.2 fun ε εpos => _
  intro ε εpos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ b : ℕ, N ≤ b → ‖f b‖ ≤ ε / 2 * g b := by
    simpa only [A, eventually_atTop] using isLittleO_iff.mp h (half_pos εpos)
  have : (fun _ : ℕ => ∑ i ∈ range N, f i) =o[atTop] fun n : ℕ => ∑ i ∈ range n, g i := by
    apply isLittleO_const_left.2
    exact Or.inr (h'g.congr fun n => (B n).symm)
  filter_upwards [isLittleO_iff.1 this (half_pos εpos), Ici_mem_atTop N] with n hn Nn
  calc
    ‖∑ i ∈ range n, f i‖ = ‖(∑ i ∈ range N, f i) + ∑ i ∈ Ico N n, f i‖ := by
      rw [sum_range_add_sum_Ico _ Nn]
    _ ≤ ‖∑ i ∈ range N, f i‖ + ‖∑ i ∈ Ico N n, f i‖ := norm_add_le _ _
    _ ≤ ‖∑ i ∈ range N, f i‖ + ∑ i ∈ Ico N n, ε / 2 * g i :=
      (add_le_add le_rfl (norm_sum_le_of_le _ fun i hi => hN _ (mem_Ico.1 hi).1))
    _ ≤ ‖∑ i ∈ range N, f i‖ + ∑ i ∈ range n, ε / 2 * g i := by
      gcongr
      · exact fun i _ _ ↦ mul_nonneg (half_pos εpos).le (hg i)
      · rw [range_eq_Ico]
        exact Ico_subset_Ico (zero_le _) le_rfl
    _ ≤ ε / 2 * ‖∑ i ∈ range n, g i‖ + ε / 2 * ∑ i ∈ range n, g i := by rw [← mul_sum]; gcongr
    _ = ε * ‖∑ i ∈ range n, g i‖ := by
      simp only [B]
      ring

theorem Asymptotics.isLittleO_sum_range_of_tendsto_zero {α : Type*} [NormedAddCommGroup α]
    {f : ℕ → α} (h : Tendsto f atTop (𝓝 0)) :
    (fun n => ∑ i ∈ range n, f i) =o[atTop] fun n => (n : ℝ) := by
  have := ((isLittleO_one_iff ℝ).2 h).sum_range fun i => zero_le_one
  simp only [sum_const, card_range, Nat.smul_one_eq_cast] at this
  exact this tendsto_natCast_atTop_atTop

/-- The Cesaro average of a converging sequence converges to the same limit. -/
theorem Filter.Tendsto.cesaro_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℕ → E}
    {l : E} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) • ∑ i ∈ range n, u i) atTop (𝓝 l) := by
  rw [← tendsto_sub_nhds_zero_iff, ← isLittleO_one_iff ℝ]
  have := Asymptotics.isLittleO_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 h)
  apply ((isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop).smul_isLittleO this).congr' _ _
  · filter_upwards [Ici_mem_atTop 1] with n npos
    have nposℝ : (0 : ℝ) < n := Nat.cast_pos.2 npos
    simp only [smul_sub, sum_sub_distrib, sum_const, card_range, sub_right_inj]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ nposℝ.ne', one_smul]
  · filter_upwards [Ici_mem_atTop 1] with n npos
    have nposℝ : (0 : ℝ) < n := Nat.cast_pos.2 npos
    rw [smul_eq_mul, inv_mul_cancel₀ nposℝ.ne']

/-- The Cesaro average of a converging sequence converges to the same limit. -/
theorem Filter.Tendsto.cesaro {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ i ∈ range n, u i) atTop (𝓝 l) :=
  h.cesaro_smul

variable {α β : Type*} [CommMonoid α] [TopologicalSpace α]
  {f : β → α} {a : α}
@[to_additive]
lemma hasProd_conditional_iff [Preorder β] [LocallyFiniteOrder β] : HasProd f a (.conditional β) ↔
    Tendsto (fun p ↦ ∏ b ∈ Icc p.1 p.2, f b) (atBot ×ˢ atTop) (𝓝 a) := by rfl

-- attribute [to_dual] OrderBot.atBot_eq

-- todo: dualize
@[to_additive]
lemma hasProd_conditional_bot_iff [PartialOrder β] [LocallyFiniteOrder β] [OrderBot β] :
    HasProd f a (.conditional β) ↔
    Tendsto (fun c ↦ ∏ b ∈ Icc ⊥ c, f b) atTop (𝓝 a) := by
  simp_rw [hasProd_conditional_iff, OrderBot.atBot_eq, pure_prod, Filter.tendsto_map'_iff,
    Function.comp_def]

@[to_additive]
lemma hasProd_conditional_nat_iff {f : ℕ → α} :
    HasProd f a (.conditional ℕ) ↔
    Tendsto (fun n ↦ ∏ b ∈ range n, f b) atTop (𝓝 a) := by
  simp_rw [hasProd_conditional_bot_iff, Nat.bot_eq_zero, ← Nat.range_succ_eq_Icc_zero]
  exact Filter.tendsto_add_atTop_iff_nat (f := fun n ↦ ∏ b ∈ range n, f b) 1

@[to_additive]
lemma Filter.tendsto_mul_const_iff {α M : Type*} [TopologicalSpace M] [Group M]
    [ContinuousMul M] {b c : M} {f : α → M} {l : Filter α} :
    Tendsto (fun k => f k * b) l (nhds (c * b)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨?_, Tendsto.mul_const b⟩
  convert Tendsto.mul_const b⁻¹ using 3 <;> rw [mul_inv_cancel_right]

@[to_additive]
lemma Filter.tendsto_const_mul_iff {α M : Type*} [TopologicalSpace M] [Group M]
    [ContinuousMul M] {b c : M} {f : α → M} {l : Filter α} :
    Tendsto (fun k => b * f k) l (nhds (b * c)) ↔ Tendsto f l (𝓝 c) := by
  refine ⟨?_, Tendsto.const_mul b⟩
  convert Tendsto.const_mul b⁻¹ using 3 <;> rw [inv_mul_cancel_left]

-- @[to_additive tendsto_sub_const_iff]
lemma Filter.tendsto_div_const_iff' {α M : Type*} [TopologicalSpace M] [Group M]
    [ContinuousMul M] {b c : M} {f : α → M} {l : Filter α} :
    Tendsto (fun k => f k / b) l (nhds (c / b)) ↔ Tendsto f l (𝓝 c) := by
  simp_rw [div_eq_mul_inv, tendsto_mul_const_iff]

@[to_additive const_sub_iff]
lemma Filter.tendsto_const_div_iff' {α M : Type*} [TopologicalSpace M] [Group M]
    [IsTopologicalGroup M] {b c : M} {f : α → M} {l : Filter α} :
    Tendsto (fun k => b / f k) l (nhds (b / c)) ↔ Tendsto f l (𝓝 c) := by
  simp_rw [div_eq_mul_inv, tendsto_const_mul_iff, tendsto_inv_iff]

/-
Hardy's Tauberian Theorem: If the arithmetic means of partial sums converge of a sequence converge
to `l`, and the differences are `O(1 / n)`, then the sequence converges to `l`.
-/
theorem tendsto_of_tendsto_cesaro {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℕ → E} {l : E}
    (h : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) • ∑ i ∈ range n, u i) atTop (𝓝 l))
    (h_bound : (fun n ↦ u (n + 1) - u n) =O[atTop] (fun n ↦ (n : ℝ)⁻¹)) :
    Tendsto u atTop (𝓝 l) := by
  sorry

/-
Hardy's Tauberian Theorem: If the arithmetic means of partial sums of a series converge to `l`,
and the terms are `O(1 / n)`, then the series converges to `l`.
-/
theorem hasSum_of_tendsto_cesaro {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℕ → E} {l : E}
    (h : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) • ∑ (i ∈ range n), ∑ (j ∈ range i), u j)
      atTop (𝓝 l))
    (h_bound : u =O[atTop] (fun n ↦ (n : ℝ)⁻¹)) :
    HasSum u l (.conditional ℕ) := by
  simp_rw [hasSum_conditional_nat_iff]
  apply tendsto_of_tendsto_cesaro h
  simp_rw [sum_range_succ, add_sub_cancel_left, h_bound]

/-
Hardy's Tauberian Theorem: If the arithmetic means of partial sums converge of a sequence converge
to `l`, and the differences are `O(1 / n)`, then the sequence converges to `l`.
-/
theorem tendsto_of_tendsto_cesaro' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u : ℕ → E} {l : E}
    (h : Tendsto (fun n : ℕ => (n⁻¹ : ℝ) • ∑ i ∈ range n, u i) atTop (𝓝 l))
    (h_bound : (fun n ↦ u (n + 1) - u n) =O[atTop] (fun n ↦ (n : ℝ)⁻¹)) :
    Tendsto u atTop (𝓝 l) := by
  rw [funext (Finset.eq_sum_range_sub u), ← add_sub_cancel (u 0) l,
    tendsto_const_add_iff, ← hasSum_conditional_nat_iff]
  apply hasSum_of_tendsto_cesaro _ h_bound
  have := fun n ↦ inv_smul_smul₀ (α := ℝ) (β := E) (Nat.cast_ne_zero.mpr <| Nat.add_one_ne_zero n)
  simp_rw +singlePass [sum_range_sub u, sum_sub_distrib, sum_const, card_range, smul_sub,
    ← Nat.cast_smul_eq_nsmul ℝ, ← Filter.tendsto_add_atTop_iff_nat 1, this,
    tendsto_sub_const_iff, (Filter.tendsto_add_atTop_iff_nat 2).mpr h]
