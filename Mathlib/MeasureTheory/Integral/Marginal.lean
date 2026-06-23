/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Tactic.ClickSuggestions -- delete when making Mathlib PR

/-!
# Marginals of multivariate functions

In this file, we define a convenient way to compute integrals of multivariate functions, especially
if you want to write expressions where you integrate only over some of the variables that the
function depends on. This is common in induction arguments involving integrals of multivariate
functions.
This constructions allows working with iterated integrals and applying Tonelli's theorem
and Fubini's theorem, without using measurable equivalences by changing the representation of your
space (e.g. `((ι ⊕ ι') → ℝ) ≃ (ι → ℝ) × (ι' → ℝ)`).

## Main Definitions

* Assume that `∀ i : ι, X i` is a product of measurable spaces with measures `μ i` on `X i`,
  `f : (∀ i, X i) → ℝ≥0∞` is a function and `s : Finset ι`.
  Then `lmarginal μ s f` or `∫⋯∫⁻_s, f ∂μ` is the function that integrates `f`
  over all variables in `s`. It returns a function that still takes the same variables as `f`,
  but is constant in the variables in `s`. Mathematically, if `s = {i₁, ..., iₖ}`,
  then `lmarginal μ s f` is the expression
  $$
  \vec{x}\mapsto \int\!\!\cdots\!\!\int f(\vec{x}[\vec{y}])dy_{i_1}\cdots dy_{i_k}.
  $$
  where $\vec{x}[\vec{y}]$ is the vector $\vec{x}$ with $x_{i_j}$ replaced by $y_{i_j}$ for all
  $1 \le j \le k$.
  If `f` is the distribution of a random variable, this is the marginal distribution of all
  variables not in `s` (but not the most general notion, since we only consider product measures
  here).
  Note that the notation `∫⋯∫⁻_s, f ∂μ` is not a binder, and returns a function.

## Main Results

* `lmarginal_union` is the analogue of Tonelli's theorem for iterated integrals. It states that
  for measurable functions `f` and disjoint finsets `s` and `t` we have
  `∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ`.

## Implementation notes

The function `f` can have an arbitrary product as its domain (even infinite products), but the
set `s` of integration variables is a `Finset`. We are assuming that the function `f` is measurable
for most of this file. Note that asking whether it is `AEMeasurable` is not even well-posed,
since there is no well-behaved measure on the domain of `f`.

## TODO

* Define the marginal function for functions taking values in a Banach space.

-/

@[expose] public section

#click_suggestions

open scoped ENNReal
open Set Function Equiv Finset

noncomputable section

namespace MeasureTheory

section LMarginal

variable {δ δ' : Type*} {X : δ → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [DecidableEq δ]
variable {s t : Finset δ} {f : (∀ i, X i) → ℝ≥0∞} {x : ∀ i, X i}

/-- Integrate `f(x₁,…,xₙ)` over all variables `xᵢ` where `i ∈ s`. Return a function in the
  remaining variables (it will be constant in the `xᵢ` for `i ∈ s`).
  This is the marginal distribution of all variables not in `s` when the considered measure
  is the product measure. -/
def lmarginal (μ : ∀ i, Measure (X i)) (s : Finset δ) (f : (∀ i, X i) → ℝ≥0∞)
    (x : ∀ i, X i) : ℝ≥0∞ :=
  ∫⁻ y : ∀ i : s, X i, f (updateFinset x s y) ∂Measure.pi fun i : s => μ i

-- Note: this notation is not a binder. This is more convenient since it returns a function.
@[inherit_doc]
notation "∫⋯∫⁻_" s ", " f " ∂" μ:70 => lmarginal μ s f

@[inherit_doc lmarginal]
notation3 "∫⋯∫⁻_" s ", " f => lmarginal (fun _ ↦ volume) s f

variable (μ)

theorem _root_.Measurable.lmarginal [∀ i, SigmaFinite (μ i)] (hf : Measurable f) :
    Measurable (∫⋯∫⁻_s, f ∂μ) :=
  Measurable.lintegral_prod_right (hf.comp measurable_updateFinset')

@[simp] theorem lmarginal_empty (f : (∀ i, X i) → ℝ≥0∞) : ∫⋯∫⁻_∅, f ∂μ = f := by
  ext1 x
  simp_rw [lmarginal, Measure.pi_of_empty fun i : (∅ : Finset δ) => μ i]
  apply lintegral_dirac'
  exact Subsingleton.measurable

/-- A generalization of `lmarginal_congr` that also proves that the marginal doesn't depend on
  a variable `xᵢ` if the function `f` doesn't depend on the variable `xᵢ`. -/
theorem lmarginal_congr' {x y : ∀ i, X i} (f : (∀ i, X i) → ℝ≥0∞)
    (h : DependsOn f (s ∪ {i | x i = y i})) : (∫⋯∫⁻_s, f ∂μ) x = (∫⋯∫⁻_s, f ∂μ) y := by
  dsimp [lmarginal, updateFinset_def]
  grind [DependsOn]

/-- The marginal distribution is independent of the variables in `s`.

Special case of `lmarginal_congr'` (though proving it directly is easier than using
`lmarginal_congr'`) -/
theorem lmarginal_congr {x y : ∀ i, X i} (f : (∀ i, X i) → ℝ≥0∞)
    (h : ∀ i ∉ s, x i = y i) :
    (∫⋯∫⁻_s, f ∂μ) x = (∫⋯∫⁻_s, f ∂μ) y := by
  dsimp only [lmarginal, updateFinset_def]
  grind

theorem lmarginal_update_of_mem {i : δ} (hi : i ∈ s)
    (f : (∀ i, X i) → ℝ≥0∞) (x : ∀ i, X i) (y : X i) :
    (∫⋯∫⁻_s, f ∂μ) (Function.update x i y) = (∫⋯∫⁻_s, f ∂μ) x := by
  grind [MeasureTheory.lmarginal_congr]

variable {μ} in
theorem lmarginal_singleton (f : (∀ i, X i) → ℝ≥0∞) (i : δ) :
    ∫⋯∫⁻_{i}, f ∂μ = fun x => ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by
  let α : Type _ := ({i} : Finset δ)
  let e := (MeasurableEquiv.piUnique fun j : α ↦ X j).symm
  ext1 x
  calc (∫⋯∫⁻_{i}, f ∂μ) x
      = ∫⁻ (y : X (default : α)), f (updateFinset x {i} (e y)) ∂μ (default : α) := by
        simp_rw [lmarginal,
          measurePreserving_piUnique (fun j : ({i} : Finset δ) ↦ μ j) |>.symm _
            |>.lintegral_map_equiv, e, α]
    _ = ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i := by simp [update_eq_updateFinset]; rfl

variable {μ} in
@[gcongr]
theorem lmarginal_mono {f g : (∀ i, X i) → ℝ≥0∞} (hfg : f ≤ g) : ∫⋯∫⁻_s, f ∂μ ≤ ∫⋯∫⁻_s, g ∂μ :=
  fun _ => lintegral_mono fun _ => hfg _

variable [∀ i, SigmaFinite (μ i)]

-- move
lemma _root_.AEMeasurable.prodMk_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    {f : α × β → ℝ≥0∞} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, AEMeasurable (fun y ↦ f (x, y)) ν := by
  obtain ⟨g, hg, hfg⟩ := hf
  filter_upwards [MeasureTheory.Measure.ae_ae_eq_curry_of_prod hfg] with x hx
  refine AEMeasurable.congr ?_ hx.symm
  exact hg.fun_comp (measurable_const.prodMk measurable_id') |>.aemeasurable

-- move
variable {δ' : Type*} [DecidableEq δ'] in
@[simps]
def _root_.Equiv.finsetCoeCongr {s t : Finset δ'} (h : s = t) :
    s ≃ t where
  toFun i := ⟨i, h ▸ i.2⟩
  invFun i := ⟨i, h ▸ i.2⟩
  left_inv i := by ext; rfl
  right_inv i := by ext; rfl

-- move
variable {δ' : Type*} [DecidableEq δ'] in
@[simps]
def _root_.Equiv.finsetUniv [Fintype δ'] :
  Finset.univ (α := δ') ≃ δ' where
  toFun i := i
  invFun i := ⟨i, mem_univ _⟩
  left_inv i := by ext; rfl
  right_inv i := rfl

-- move
variable {α : Type*} [DecidableEq α] [Fintype α] in
@[simp]
theorem _root_.Finset.compl_union_self (s : Finset α) : sᶜ ∪ s = Finset.univ :=
  compl_sup_eq_top

-- move
variable {δ' : Type*} (π : δ' → Type*) [(i : δ') → MeasurableSpace (π i)]
  [DecidableEq δ'] in
def _root_.MeasurableEquiv.piFinsetComplUnion [Fintype δ'] (s : Finset δ') :
    ((∀ i : ↥sᶜ, π i) × ∀ i : s, π i) ≃ᵐ ∀ i, π i :=
  MeasurableEquiv.piFinsetUnion π disjoint_compl_left |>.trans <| MeasurableEquiv.piCongrLeft π <|
  Equiv.finsetCoeCongr (compl_union_self s) |>.trans Equiv.finsetUniv

-- Ok if we add these too?
variable {ι : Type*} [DecidableEq ι] (α : ι → Type*) in
def _root_.Equiv.piFinsetComplUnion [Fintype ι] (s : Finset ι) :
    ((∀ i : ↥sᶜ, α i) × ∀ i : s, α i) ≃ ∀ i, α i :=
  Equiv.piFinsetUnion α disjoint_compl_left |>.trans <| Equiv.piCongrLeft α <|
  Equiv.finsetCoeCongr (compl_union_self s) |>.trans Equiv.finsetUniv

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*} in
theorem _root_.Equiv.piFinsetComplUnion_eq_of_notMem [Fintype ι] {s : Finset ι}
    {f : ∀ i : ↥sᶜ, α i} {g : ∀ i : s, α i} {i : ι} (hi : i ∉ s) :
    piFinsetComplUnion α s ⟨f, g⟩ i = f ⟨i, Finset.mem_compl.mpr hi⟩ :=
  Equiv.piFinsetUnion_left α disjoint_compl_left (Finset.mem_compl.mpr hi)
    (Finset.mem_union_left s <| Finset.mem_compl.mpr hi)

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*} in
theorem _root_.Equiv.piFinsetComplUnion_eq_of_mem [Fintype ι] {s : Finset ι}
    {f : ∀ i : ↥sᶜ, α i} {g : ∀ i : s, α i} {i : ι} (hi : i ∈ s) :
    piFinsetComplUnion α s ⟨f, g⟩ i = g ⟨i, hi⟩ :=
  Equiv.piFinsetUnion_right α disjoint_compl_left hi <| Finset.mem_union_right _ hi

-- move
theorem measurePreserving_piFinsetComplUnion [Fintype δ] (s : Finset δ) :
    MeasurePreserving (MeasurableEquiv.piFinsetComplUnion X s)
      ((Measure.pi fun i ↦ μ i.1).prod (Measure.pi fun i ↦ μ i))
      (Measure.pi fun i ↦ μ i) :=
  measurePreserving_piFinsetUnion (disjoint_compl_left (a := s)) μ |>.trans <|
    measurePreserving_piCongrLeft μ <|
    Equiv.finsetCoeCongr (compl_union_self s) |>.trans Equiv.finsetUniv

variable {δ' : Type*} {π : δ' → Type*} [(i : δ') → MeasurableSpace (π i)] [DecidableEq δ'] in
lemma MeasurableEquiv.piFinsetComplUnion_apply [Fintype δ'] {s : Finset δ'}
    (x : ((i : ↥sᶜ) → π i) × ((i : ↥s) → π i)) :
    MeasurableEquiv.piFinsetComplUnion π s x =
    Equiv.piFinsetComplUnion π s x := rfl

variable {δ' : Type*} {π : δ' → Type*} [DecidableEq δ'] in
lemma Equiv.updateFinset_piFinsetComplUnion [Fintype δ'] {s : Finset δ'}
    (x : ((i : ↥sᶜ) → π i) × ((i : ↥s) → π i))
    (y : (i : ↥s) → π i) :
    updateFinset (Equiv.piFinsetComplUnion π s x) s y =
    Equiv.piFinsetComplUnion π s (x.1, y) := by
  ext i
  by_cases hi : i ∈ s
  · simpa [updateFinset, hi] using piFinsetComplUnion_eq_of_mem (f := x.1) (g := y) hi |>.symm
  · simp only [updateFinset, hi, ↓reduceDIte, piFinsetComplUnion_eq_of_notMem hi]

lemma _root_.AEMeasurable.comp_updateFinset [Fintype δ] (hf : AEMeasurable f (.pi μ)) :
    ∀ᵐ x ∂Measure.pi μ, AEMeasurable (f <| updateFinset x s ·) (Measure.pi (μ ·)) := by
  let f' : ((∀ i : (sᶜ : Finset δ), X i) × (∀ i : (s : Finset δ), X i)) → ℝ≥0∞ :=
    f ∘' MeasurableEquiv.piFinsetComplUnion X s
  have : AEMeasurable f' ((Measure.pi (μ ·.1)).prod (Measure.pi (μ ·.1))) := by
    rw [← measurePreserving_piFinsetComplUnion .. |>.map_eq] at hf
    exact hf.comp_measurable (MeasurableEquiv.measurable _)
  have h' : ∀ᵐ (x : (i : ↥sᶜ) → X ↑i) ∂Measure.pi (μ ·.1),
      AEMeasurable (fun y ↦ f' (x, y)) (Measure.pi (μ ·.1)) :=
    AEMeasurable.prodMk_left this
  let e := MeasurableEquiv.piFinsetComplUnion X s
  rw [← measurePreserving_piFinsetComplUnion μ _ |>.map_eq, e.measurableEmbedding.ae_map_iff]
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h'] with x hx
  simp_rw [f', Function.dcomp, MeasurableEquiv.piFinsetComplUnion_apply] at hx
  simp_rw [e, MeasurableEquiv.piFinsetComplUnion_apply, Equiv.updateFinset_piFinsetComplUnion, hx]

-- open MeasurableSpace in
-- lemma absolutelyContinuous_generateFrom_iff {α : Type*} {C : Set (Set α)}
--     {μ ν : Measure[generateFrom C] α} (h : ∀ s ∈ C, ν s = 0 → μ s = 0) : μ ≪ ν := by
--   apply Measure.AbsolutelyContinuous.mk fun s hs hνs ↦ ?_
--   induction hs with
--   | basic u hu => exact h u hu hνs
--   | empty => exact measure_empty
--   | compl t ht ih => sorry
--   | iUnion f hf ih => sorry


-- move / is this true?
lemma quasiMeasurePreserving_updateFinset [Fintype δ] :
  Measure.QuasiMeasurePreserving
    (fun a : ((i : δ) → X i) × ((i : s) → X i) ↦ updateFinset a.1 s a.2)
    ((Measure.pi μ).prod (Measure.pi fun i ↦ μ i)) (Measure.pi μ) := by
  refine ⟨measurable_updateFinset', ?_⟩
  sorry

lemma _root_.AEMeasurable.marginal [Fintype δ] (hf : AEMeasurable f (.pi μ)) :
    AEMeasurable (∫⋯∫⁻_ s, f ∂μ) (Measure.pi (μ ·)) := by
  apply AEMeasurable.lintegral_prod_right
  exact hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_updateFinset μ)




theorem lmarginal_union_ae_apply (f : (∀ i, X i) → ℝ≥0∞)
    {x : (i : δ) → X i}
    (hx : AEMeasurable (fun y ↦ f (updateFinset x (s ∪ t) y)) (Measure.pi fun x ↦ μ ↑x))
    (hst : Disjoint s t) : (∫⋯∫⁻_s ∪ t, f ∂μ) x = (∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ) x := by
  let e := MeasurableEquiv.piFinsetUnion X hst
  calc (∫⋯∫⁻_s ∪ t, f ∂μ) x
      = ∫⁻ (y : (i : ↥(s ∪ t)) → X i), f (updateFinset x (s ∪ t) y)
          ∂.pi fun i' : ↥(s ∪ t) ↦ μ i' := rfl
    _ = ∫⁻ (y : ((i : s) → X i) × ((j : t) → X j)), f (updateFinset x (s ∪ t) _)
          ∂(Measure.pi fun i : s ↦ μ i).prod (.pi fun j : t ↦ μ j) := by
        rw [measurePreserving_piFinsetUnion hst μ |>.lintegral_map_equiv]
    _ = ∫⁻ (y : (i : s) → X i), ∫⁻ (z : (j : t) → X j), f (updateFinset x (s ∪ t) (e (y, z)))
          ∂.pi fun j : t ↦ μ j ∂.pi fun i : s ↦ μ i := by
        apply lintegral_prod
        rw [← measurePreserving_piFinsetUnion hst μ |>.map_eq] at hx
        exact hx.comp_measurable (g := f ∘ updateFinset x _) e.measurable
    _ = (∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ) x := by
        simp_rw [lmarginal, updateFinset_updateFinset hst]
        rfl

theorem lmarginal_union_ae [Fintype δ] (f : (∀ i, X i) → ℝ≥0∞) (hf : AEMeasurable f (.pi μ))
    (hst : Disjoint s t) : ∫⋯∫⁻_s ∪ t, f ∂μ =ᵐ[Measure.pi μ] ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ := by
  filter_upwards [hf.comp_updateFinset] with x hx
  exact lmarginal_union_ae_apply μ f hx hst

theorem lmarginal_union (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f)
    (hst : Disjoint s t) : ∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ := by
  ext1 x
  exact lmarginal_union_ae_apply μ f (hf.comp measurable_updateFinset).aemeasurable hst

-- todo: rename to `lmarginal_union_rev` or something
theorem lmarginal_union' (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) {s t : Finset δ}
    (hst : Disjoint s t) : ∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_t, ∫⋯∫⁻_s, f ∂μ ∂μ := by
  rw [Finset.union_comm, lmarginal_union μ f hf hst.symm]

variable {μ}

/-- Peel off a single integral from a `lmarginal` integral at the beginning (compare with
`lmarginal_insert'`, which peels off an integral at the end). -/
theorem lmarginal_insert (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∉ s) (x : ∀ i, X i) :
    (∫⋯∫⁻_insert i s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫⁻_s, f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  rw [Finset.insert_eq, lmarginal_union μ f hf (Finset.disjoint_singleton_left.mpr hi),
    lmarginal_singleton]

/-- Peel off a single integral from a `lmarginal` integral at the beginning (compare with
`lmarginal_erase'`, which peels off an integral at the end). -/
theorem lmarginal_erase (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∈ s) (x : ∀ i, X i) :
    (∫⋯∫⁻_s, f ∂μ) x = ∫⁻ xᵢ, (∫⋯∫⁻_(erase s i), f ∂μ) (Function.update x i xᵢ) ∂μ i := by
  simpa [insert_erase hi] using lmarginal_insert _ hf (notMem_erase i s) x

/-- Peel off a single integral from a `lmarginal` integral at the end (compare with
`lmarginal_insert`, which peels off an integral at the beginning). -/
theorem lmarginal_insert' (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∉ s) :
    ∫⋯∫⁻_insert i s, f ∂μ = ∫⋯∫⁻_s, (fun x ↦ ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  rw [Finset.insert_eq, Finset.union_comm,
    lmarginal_union (s := s) μ f hf (Finset.disjoint_singleton_right.mpr hi), lmarginal_singleton]

/-- Peel off a single integral from a `lmarginal` integral at the end (compare with
`lmarginal_erase`, which peels off an integral at the beginning). -/
theorem lmarginal_erase' (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) {i : δ}
    (hi : i ∈ s) :
    ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_(erase s i), (fun x ↦ ∫⁻ xᵢ, f (Function.update x i xᵢ) ∂μ i) ∂μ := by
  simpa [insert_erase hi] using lmarginal_insert' _ hf (notMem_erase i s)

@[simp] theorem lmarginal_univ [Fintype δ] {f : (∀ i, X i) → ℝ≥0∞} :
    ∫⋯∫⁻_univ, f ∂μ = fun _ => ∫⁻ x, f x ∂Measure.pi μ := by
  let e : { j // j ∈ Finset.univ } ≃ δ := Equiv.subtypeUnivEquiv mem_univ
  ext1 x
  simp_rw [lmarginal, measurePreserving_piCongrLeft μ e |>.lintegral_map_equiv, updateFinset_def]
  simp
  rfl

theorem lintegral_eq_lmarginal_univ [Fintype δ] {f : (∀ i, X i) → ℝ≥0∞} (x : ∀ i, X i) :
    ∫⁻ x, f x ∂Measure.pi μ = (∫⋯∫⁻_univ, f ∂μ) x := by simp

-- move
instance [Fintype δ] [∀ i, NeZero (μ i)] : NeZero (Measure.pi μ) := by
  rw [neZero_iff, ← Measure.measure_univ_ne_zero, Measure.pi_univ, Finset.prod_ne_zero_iff]
  simp [NeZero.ne]

theorem lmarginal_lmarginal_compl [Fintype δ] [∀ i, NeZero (μ i)] (f : (∀ i, X i) → ℝ≥0∞)
    (hf : AEMeasurable f (.pi μ)) : (∫⋯∫⁻_s, ∫⋯∫⁻_sᶜ, f ∂μ ∂μ) x = ∫⁻ x, f x ∂Measure.pi μ := by
  obtain ⟨y, hy⟩ := lmarginal_union_ae μ f hf (disjoint_compl_right (a := s)) |>.exists
  rw [lintegral_eq_lmarginal_univ y, ← Finset.union_compl, hy]
  grind [lmarginal_congr', lmarginal_congr, Finset.mem_compl, DependsOn]

theorem lmarginal_compl_lmarginal [Fintype δ] [∀ i, NeZero (μ i)] (f : (∀ i, X i) → ℝ≥0∞)
    (hf : AEMeasurable f (.pi μ)) : (∫⋯∫⁻_sᶜ, ∫⋯∫⁻_s, f ∂μ ∂μ) x = ∫⁻ x, f x ∂Measure.pi μ := by
  simpa using lmarginal_lmarginal_compl f hf (s := sᶜ)

theorem lmarginal_image [DecidableEq δ'] {e : δ' → δ} (he : Injective e) (s : Finset δ')
    {f : (∀ i, X (e i)) → ℝ≥0∞} (hf : Measurable f) (x : ∀ i, X i) :
      (∫⋯∫⁻_s.image e, f ∘ (· ∘' e) ∂μ) x = (∫⋯∫⁻_s, f ∂μ ∘' e) (x ∘' e) := by
  have h : Measurable ((· ∘' e) : (∀ i, X i) → _) :=
    measurable_pi_iff.mpr <| fun i ↦ measurable_pi_apply (e i)
  induction s using Finset.induction generalizing x with
  | empty => simp
  | insert _ _ hi ih =>
    rw [image_insert, lmarginal_insert _ (hf.comp h) (he.mem_finset_image.not.mpr hi),
      lmarginal_insert _ hf hi]
    simp_rw [ih, ← update_comp_eq_of_injective' x he]

theorem lmarginal_update_of_notMem {i : δ}
    {f : (∀ i, X i) → ℝ≥0∞} (hf : Measurable f) (hi : i ∉ s) (x : ∀ i, X i) (y : X i) :
    (∫⋯∫⁻_s, f ∂μ) (Function.update x i y) = (∫⋯∫⁻_s, f ∘ (Function.update · i y) ∂μ) x := by
  induction s using Finset.induction generalizing x with
  | empty => simp
  | insert i' s hi' ih =>
    rw [lmarginal_insert _ hf hi', lmarginal_insert _ (hf.comp measurable_update_left) hi']
    have hii' : i ≠ i' := mt (by rintro rfl; exact mem_insert_self i s) hi
    simp_rw [update_comm hii', ih (mt Finset.mem_insert_of_mem hi)]

theorem lmarginal_eq_of_subset {f g : (∀ i, X i) → ℝ≥0∞} (hst : s ⊆ t)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_s, g ∂μ) :
    ∫⋯∫⁻_t, f ∂μ = ∫⋯∫⁻_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst, lmarginal_union' μ f hf disjoint_sdiff,
    lmarginal_union' μ g hg disjoint_sdiff, hfg]

theorem lmarginal_le_of_subset {f g : (∀ i, X i) → ℝ≥0∞} (hst : s ⊆ t)
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ ≤ ∫⋯∫⁻_s, g ∂μ) :
    ∫⋯∫⁻_t, f ∂μ ≤ ∫⋯∫⁻_t, g ∂μ := by
  rw [← union_sdiff_of_subset hst, lmarginal_union' μ f hf disjoint_sdiff,
    lmarginal_union' μ g hg disjoint_sdiff]
  exact lmarginal_mono hfg

theorem lintegral_eq_of_lmarginal_eq [Fintype δ] (s : Finset δ) {f g : (∀ i, X i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ = ∫⋯∫⁻_s, g ∂μ) :
    ∫⁻ x, f x ∂Measure.pi μ = ∫⁻ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, X i) with h | ⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty]
  simp_rw [lintegral_eq_lmarginal_univ x, lmarginal_eq_of_subset (Finset.subset_univ s) hf hg hfg]

theorem lintegral_le_of_lmarginal_le [Fintype δ] (s : Finset δ) {f g : (∀ i, X i) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hfg : ∫⋯∫⁻_s, f ∂μ ≤ ∫⋯∫⁻_s, g ∂μ) :
    ∫⁻ x, f x ∂Measure.pi μ ≤ ∫⁻ x, g x ∂Measure.pi μ := by
  rcases isEmpty_or_nonempty (∀ i, X i) with h | ⟨⟨x⟩⟩
  · simp_rw [lintegral_of_isEmpty, le_rfl]
  simp_rw [lintegral_eq_lmarginal_univ x, lmarginal_le_of_subset (Finset.subset_univ s) hf hg hfg x]

end LMarginal

end MeasureTheory
