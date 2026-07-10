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
* Similarly, `lmarginal_union_ae` gives a a.e.-equality ofthis under the weaker assumption
  that `f` is a.e.-measurable.
* If `s` and `t` are complements, then we can upgrade this to an actual equality again, see
  `lmarginal_lmarginal_compl`

## Implementation notes

The function `f` can have an arbitrary product as its domain (even infinite products), but the
set `s` of integration variables is a `Finset`. We are assuming that the function `f` is measurable
for most of this file.

Some results require that `f` is `AEMeasurable`, in which case we do have to assume that the
there are finitely many factors in the product.
Even to state that `f` is AEMeasurable as a function on finitely many coordinates we need to assume
that there are finitely many factors
-/

@[expose] public section

#click_suggestions

open scoped ENNReal
open Set Function Equiv Finset

noncomputable section

namespace MeasureTheory

open Measure

section LMarginal

variable {δ δ' : Type*} {X : δ → Type*} [∀ i, MeasurableSpace (X i)]
variable {μ : ∀ i, Measure (X i)} [DecidableEq δ]
variable {s t : Finset δ} {f : (∀ i, X i) → ℝ≥0∞} {x : ∀ i, X i}

section Move


-- move
lemma _root_.AEMeasurable.prodMk_left {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite ν]
    {f : α × β → ℝ≥0∞} (hf : AEMeasurable f (μ.prod ν)) :
    ∀ᵐ x ∂μ, AEMeasurable (fun y ↦ f (x, y)) ν := by
  obtain ⟨g, hg, hfg⟩ := hf
  filter_upwards [MeasureTheory.Measure.ae_ae_eq_curry_of_prod hfg] with x hx
  refine AEMeasurable.congr ?_ hx.symm
  exact hg.comp (measurable_const.prodMk measurable_id') |>.aemeasurable

-- move
variable {δ' : Type*} in
@[simps]
def _root_.Equiv.finsetCoeCongr {s t : Finset δ'} (h : s = t) :
    s ≃ t where
  toFun i := ⟨i, h ▸ i.2⟩
  invFun i := ⟨i, h ▸ i.2⟩
  left_inv i := by ext; rfl
  right_inv i := by ext; rfl

-- move
variable {δ' : Type*} in
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

-- -- Ok if we add these too?
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
    {f : (∀ i : ↥sᶜ, α i) × (∀ i : s, α i)} {i : ι} (hi : i ∈ s) :
    piFinsetComplUnion α s f i = f.2 ⟨i, hi⟩ :=
  Equiv.piFinsetUnion_right α disjoint_compl_left hi <| Finset.mem_union_right _ hi

-- move
theorem measurePreserving_piFinsetComplUnion [Fintype δ] [∀ i, SigmaFinite (μ i)]
    (s : Finset δ) :
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
  · simpa [updateFinset, hi] using piFinsetComplUnion_eq_of_mem (f := (x.1, y)) hi |>.symm
  · simp only [updateFinset, hi, ↓reduceDIte, piFinsetComplUnion_eq_of_notMem hi]

variable {δ' : Type*} (π : δ' → Type*) [DecidableEq δ'] in
lemma _root_.Function.involutive_updateFinset (s : Finset δ') :
    Involutive fun z : (∀ i, π i) × ∀ i : s, π i ↦ (updateFinset z.1 s z.2, (z.1 ·)) := by
  intro z
  ext i <;> simp +contextual [updateFinset]

variable {δ' : Type*} (π : δ' → Type*) [DecidableEq δ'] in
/-- The equivalence that sends `(x, y, z)` to `(z, y, x)`, where `(x, y) : ∀ i, π i` with `x` the
components in `s` and `y` the components not in `s`. -/
@[simps]
def _root_.Equiv.piFinsetSwap (s : Finset δ') :
    ((∀ i, π i) × ∀ i : s, π i) ≃ (∀ i, π i) × ∀ i : s, π i where
      toFun z := (updateFinset z.1 s z.2, (z.1 ·))
      invFun z := (updateFinset z.1 s z.2, (z.1 ·))
      left_inv := involutive_updateFinset π s
      right_inv := involutive_updateFinset π s

variable {δ' : Type*} (π : δ' → Type*) [(i : δ') → MeasurableSpace (π i)]
  [DecidableEq δ'] in
/-- The measurable equivalence that sends `(x, y, z)` to `(z, y, x)`, where `(x, y) : ∀ i, π i`
with `x` the components in `s` and `y` the components not in `s`. -/
def _root_.MeasurableEquiv.piFinsetSwap (s : Finset δ') :
    ((∀ i, π i) × ∀ i : s, π i) ≃ᵐ (∀ i, π i) × ∀ i : s, π i where
  toEquiv := Equiv.piFinsetSwap π s
  measurable_toFun := by rw [funext <| Equiv.piFinsetSwap_apply _ _]; fun_prop
  measurable_invFun := by rw [funext <| Equiv.piFinsetSwap_symm_apply _ _]; fun_prop

variable {δ' : Type*} (π : δ' → Type*) [(i : δ') → MeasurableSpace (π i)]
  [DecidableEq δ'] in
lemma _root_.MeasurableEquiv.piFinsetSwap_apply (s : Finset δ') (x : (∀ i, π i) × ∀ i : s, π i) :
    MeasurableEquiv.piFinsetSwap π s x = Equiv.piFinsetSwap π s x := rfl

variable {δ' : Type*} (π : δ' → Type*) [DecidableEq δ'] {s : Finset δ'} in
theorem preimage_piFinsetSwap (u : ∀ i, Set (π i)) (v : ∀ i : s, Set (π i)) :
    Equiv.piFinsetSwap π s ⁻¹' Set.univ.pi u ×ˢ Set.univ.pi v =
    Set.univ.pi (updateFinset u s v) ×ˢ Set.univ.pi (fun i : s ↦ u i) := by
  ext x
  simp_rw [Set.mem_preimage, piFinsetSwap_apply]
  grind [updateFinset]

variable {ι : Type*} [DecidableEq ι] [Fintype ι] in
lemma filter_univ_mem (s : Finset ι) : ({i | i ∈ s} : Finset ι) = s := by simp

variable {ι : Type*} [DecidableEq ι] [Fintype ι] in
@[simp]
lemma filter_univ_notMem (s : Finset ι) : ({i | i ∉ s} : Finset ι) = sᶜ := by
  simp [← Finset.mem_compl]

variable {δ' M : Type*} (π : δ' → Type*) [DecidableEq δ'] [CommMonoid M] in
/-- A product involving `updateFinset` can be split up -/
theorem prod_updateFinset_eq [Fintype δ'] {s : Finset δ'}
    (f : ∀ i, π i → M)
    (x : ∀ i, π i) (y : ∀ i : s, π i) :
    ∏ i, f i (updateFinset x s y i) =
    (∏ i ∈ s.attach, f i (y i)) * ∏ i ∈ sᶜ, f i (x i) := by
  simp_rw [updateFinset, apply_dite, prod_dite, univ_eq_attach,
    prod_attach (f := fun i ↦ f i (x i)), filter_univ_notMem]
  congr! <;> simp

variable {δ' M : Type*} {π π' : δ' → Type*} [DecidableEq δ'] [CommMonoid M] in
/-- Two different ways to write `(∏ i, F i (f i) (x i)) * ∏ i, F i (g i) (y i)` using
`updateFinset` are equal. -/
theorem prod_updateFinset_mul_prod_eq [Fintype δ'] {s : Finset δ'}
    (F : ∀ i, π i → π' i → M)
    (f : ∀ i, π i) (g : ∀ i : s, π i)
    (x : ∀ i, π' i) (y : ∀ i : s, π' i) :
    (∏ i, F i (updateFinset f s g i) (x i)) * ∏ i ∈ s.attach, F i (f i) (y i) =
    (∏ i, F i (f i) (updateFinset x s y i)) * ∏ i ∈ s.attach, F i (g i) (x i) := by
  rw [prod_updateFinset_eq, prod_updateFinset_eq (f := fun (i : δ') (f : π i) ↦ F i f (x i))]
  grind only

variable [∀ i, SigmaFinite (μ i)]

variable (μ) in
theorem map_piFinsetSwap [Fintype δ] (ν : ∀ i : s, Measure (X i)) [∀ i, SigmaFinite (ν i)] :
    Measure.map (MeasurableEquiv.piFinsetSwap X s) (.prod (.pi μ) (.pi ν)) =
      .prod (.pi <| updateFinset μ s ν) (.pi (μ ·)) := by
  have : ∀ i, SigmaFinite (updateFinset μ s ν i) := by grind [updateFinset]
  apply Measure.prod_eq_generateFrom generateFrom_pi generateFrom_pi isPiSystem_pi isPiSystem_pi
    ?_ ?_ ?_ |>.symm
  · exact .pi fun i ↦ (updateFinset μ s ν i).toFiniteSpanningSetsIn
  · exact .pi fun i : s ↦ (μ i).toFiniteSpanningSetsIn
  simp_rw [Set.mem_image, Set.mem_pi, Set.mem_univ, mem_setOf_eq, forall_const,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, pi_pi]
  intro u hu v hv
  simp_rw [map_apply (MeasurableEquiv.measurable _) (.prod (.univ_pi hu) (.univ_pi hv)),
    funext <| MeasurableEquiv.piFinsetSwap_apply _ _, preimage_piFinsetSwap, prod_prod,
    pi_pi, univ_eq_attach, prod_updateFinset_mul_prod_eq]

variable {ι : Type*} (π : ι → Type*) [DecidableEq ι] in
@[simp]
lemma updateFinsetSelf (x : ∀ i, π i) (s : Finset ι) : updateFinset x s (x ·) = x := by
  simp [updateFinset_def]

-- move
variable (μ) in
theorem measurePreserving_piFinsetSwap [Fintype δ] (s : Finset δ) :
    MeasurePreserving (MeasurableEquiv.piFinsetSwap X s)
      (.prod (.pi μ) (.pi (μ ·)))
      (.prod (.pi μ) (.pi (μ ·))) :=
  ⟨MeasurableEquiv.measurable _, by rw [map_piFinsetSwap, updateFinsetSelf]⟩

-- move
variable (μ) in
lemma quasiMeasurePreserving_updateFinset [Fintype δ] :
  QuasiMeasurePreserving
    (fun a : ((i : δ) → X i) × ((i : s) → X i) ↦ updateFinset a.1 s a.2)
    ((Measure.pi μ).prod (Measure.pi (μ ·))) (Measure.pi μ) := by
  convert quasiMeasurePreserving_fst.comp
    (measurePreserving_piFinsetSwap μ s).quasiMeasurePreserving
  rfl

variable (s) in
lemma _root_.AEMeasurable.comp_updateFinset [Fintype δ] (hf : AEMeasurable f (.pi μ)) :
    AEMeasurable (uncurry (f <| updateFinset · s ·))
      (Measure.pi μ |>.prod <| Measure.pi (μ ·)) :=
  hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_updateFinset μ)

omit [DecidableEq δ] in
lemma Measure.pi_eq_zero_iff [Fintype δ] : Measure.pi μ = 0 ↔ ∃ i, μ i = 0 := by
  simp_rw [← Measure.measure_univ_eq_zero, Measure.pi_univ, Finset.prod_eq_zero_iff]
  simp

omit [DecidableEq δ] in
lemma Measure.neZero_pi_iff [Fintype δ] : NeZero (Measure.pi μ) ↔ ∀ i, NeZero (μ i) := by
  simp_rw [neZero_iff, ne_eq, Measure.pi_eq_zero_iff, not_exists]

instance [Fintype δ] [∀ i, NeZero (μ i)] : NeZero (Measure.pi μ) :=
  neZero_pi_iff.mpr ‹_›

variable {ι : Type*} {π : ι → Type*} [DecidableEq ι] {s t : Finset ι} in
lemma updateFinset_eq_of_subset (h : t ⊆ s) (x : ∀ i, π i) (y : ∀ i : t, π i) :
    updateFinset x t y =
    updateFinset x s (updateFinset (x ·) (t.preimage Subtype.val injOn_subtype_val)
      fun i ↦ y ⟨i, Finset.mem_preimage.mp i.2⟩) := by
  grind [updateFinset_def, Finset.mem_preimage]

-- -- to Constructions.Pi
-- omit [DecidableEq δ] in
-- theorem QuasiMeasurePreserving.dcomp_of_injective [Fintype δ] [Fintype δ']
--     {e : δ' → δ} (he : Injective e) :
--     QuasiMeasurePreserving (· ∘' e) (.pi μ) (.pi (μ ∘' e)) := by
--   refine ⟨by fun_prop, AbsolutelyContinuous.mk fun s hs h2s => ?_⟩
--   rw [map_apply (by fun_prop) hs]
--   sorry

omit [DecidableEq δ] in
variable (μ) in
theorem QuasiMeasurePreserving.piCoe [Fintype δ] (s : Finset δ) :
    QuasiMeasurePreserving (fun (x : ∀ i, X i) (i : s) ↦ x i) (.pi μ) (.pi (μ ·)) := by
  classical
  convert quasiMeasurePreserving_snd.comp
    (measurePreserving_piFinsetComplUnion (μ := μ) s).symm.quasiMeasurePreserving
  rfl

omit [DecidableEq δ] in
variable (μ) in
-- only finish if useful
theorem QuasiMeasurePreserving.piCoe_of_subset {s t : Finset δ} (h : t ⊆ s) :
    QuasiMeasurePreserving (fun (x : ∀ i : s, X i) (i : t) ↦ x ⟨i, h i.2⟩)
      (.pi (μ ·)) (.pi (μ ·)) := by
  classical
  have := QuasiMeasurePreserving.piCoe (fun i : s ↦ μ i)
      (t.attach.map (Subtype.impEmbedding _ _ h))
  let e : ↥(Finset.map (Subtype.impEmbedding (fun x ↦ x ∈ t) (fun x ↦ x ∈ s) h) t.attach)
      ≃ t := by
    convert Equiv.subtypeSubtypeEquivSubtype _ with x
    · grind [Subtype.exists]
    grind only [subset_iff]
  have h2 := measurePreserving_piCongrLeft (fun i : (_ : Finset _) ↦ μ i) e.symm
    |>.symm.quasiMeasurePreserving.comp this
  convert this
  simp
  -- congr!
  sorry
  -- simp
  -- convert quasiMeasurePreserving_snd.comp
  --   (measurePreserving_piFinsetComplUnion (μ := μ) s).symm.quasiMeasurePreserving
  -- rfl

omit [DecidableEq δ] in
-- set_option pp.funBinderTypes true in
theorem quasiMeasurePreserving_dcomp [Fintype δ] [Fintype δ']
    {e : δ' → δ} (he : Injective e) :
    QuasiMeasurePreserving (fun x : ∀ i, X i ↦ x ∘' e)
    (.pi μ) (.pi fun i' ↦ μ (e i')) := by
  classical
  have : Measurable (fun x : ∀ i, X i ↦ x ∘' e) :=
    measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (e i)
  refine ⟨this, ?_⟩
  refine .mk fun s hs hμs ↦ ?_
  rw [map_apply this hs]
  -- this could be generalized as a separate lemma.
  rw [← measurePreserving_piFinsetComplUnion (μ := μ) (Finset.univ.image e) |>.map_eq]
  have : ∀ i, e i ∈ Finset.univ.image e := fun i ↦ Finset.mem_image_of_mem e (Finset.mem_univ i)
  let e' : δ' ≃ Finset.univ.image e := calc
    δ' ≃ range e := ofInjective e he
    _ ≃ Finset.univ.image e := subtypeEquivRight (by simp)
  have e'_def x : (e' x).1 = e x := rfl
  have e'_def' x : e' x = ⟨e x, this x⟩ := rfl
  have e'_symm x : e'.symm ⟨e x, this x⟩ = x := by simp [e', subtypeEquivRight]
  rw [map_apply sorry sorry, preimage_preimage]
  simp_rw [funext (dcomp.eq_1 _ _)]
  simp_rw [MeasurableEquiv.piFinsetComplUnion_apply, piFinsetComplUnion_eq_of_mem (this _)]
  rw [← preimage_preimage
    (g := (fun (x : ∀ i : Finset.univ.image e, X i) (i : δ') ↦ x ⟨e i, this i⟩)) (f := Prod.snd),
    ← univ_prod, prod_prod]
  rw [← pi_map_piCongrLeft e' (μ ·), ]
  rw [map_apply sorry sorry, preimage_preimage]
  sorry
  -- conv => enter [1, 2, 2, 1, x, i]; rw! [← e'_def'] -- kernel error
  -- simp_rw [MeasurableEquiv.piCongrLeft_apply_apply]
  -- convert (postTransparency := .default) mul_zero _


theorem updateFinset_image {δ : Type u_1} {δ' : Type u_2}
    {X : δ → Type u_3} [DecidableEq δ] [DecidableEq δ']
    {e : δ' → δ} (he : Injective e) {s : Finset δ'} (x : ∀ i, X i)
    (y : ∀ (i : s.image e), X i) (i : δ') :
    updateFinset x (s.image e) y (e i) =
    updateFinset (x ∘' e) s (fun j ↦ y ⟨e j, (Injective.mem_finset_image he).mpr j.2⟩) i := by
  by_cases hi : i ∈ s
  · have : e i ∈ s.image e := (Injective.mem_finset_image he).mpr hi
    simp [updateFinset_def, hi, this]
  · have : e i ∉ s.image e := he.mem_finset_image.not.mpr hi
    simp [updateFinset_def, hi, this]

end Move

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

@[simp] theorem lmarginal_zero : ∫⋯∫⁻_s, 0 ∂μ = 0 := by
  simp_rw [funext_iff, lmarginal, Pi.zero_apply, lintegral_zero, implies_true]

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

variable {μ} in
theorem lmarginal_eq_zero_iff (hf : Measurable f) :
    (∫⋯∫⁻_s, f ∂μ) x = 0 ↔
    (fun y : ∀ i : s, X i ↦ f (updateFinset x s y)) =ᵐ[Measure.pi (fun i : s ↦ μ i)] 0 := by
  rw [lmarginal, lintegral_eq_zero_iff]
  fun_prop

variable {μ} [∀ i, SigmaFinite (μ i)]

theorem lmarginal_eq_zero_of_measure_eq_zero {i : δ} (hi : i ∈ s) (h : μ i = 0) :
    ∫⋯∫⁻_s, f ∂μ = 0 := by
  ext x
  refine lintegral_congr_ae ?_ |>.trans lintegral_zero
  rw [Measure.pi_eq_zero_iff.mpr ⟨⟨i, hi⟩, h⟩]
  simp_rw [Filter.EventuallyEq, Filter.Eventually, ae_zero, Filter.mem_bot]

theorem lmarginal_union_ae_apply (f : (∀ i, X i) → ℝ≥0∞)
    {x : (i : δ) → X i}
    (hx : AEMeasurable (fun y ↦ f (updateFinset x (s ∪ t) y)) (Measure.pi (μ ·)))
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

variable (μ) in
theorem lmarginal_union (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f)
    (hst : Disjoint s t) : ∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ := by
  ext1 x
  exact lmarginal_union_ae_apply f (hf.comp measurable_updateFinset).aemeasurable hst

-- todo: rename to `lmarginal_union_rev` or something
variable (μ) in
theorem lmarginal_union' (f : (∀ i, X i) → ℝ≥0∞) (hf : Measurable f) {s t : Finset δ}
    (hst : Disjoint s t) : ∫⋯∫⁻_s ∪ t, f ∂μ = ∫⋯∫⁻_t, ∫⋯∫⁻_s, f ∂μ ∂μ := by
  rw [Finset.union_comm, lmarginal_union μ f hf hst.symm]

variable (μ) in
@[simp] theorem lmarginal_univ [Fintype δ] {f : (∀ i, X i) → ℝ≥0∞} :
    ∫⋯∫⁻_univ, f ∂μ = fun _ => ∫⁻ x, f x ∂Measure.pi μ := by
  let e : { j // j ∈ Finset.univ } ≃ δ := Equiv.subtypeUnivEquiv mem_univ
  ext1 x
  simp_rw [lmarginal, measurePreserving_piCongrLeft μ e |>.lintegral_map_equiv, updateFinset_def]
  simp
  rfl

section Fintype
variable [Fintype δ]

/-- The function `f` is a.e.-measurable as a function on the coordinates in `f`, for almost all
values in the remaining arguments. -/
def AEMeasurableWRT (f : (∀ i, X i) → ℝ≥0∞) (s : Finset δ) (μ : ∀ i, Measure (X i)) :
    Prop :=
  ∀ᵐ x ∂Measure.pi μ, AEMeasurable (f <| updateFinset x s ·) (Measure.pi (μ ·))

lemma _root_.AEMeasurable.aemeasurableWRT (hf : AEMeasurable f (.pi μ)) :
    AEMeasurableWRT f s μ :=
  hf.comp_updateFinset s |>.prodMk_left

theorem AEMeasurableWRT.image [Fintype δ'] [DecidableEq δ'] {e : δ' → δ} (he : Injective e)
    {s : Finset δ'} {f : (∀ i, X (e i)) → ℝ≥0∞} (hf : AEMeasurableWRT f s (μ ∘' e)) :
    AEMeasurableWRT (f ∘ (· ∘' e)) (s.image e) μ := by
  have h : Measurable ((· ∘' e) : (∀ i, X i) → _) :=
    measurable_pi_iff.mpr fun i ↦ measurable_pi_apply (e i)
  have : QuasiMeasurePreserving (fun x : ∀ i, X i ↦ x ∘' e)
    (Measure.pi μ) (Measure.pi fun i' ↦ μ (e i')) :=
      sorry
  filter_upwards [this.ae hf] with x hx
  convert hx.comp_quasiMeasurePreserving
    (f := fun (z : ∀ i : s.image e, X i) (i : s) ↦
      z ⟨e i.1, (Injective.mem_finset_image he).mpr i.2⟩) ?_
  · simp_rw [funext (Function.dcomp.eq_1 _ _), comp_apply]
    congr
    ext i
    rw [updateFinset_image he]
  sorry

open scoped Set.Notation in
/-
Proof idea:
The following are maps are quasi-measure-preserving:
(∀ i, X i) × (∀ i : s, X i) -> 1 ⊗ split
(∀ i, X i) × (∀ i : s \ t, X i) × (∀ i : t, X i) -> swap ⊗ 1
(∀ i, X i) × (∀ i : s \ t, X i) × (∀ i : t, X i) -> π₁ ⊗ π₃
(∀ i, X i) × (∀ i : t, X i)
Let's call the composition g.

Equivalently
(∀ i, X i) × (∀ i : s, X i) -> swap
(∀ i, X i) × (∀ i : t, X i) × (∀ i : s \ t, X i) -> 1 ⊗ split
(∀ i, X i) × (∀ i : t, X i) × (∀ i : s \ t, X i) -> swap ⊗ 1
(∀ i, X i) × (∀ i : t, X i) × (∀ i : s \ t, X i) -> π₁ ⊗ π₂
(∀ i, X i) × (∀ i : t, X i)

Known: ∀ᵐx, h(g(x, ·)) is a.e. measurable. To prove: ∀ᵐx, h(x, ·) is a.e. measurable, where
`h = (f <| updateFinset · t ·)`
Need to somehow encode that `h` doesn't depend on the values in `∀ i : s \ t, X i`.
-/
lemma AEMeasurableWRT.mono (hf : AEMeasurableWRT f s μ) (h : t ⊆ s) :
    AEMeasurableWRT f t μ := by
  filter_upwards [hf] with x hx

  -- have' g := (measurePreserving_piFinsetSwap μ t).quasiMeasurePreserving.comp
  --   (QuasiMeasurePreserving.prodMap (.id _) <| QuasiMeasurePreserving.piCoe_of_subset μ h)
  --   |>.comp (measurePreserving_piFinsetSwap μ s).quasiMeasurePreserving
  simp_rw [updateFinset_eq_of_subset h]


  sorry -- should be true, but ugly

set_option backward.isDefEq.respectTransparency false in
lemma aemeasurableWRT_univ_iff [∀ i, NeZero (μ i)] :
    AEMeasurableWRT f univ μ ↔ AEMeasurable f (.pi μ) := by
  refine ⟨fun h ↦ ?_, (·.aemeasurableWRT)⟩
  simp_rw [AEMeasurableWRT, updateFinset_univ, Filter.eventually_const] at h
  convert h.comp_quasiMeasurePreserving
      (measurePreserving_piCongrLeft (μ ·) Equiv.finsetUniv).symm.quasiMeasurePreserving
  rfl -- simp doesn't like this, since small variations make this reducibly type incorrect.

lemma _root_.AEMeasurable.marginal (hf : AEMeasurable f (.pi μ)) :
    AEMeasurable (∫⋯∫⁻_ s, f ∂μ) (Measure.pi (μ ·)) := by
  apply AEMeasurable.lintegral_prod_right
  exact hf.comp_quasiMeasurePreserving (quasiMeasurePreserving_updateFinset μ)

-- todo: lmarginal_insert_ae, lmarginal_erase_ae, ...
theorem lmarginal_union_ae (hf : AEMeasurableWRT f (s ∪ t) μ)
    (hst : Disjoint s t) : ∫⋯∫⁻_s ∪ t, f ∂μ =ᵐ[Measure.pi μ] ∫⋯∫⁻_s, ∫⋯∫⁻_t, f ∂μ ∂μ := by
  filter_upwards [hf] with x hx
  exact lmarginal_union_ae_apply f hx hst

theorem lintegral_eq_lmarginal_univ (x : ∀ i, X i) :
    ∫⁻ x, f x ∂Measure.pi μ = (∫⋯∫⁻_univ, f ∂μ) x := by simp

theorem lmarginal_lmarginal_compl (f : (∀ i, X i) → ℝ≥0∞)
    (hf : AEMeasurable f (.pi μ)) : (∫⋯∫⁻_s, ∫⋯∫⁻_sᶜ, f ∂μ ∂μ) x = ∫⁻ x, f x ∂Measure.pi μ := by
  by_cases h : ∀ i, NeZero (μ i); swap
  · simp_rw [not_forall, not_neZero] at h
    obtain ⟨i, h⟩ := h
    by_cases hi : i ∈ s
    · rw [lmarginal_eq_zero_of_measure_eq_zero hi h, Measure.pi_eq_zero_iff.mpr ⟨i, h⟩,
        lintegral_zero_measure, Pi.zero_apply]
    · rw [lmarginal_eq_zero_of_measure_eq_zero (Finset.mem_compl.mpr hi) h, lmarginal_zero,
        Measure.pi_eq_zero_iff.mpr ⟨i, h⟩, lintegral_zero_measure, Pi.zero_apply]
  obtain ⟨y, hy⟩ := lmarginal_union_ae hf.aemeasurableWRT (disjoint_compl_right (a := s)) |>.exists
  rw [lintegral_eq_lmarginal_univ y, ← Finset.union_compl, hy]
  grind [lmarginal_congr', lmarginal_congr, Finset.mem_compl, DependsOn]

theorem lmarginal_compl_lmarginal (f : (∀ i, X i) → ℝ≥0∞)
    (hf : AEMeasurable f (.pi μ)) : (∫⋯∫⁻_sᶜ, ∫⋯∫⁻_s, f ∂μ ∂μ) x = ∫⁻ x, f x ∂Measure.pi μ := by
  simpa using lmarginal_lmarginal_compl f hf (s := sᶜ)

end Fintype

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
