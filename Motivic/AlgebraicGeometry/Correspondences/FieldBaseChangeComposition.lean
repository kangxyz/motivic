/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.FieldBaseChangeIncidenceTor
public import Motivic.AlgebraicGeometry.Correspondences.FieldBaseChangeIncidenceCycle
public import Motivic.AlgebraicGeometry.Correspondences.FieldBaseChangeCompositionPushforward
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Actual signed correspondence composition under arbitrary field change

Component incidence cycles are compared inside the entire new incidence, with
all-point coefficients and all finite-image collisions retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic

namespace FiniteCorrespondenceGenerator

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (a : genericPoints (A.fieldBaseChangeSupport φ))
  (b : genericPoints (B.fieldBaseChangeSupport φ))

/-- The component-incidence map commutes with the actual final finite projection. -/
@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentIncidenceToWhole_map :
    A.fieldBaseChangeComponentIncidenceToWhole φ B a b ≫ A.fieldBaseChangeIncidenceMap φ B =
      (A.fieldBaseChangeComponentGenerator φ a).incidenceMap
        (B.fieldBaseChangeComponentGenerator φ b) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, fieldBaseChangeIncidenceMap_fst,
      fieldBaseChangeComponentIncidenceToWhole_fst_assoc,
      fieldBaseChangeComponentToWhole_projection, incidenceMap_fst, incidenceSource]
  · simp only [Category.assoc, fieldBaseChangeIncidenceMap_snd,
      fieldBaseChangeComponentIncidenceToWhole_snd_assoc,
      fieldBaseChangeComponentToWhole_targetProjection, incidenceMap_snd, incidenceTarget]

/-- The actual pair Tor cycle included into the entire new incidence. -/
def fieldBaseChangePairTorCycle : IntegralCycle (A.fieldBaseChangeIncidence φ B) :=
  IntegralCycle.finitePushforward (A.fieldBaseChangeComponentIncidenceToWhole φ B a b)
    (IntegralCycle.ofGenericCoefficients
      ((A.fieldBaseChangeComponentGenerator φ a).incidence
        (B.fieldBaseChangeComponentGenerator φ b))
      ((A.fieldBaseChangeComponentGenerator φ a).incidenceTorCoefficient
        (S := Spec (.of L)) (B.fieldBaseChangeComponentGenerator φ b)))

/-- At an actual lift the closed immersion contributes exactly its Tor coefficient. -/
theorem fieldBaseChangePairTorCycle_coefficient_of_lift
    (v : genericPoints ((A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b))) :
    IntegralCycle.toPoints (A.fieldBaseChangePairTorCycle φ B a b)
      (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v.1) =
      (A.fieldBaseChangeComponentGenerator φ a).incidenceTorCoefficient
        (S := Spec (.of L)) (B.fieldBaseChangeComponentGenerator φ b) v := by
  classical
  let := IntegralCycle.genericPointFintype
    ((A.fieldBaseChangeComponentGenerator φ a).incidence (B.fieldBaseChangeComponentGenerator φ b))
  rw [fieldBaseChangePairTorCycle,
    IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  unfold IntegralCycle.genericPushforwardCoefficient
  rw [Finset.sum_eq_single v]
  · simp only [ite_true, residueDegree_of_surjectiveOnStalks, Nat.cast_one, mul_one]
  · intro w _ hw
    rw [ite_eq_right]
    intro h
    exact hw (Subtype.ext
      ((A.fieldBaseChangeComponentIncidenceToWhole φ B a b).isEmbedding.injective h))
  · simp

/-- No actual lift means no coefficient, including points outside every pair component. -/
theorem fieldBaseChangePairTorCycle_coefficient_of_no_lift
    (w : A.fieldBaseChangeIncidence φ B)
    (hno : ¬ ∃ v : genericPoints ((A.fieldBaseChangeComponentGenerator φ a).incidence
        (B.fieldBaseChangeComponentGenerator φ b)),
      A.fieldBaseChangeComponentIncidenceToWhole φ B a b v.1 = w) :
    IntegralCycle.toPoints (A.fieldBaseChangePairTorCycle φ B a b) w = 0 := by
  classical
  let := IntegralCycle.genericPointFintype
    ((A.fieldBaseChangeComponentGenerator φ a).incidence (B.fieldBaseChangeComponentGenerator φ b))
  rw [fieldBaseChangePairTorCycle,
    IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  unfold IntegralCycle.genericPushforwardCoefficient
  apply Finset.sum_eq_zero
  intro v _
  exact ite_eq_right (fun hv => hno ⟨v, hv⟩)

/-- Proven generic preservation gives vanishing at every nongeneric whole-incidence point. -/
theorem fieldBaseChangePairTorCycle_coefficient_of_not_generic
    (w : A.fieldBaseChangeIncidence φ B) (hw : w ∉ genericPoints (A.fieldBaseChangeIncidence φ B)) :
    IntegralCycle.toPoints (A.fieldBaseChangePairTorCycle φ B a b) w = 0 := by
  apply A.fieldBaseChangePairTorCycle_coefficient_of_no_lift φ B a b w
  rintro ⟨v, hv⟩
  exact hw (hv ▸ A.fieldBaseChangeComponentIncidenceToWhole_generic φ B a b v)

/-- Final finite pushforward is the actual generator-pair correspondence cycle. -/
theorem finitePushforward_fieldBaseChangePairTorCycle :
    IntegralCycle.finitePushforward (A.fieldBaseChangeIncidenceMap φ B)
      (A.fieldBaseChangePairTorCycle φ B a b) =
    FiniteCorrespondence.toIntegralCycle
      (f := ((SmoothSite.fieldBaseChange φ).obj X).hom)
      (g := ((SmoothSite.fieldBaseChange φ).obj Z).hom)
      ((A.fieldBaseChangeComponentGenerator φ a).incidenceTorCorrespondence L
        (X := (SmoothSite.fieldBaseChange φ).obj X)
        (Y := (SmoothSite.fieldBaseChange φ).obj Y)
        (Z := (SmoothSite.fieldBaseChange φ).obj Z)
        (B.fieldBaseChangeComponentGenerator φ b)) := by
  rw [fieldBaseChangePairTorCycle, ← AddMonoidHom.comp_apply,
    ← IntegralCycle.finitePushforward_comp]
  simp only [fieldBaseChangeComponentIncidenceToWhole_map]
  exact
    ((A.fieldBaseChangeComponentGenerator φ a).toIntegralCycle_incidenceTorCorrespondence L
      (X := (SmoothSite.fieldBaseChange φ).obj X)
      (Y := (SmoothSite.fieldBaseChange φ).obj Y)
      (Z := (SmoothSite.fieldBaseChange φ).obj Z)
      (B.fieldBaseChangeComponentGenerator φ b)).symm

omit a b in
/-- Biadditivity keeps both original support lengths in the whole pair-cycle sum. -/
theorem toIntegralCycle_fieldBaseChangeCycle_pairing :
    FiniteCorrespondence.toIntegralCycle
      (f := ((SmoothSite.fieldBaseChange φ).obj X).hom)
      (g := ((SmoothSite.fieldBaseChange φ).obj Z).hom)
      (FiniteCorrespondence.incidenceTorPairing L
        (X := (SmoothSite.fieldBaseChange φ).obj X)
        (Y := (SmoothSite.fieldBaseChange φ).obj Y)
        (Z := (SmoothSite.fieldBaseChange φ).obj Z)
        (A.fieldBaseChangeCycle φ) (B.fieldBaseChangeCycle φ)) =
    letI := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
    letI := IntegralCycle.genericPointFintype (B.fieldBaseChangeSupport φ)
    IntegralCycle.finitePushforward (A.fieldBaseChangeIncidenceMap φ B)
      (∑ a, ∑ b, ((genericMultiplicity a : ℤ) * (genericMultiplicity b : ℤ)) •
        A.fieldBaseChangePairTorCycle φ B a b) := by
  classical
  let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
  let := IntegralCycle.genericPointFintype (B.fieldBaseChangeSupport φ)
  rw [A.fieldBaseChangeCycle_eq_sum φ, B.fieldBaseChangeCycle_eq_sum φ]
  simp only [map_sum, AddMonoidHom.finsetSum_apply,
    FiniteCorrespondence.incidenceTorPairing_single, map_zsmul,
    finitePushforward_fieldBaseChangePairTorCycle]
  rw [Finset.sum_comm]

/-- The same original-list quotient Euler is the actual included pair-cycle coefficient. -/
theorem fieldBaseChangePairQuotientEuler_eq_coefficient
    (w : genericPoints (A.fieldBaseChangeIncidence φ B))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))))
    (hs : RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))) s)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w.1)).hom = Ideal.ofList s) :
    A.fieldBaseChangePairQuotientEuler φ B a b w s hker =
      IntegralCycle.toPoints (A.fieldBaseChangePairTorCycle φ B a b) w.1 := by
  classical
  by_cases hlift : ∃ v : genericPoints ((A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b)),
    A.fieldBaseChangeComponentIncidenceToWhole φ B a b v.1 = w.1
  · obtain ⟨v, hv⟩ := hlift
    have hc := A.fieldBaseChangePairTorCycle_coefficient_of_lift φ B a b v
    rw [hv] at hc
    exact (A.fieldBaseChangePairQuotientEuler_eq_tor φ B a b w v hv s hs hker).trans hc.symm
  · rw [A.fieldBaseChangePairQuotientEuler_eq_zero_of_no_lift φ B a b w hlift s hker,
      A.fieldBaseChangePairTorCycle_coefficient_of_no_lift φ B a b w.1 hlift]

omit a b in
/-- The actual weighted component-pair Tor cycles equal the entire field-changed
original Tor cycle, with nongeneric vanishing proved before point extensionality. -/
theorem fieldBaseChangeIncidenceTorCycle_eq_pair_sum :
    IntegralCycle.ofGenericCoefficients (A.fieldBaseChangeIncidence φ B)
      (fun w => A.incidenceTorCoefficient (S := Spec (.of k)) B
          (A.fieldBaseChangeIncidenceOriginalGeneric φ B w) *
        A.fieldBaseChangeIncidenceFiberMultiplicity φ B w) =
    letI := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
    letI := IntegralCycle.genericPointFintype (B.fieldBaseChangeSupport φ)
    ∑ a, ∑ b, ((genericMultiplicity a : ℤ) * (genericMultiplicity b : ℤ)) •
      A.fieldBaseChangePairTorCycle φ B a b := by
  classical
  let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
  let := IntegralCycle.genericPointFintype (B.fieldBaseChangeSupport φ)
  apply IntegralCycle.toPoints_injective
  ext w
  simp only [map_sum, map_zsmul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, zsmul_eq_mul, Int.cast_id]
  rw [IntegralCycle.toPoints_ofGenericCoefficients_apply]
  by_cases hw : w ∈ genericPoints (A.fieldBaseChangeIncidence φ B)
  · rw [dite_eq_left hw]
    obtain ⟨s, hs, hker⟩ := Diagonal.exists_regular_kernel_of_smooth Y.hom
      (A.fieldBaseChangeIncidenceMiddle φ B w)
    rw [← A.fieldBaseChangeMiddleKoszulCoefficient_eq φ B ⟨w, hw⟩ s hs hker]
    have hsum : A.fieldBaseChangeMiddleKoszulCoefficient φ B ⟨w, hw⟩ s hker =
        ∑ a, ∑ b, ((genericMultiplicity a : ℤ) * (genericMultiplicity b : ℤ)) *
          A.fieldBaseChangePairQuotientEuler φ B a b ⟨w, hw⟩ s hker := by
      exact A.fieldBaseChangeMiddleKoszulCoefficient_eq_component_pair_sum φ B ⟨w, hw⟩ s hker
    rw [hsum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [A.fieldBaseChangePairQuotientEuler_eq_coefficient φ B a b ⟨w, hw⟩ s hs hker]
  · rw [dite_eq_right hw]
    symm
    apply Finset.sum_eq_zero
    intro a _
    apply Finset.sum_eq_zero
    intro b _
    rw [A.fieldBaseChangePairTorCycle_coefficient_of_not_generic φ B a b w hw, mul_zero]

omit a b in
/-- Actual field change preserves generator composition, with every branch weight
and the original finite residue degrees retained. -/
theorem fieldBaseChange_incidenceTorCorrespondence :
    FiniteCorrespondence.fieldBaseChange (X := X) (Y := Z) φ
      (A.incidenceTorCorrespondence k B) =
    FiniteCorrespondence.incidenceTorPairing L
      (X := (SmoothSite.fieldBaseChange φ).obj X)
      (Y := (SmoothSite.fieldBaseChange φ).obj Y)
      (Z := (SmoothSite.fieldBaseChange φ).obj Z)
      (A.fieldBaseChangeCycle φ) (B.fieldBaseChangeCycle φ) := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_fieldBaseChangeCycle_pairing,
    ← fieldBaseChangeIncidenceTorCycle_eq_pair_sum]
  exact (A.finitePushforward_fieldBaseChangeIncidenceTorCycle φ B).symm

end FiniteCorrespondenceGenerator

namespace FiniteCorrespondence

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k}

/-- Unit input cycles recover the proved actual generator comparison. -/
theorem fieldBaseChange_incidenceTorPairing_cycle
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    (B : FiniteCorrespondenceGenerator Y.hom Z.hom) :
    fieldBaseChange (X := X) (Y := Z) φ
      (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) A.cycle B.cycle) =
    incidenceTorPairing L
      (X := (SmoothSite.fieldBaseChange φ).obj X)
      (Y := (SmoothSite.fieldBaseChange φ).obj Y)
      (Z := (SmoothSite.fieldBaseChange φ).obj Z)
      (fieldBaseChange (X := X) (Y := Y) φ A.cycle)
      (fieldBaseChange (X := Y) (Y := Z) φ B.cycle) := by
  simp only [incidenceTorPairing_cycle, fieldBaseChange_cycle]
  exact A.fieldBaseChange_incidenceTorCorrespondence φ B

/-- Arbitrary field change preserves composition of every signed correspondence,
including disconnected and empty smooth objects. -/
theorem fieldBaseChange_incidenceTorPairing
    (α : FiniteCorrespondence X.hom Y.hom) (β : FiniteCorrespondence Y.hom Z.hom) :
    fieldBaseChange (X := X) (Y := Z) φ
      (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) α β) =
    incidenceTorPairing L
      (X := (SmoothSite.fieldBaseChange φ).obj X)
      (Y := (SmoothSite.fieldBaseChange φ).obj Y)
      (Z := (SmoothSite.fieldBaseChange φ).obj Z)
      (fieldBaseChange (X := X) (Y := Y) φ α)
      (fieldBaseChange (X := Y) (Y := Z) φ β) := by
  have hright (A : FiniteCorrespondenceGenerator X.hom Y.hom) :
      (fieldBaseChange (X := X) (Y := Z) φ).comp
          (incidenceTorPairing k (X := X) (Y := Y) (Z := Z) A.cycle) =
        (incidenceTorPairing L
          (X := (SmoothSite.fieldBaseChange φ).obj X)
          (Y := (SmoothSite.fieldBaseChange φ).obj Y)
          (Z := (SmoothSite.fieldBaseChange φ).obj Z)
          (fieldBaseChange (X := X) (Y := Y) φ A.cycle)).comp
          (fieldBaseChange (X := Y) (Y := Z) φ) := by
    apply Finsupp.addHom_ext
    intro B n
    have hsingle : Finsupp.single B n = n • B.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hsingle, map_zsmul, map_zsmul]
    exact congrArg (fun γ => n • γ) (fieldBaseChange_incidenceTorPairing_cycle φ A B)
  have hleft :
      (fieldBaseChange (X := X) (Y := Z) φ).comp
          ((incidenceTorPairing k (X := X) (Y := Y) (Z := Z)).flip β) =
        ((incidenceTorPairing L
          (X := (SmoothSite.fieldBaseChange φ).obj X)
          (Y := (SmoothSite.fieldBaseChange φ).obj Y)
          (Z := (SmoothSite.fieldBaseChange φ).obj Z)).flip
          (fieldBaseChange (X := Y) (Y := Z) φ β)).comp
          (fieldBaseChange (X := X) (Y := Y) φ) := by
    apply Finsupp.addHom_ext
    intro A n
    have hsingle : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hsingle, map_zsmul, map_zsmul]
    exact congrArg (fun F => n • F β) (hright A)
  exact congrArg (fun F => F α) hleft

end FiniteCorrespondence

namespace Cor

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- The additive field-change functor on the actual category of signed finite
correspondences. Its composition law is the proved whole-incidence comparison. -/
def fieldBaseChange : Cor k ⥤ Cor L where
  obj X := ⟨(SmoothSite.fieldBaseChange φ).obj X.toSmoothSite⟩
  map {X Y} α := FiniteCorrespondence.fieldBaseChange
    (X := X.toSmoothSite) (Y := Y.toSmoothSite) φ α
  map_id X := FiniteCorrespondence.fieldBaseChange_componentIdentityCycle φ X.toSmoothSite
  map_comp α β := FiniteCorrespondence.fieldBaseChange_incidenceTorPairing φ α β

instance fieldBaseChange_additive : (fieldBaseChange φ).Additive where
  map_add := by
    intro X Y α β
    exact map_add (FiniteCorrespondence.fieldBaseChange
      (X := X.toSmoothSite) (Y := Y.toSmoothSite) φ) α β

/-- The functor acts by the same actual whole-support signed cycle map. -/
@[simp] theorem fieldBaseChange_map {X Y : Cor k} (α : X ⟶ Y) :
    (fieldBaseChange φ).map α = FiniteCorrespondence.fieldBaseChange
      (X := X.toSmoothSite) (Y := Y.toSmoothSite) φ α := rfl

/-- The bundled additive functor retains the established actual field-change action. -/
def fieldBaseChangeAdditiveFunctor : Cor k ⥤+ Cor L :=
  AdditiveFunctor.of (fieldBaseChange φ)

end Cor

end Motivic

