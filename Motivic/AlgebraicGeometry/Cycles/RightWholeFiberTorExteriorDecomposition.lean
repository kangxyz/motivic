/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorExteriorPushforward
public import Motivic.AlgebraicGeometry.Intersection.RightWholeFiberTorGeneric

/-!
# The actual right whole Tor source cycle and its original component exteriors

Apply the existing component decomposition to the original G,H incidence and
F.scheme over Spec k, then transport through the literal pullback symmetry.
The symmetry compares the ORIGINAL projection stalk maps as arrows; the existing
closed-fiber quotient/module engine therefore preserves their scalar actions and
nonreduced lengths. No reversal of correspondence generators is used.

The endpoint is on the identical actual right whole inverse-image open V. Its
cycle is the restriction of the signed sum of the literal F.scheme times each
original G,H point closure, pushed by its actual closed inclusion. All original
labels and exterior branches remain, including disconnected and empty cases.
There is no image-degree, remaining-diagonal, or associativity claim here.

Source-only candidate: no compilation, diagnostic success, or acceptance claimed.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.RightWholeFiberTorExteriorDecomposition

section ArrowTransport

variable {A B R T : CommRingCat.{u}} [IsLocalRing A] [IsLocalRing R]
  {g : A ⟶ B} {f : R ⟶ T} (e : Arrow.mk g ≅ Arrow.mk f)

omit [IsLocalRing A] [IsLocalRing R] in
/-- Both component maps of an arrow isomorphism have zero kernel, so their
literal scalar square satisfies the closed-fiber quotient engine's kernel condition. -/
theorem arrowIso_kernel :
    RingHom.ker e.hom.right.hom = (RingHom.ker e.hom.left.hom).map g.hom := by
  rw [(RingHom.injective_iff_ker_eq_bot _).mp
      (ConcreteCategory.bijective_of_isIso e.hom.right).1,
    (RingHom.injective_iff_ker_eq_bot _).mp
      (ConcreteCategory.bijective_of_isIso e.hom.left).1, Ideal.map_bot]

/-- Reuse the quotient engine on an actual arrow isomorphism. Both isomorphic
scalar maps have zero kernel, so its Cartesian-kernel condition is proved. -/
def closedFiberArrowEquiv :
    Koszul.coefficientClosedFiber g.hom ≃+* Koszul.coefficientClosedFiber f.hom :=
  Module.closedFiberQuotientEquiv (A := A) (B := B) (R := R) (S := T)
    e.hom.left.hom
    (ConcreteCategory.bijective_of_isIso e.hom.left).2 e.hom.right.hom
    (ConcreteCategory.bijective_of_isIso e.hom.right).2 g.hom f.hom
    (congrArg CommRingCat.Hom.hom e.hom.w) (arrowIso_kernel e)

/-- The quotient map is induced by the actual ambient-ring map on numerators. -/
theorem closedFiberArrowEquiv_mk (b : B) :
    closedFiberArrowEquiv e (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (e.hom.right b) := rfl

include e in
/-- This is equality of lengths over their respective ORIGINAL scalar rings,
using the existing scalar-compatible module isomorphism, not ring cardinalities. -/
theorem closedFiberArrow_length :
    Module.length B (Koszul.coefficientClosedFiber g.hom) =
      Module.length T (Koszul.coefficientClosedFiber f.hom) :=
  Module.closedFiberQuotient_length (A := A) (B := B) (R := R) (S := T)
    e.hom.left.hom
    (ConcreteCategory.bijective_of_isIso e.hom.left).2 e.hom.right.hom
    (ConcreteCategory.bijective_of_isIso e.hom.right).2 g.hom f.hom
    (congrArg CommRingCat.Hom.hom e.hom.w) (arrowIso_kernel e)

end ArrowTransport

/-- A scheme isomorphism transports arbitrary signed generic coefficients.
This small cycle adapter uses the faithful all-point dictionary and degree one. -/
theorem finitePushforward_genericCoefficients_iso
    {A B : Scheme.{u}} [IsNoetherian A] [IsNoetherian B]
    (e : A ⟶ B) [IsIso e] (c : genericPoints A → ℤ) (d : genericPoints B → ℤ)
    (h : ∀ w, c w = d (mapGenericPoint e w)) :
    IntegralCycle.finitePushforward e (IntegralCycle.ofGenericCoefficients A c) =
      IntegralCycle.ofGenericCoefficients B d := by
  classical
  apply IntegralCycle.toPoints_injective
  rw [IntegralCycle.toPoints_finitePushforward_apply,
    residuePushforward_eq_mapDomain_of_surjectiveOnStalks]
  ext y
  obtain ⟨x, rfl⟩ := e.homeomorph.surjective y
  change Finsupp.mapDomain e (IntegralCycle.toPoints
      (IntegralCycle.ofGenericCoefficients A c)) (e x) = _
  rw [Finsupp.mapDomain_apply_of_injective
    (show Function.Injective e from e.homeomorph.injective)]
  simp only [IntegralCycle.toPoints_ofGenericCoefficients_apply, Scheme.Hom.homeomorph_apply]
  by_cases hx : x ∈ genericPoints A
  · rw [dite_eq_left hx, dite_eq_left ((mem_genericPoints_iff_of_isIso e x).mpr hx)]
    exact h ⟨x, hx⟩
  · rw [dite_eq_right hx,
      dite_eq_right (fun hy => hx ((mem_genericPoints_iff_of_isIso e x).mp hy))]

end Motivic.RightWholeFiberTorExteriorDecomposition

namespace Motivic.FiniteCorrespondenceGenerator

open WholeFiberTorExteriorDecomposition RightWholeFiberTorExteriorDecomposition

variable {k : Type u} [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

local instance rightDecomposition_factorFlat : Flat (F.targetProjection ≫ Y.hom) := by
  let : Subsingleton (Spec (.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  let : IsIntegral (Spec (.of k)) := inferInstance
  exact Flat.instOfSubsingletonCarrierCarrierCommRingCatOfIsIntegral
    (Y := Spec (.of k)) (F.targetProjection ≫ Y.hom)

/-- Only the product order is exchanged; the original G,H incidence is unchanged. -/
abbrev rightFirstStageExteriorSymmetry :
    pullback (G.incidenceSource H ≫ Y.hom) (F.targetProjection ≫ Y.hom) ≅
      F.rightIntermediateSupportProduct G H :=
  pullbackSymmetry (G.incidenceSource H ≫ Y.hom) (F.targetProjection ≫ Y.hom)

/-- The original right projection and the generic decomposition projection agree
through the literal symmetry, including their canonical base-point transport. -/
def rightExteriorSymmetryStalkArrowIso
    (w : (pullback (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom) : Scheme.{u})) :
    Arrow.mk ((F.rightExteriorPairProjection G H).stalkMap
      ((F.rightFirstStageExteriorSymmetry G H).hom w)) ≅
    Arrow.mk ((pullback.fst (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom)).stalkMap w) :=
  Arrow.isoMk
    ((G.incidence H).presheaf.stalkCongr (.of_eq (congrArg
      (fun f : (pullback (G.incidenceSource H ≫ Y.hom)
        (F.targetProjection ≫ Y.hom) : Scheme.{u}) ⟶ G.incidence H => f w)
      (pullbackSymmetry_hom_comp_snd (G.incidenceSource H ≫ Y.hom)
        (F.targetProjection ≫ Y.hom)))))
    (asIso ((F.rightFirstStageExteriorSymmetry G H).hom.stalkMap w)) (by
      dsimp only [Arrow.mk_left, Arrow.mk_right, Arrow.mk_hom, asIso_hom]
      simpa only [Scheme.Hom.stalkMap_comp] using
        (Scheme.Hom.stalkMap_congr_hom
          ((F.rightFirstStageExteriorSymmetry G H).hom ≫ F.rightExteriorPairProjection G H)
          (pullback.fst (G.incidenceSource H ≫ Y.hom) (F.targetProjection ≫ Y.hom))
          (pullbackSymmetry_hom_comp_snd (G.incidenceSource H ≫ Y.hom)
            (F.targetProjection ≫ Y.hom)) w).symm)

/-- The actual unreduced right closed fiber is transported by the actual
symmetry stalk map, not by an assumed abstract quotient compatibility. -/
def rightExteriorClosedFiberSymmetryEquiv
    (w : (pullback (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom) : Scheme.{u})) :
    F.rightExteriorClosedFiber G H ((F.rightFirstStageExteriorSymmetry G H).hom w) ≃+*
      Koszul.coefficientClosedFiber ((pullback.fst (G.incidenceSource H ≫ Y.hom)
        (F.targetProjection ≫ Y.hom)).stalkMap w).hom :=
  closedFiberArrowEquiv (F.rightExteriorSymmetryStalkArrowIso G H w)

/-- Every numerator uses the original symmetry stalk scalar map. -/
theorem rightExteriorClosedFiberSymmetryEquiv_mk
    (w : (pullback (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom) : Scheme.{u}))
    (r : (F.rightIntermediateSupportProduct G H).presheaf.stalk
      ((F.rightFirstStageExteriorSymmetry G H).hom w)) :
    F.rightExteriorClosedFiberSymmetryEquiv G H w (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (((F.rightFirstStageExteriorSymmetry G H).hom.stalkMap w) r) :=
  closedFiberArrowEquiv_mk (F.rightExteriorSymmetryStalkArrowIso G H w) r

/-- The complete quotient scalar square commutes through the literal symmetry
stalk map. This specifies the quotient identification on every ambient scalar. -/
theorem rightExteriorClosedFiberSymmetryEquiv_scalarSquare
    (w : (pullback (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom) : Scheme.{u})) :
    (F.rightExteriorClosedFiberSymmetryEquiv G H w).toRingHom.comp (Ideal.Quotient.mk _) =
      (Ideal.Quotient.mk _).comp
        ((F.rightFirstStageExteriorSymmetry G H).hom.stalkMap w).hom := by
  ext r
  exact F.rightExteriorClosedFiberSymmetryEquiv_mk G H w r

/-- The symmetry preserves closed-fiber length over the literal original rings. -/
theorem rightExteriorClosedFiberSymmetry_length
    (w : (pullback (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom) : Scheme.{u})) :
    Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk
        ((F.rightFirstStageExteriorSymmetry G H).hom w))
      (F.rightExteriorClosedFiber G H ((F.rightFirstStageExteriorSymmetry G H).hom w)) =
    Module.length ((pullback (G.incidenceSource H ≫ Y.hom)
        (F.targetProjection ≫ Y.hom) : Scheme.{u}).presheaf.stalk w)
      (Koszul.coefficientClosedFiber ((pullback.fst (G.incidenceSource H ≫ Y.hom)
        (F.targetProjection ≫ Y.hom)).stalkMap w).hom) :=
  closedFiberArrow_length (F.rightExteriorSymmetryStalkArrowIso G H w)

/-- The literal F.scheme times the reduced original point closure. The exterior
itself is not reduced, so all its generic-stalk multiplicities are retained. -/
abbrev rightFirstStageComponentExterior (z : genericPoints (G.incidence H)) : Scheme.{u} :=
  pullback (F.targetProjection ≫ Y.hom)
    ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ G.incidenceSource H ≫ Y.hom)

/-- Its actual Cartesian closed inclusion into the original right support product. -/
def rightFirstStageComponentExteriorInclusion (z : genericPoints (G.incidence H)) :
    F.rightFirstStageComponentExterior G H z ⟶ F.rightIntermediateSupportProduct G H :=
  pullback.map _ _ _ _ (𝟙 F.scheme)
    (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι (𝟙 (Spec (.of k)))
    (by simp) (by simp)

/-- The actual right inclusion is the base change of the original point closure. -/
theorem rightFirstStageComponentExteriorInclusion_isPullback
    (z : genericPoints (G.incidence H)) :
    IsPullback
      (pullback.snd (F.targetProjection ≫ Y.hom)
        ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
          G.incidenceSource H ≫ Y.hom))
      (F.rightFirstStageComponentExteriorInclusion G H z)
      (IntegralClosedSubscheme.pointClosure z.1).val.subschemeι
      (F.rightExteriorPairProjection G H) := by
  refine IsPullback.of_bot
    (t := (IsPullback.of_hasPullback (F.targetProjection ≫ Y.hom)
      (G.incidenceSource H ≫ Y.hom)).flip) ?_ ?_
  · simpa only [rightFirstStageComponentExteriorInclusion, pullback.map,
      pullback.lift_fst, Category.comp_id] using
      (IsPullback.of_hasPullback (F.targetProjection ≫ Y.hom)
        ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫
          G.incidenceSource H ≫ Y.hom)).flip
  · simp [rightFirstStageComponentExteriorInclusion, rightExteriorPairProjection,
      pullback.map]

instance rightFirstStageComponentExteriorInclusion_isClosedImmersion
    (z : genericPoints (G.incidence H)) :
    IsClosedImmersion (F.rightFirstStageComponentExteriorInclusion G H z) :=
  MorphismProperty.of_isPullback
    (F.rightFirstStageComponentExteriorInclusion_isPullback G H z) inferInstance

local instance rightDecomposition_sourceNoetherian :
    IsNoetherian (F.rightIntermediateSupportProduct G H) :=
  isNoetherian_of_finiteType
    (pullback.snd (F.targetProjection ≫ Y.hom) (G.incidenceSource H ≫ Y.hom))

local instance rightDecomposition_swappedNoetherian :
    IsNoetherian (pullback (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom) : Scheme.{u}) :=
  isNoetherian_of_finiteType
    (pullback.fst (G.incidenceSource H ≫ Y.hom) (F.targetProjection ≫ Y.hom))

instance rightFirstStageComponentExterior_isNoetherian
    (z : genericPoints (G.incidence H)) :
    IsNoetherian (F.rightFirstStageComponentExterior G H z) :=
  isNoetherian_of_finiteType (F.rightFirstStageComponentExteriorInclusion G H z)

local instance rightDecomposition_swappedComponentNoetherian
    (z : genericPoints (G.incidence H)) :
    IsNoetherian (componentExterior (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom) z) :=
  isNoetherian_of_finiteType (componentExteriorInclusion (G.incidenceSource H ≫ Y.hom)
    (F.targetProjection ≫ Y.hom) z)

/-- The component symmetry exchanges product factors without changing its label. -/
abbrev rightFirstStageComponentExteriorSymmetry (z : genericPoints (G.incidence H)) :
    componentExterior (G.incidenceSource H ≫ Y.hom) (F.targetProjection ≫ Y.hom) z ≅
      F.rightFirstStageComponentExterior G H z :=
  pullbackSymmetry
    ((IntegralClosedSubscheme.pointClosure z.1).val.subschemeι ≫ G.incidenceSource H ≫ Y.hom)
    (F.targetProjection ≫ Y.hom)

/-- Both routes are the actual maps into the same right whole support product. -/
@[reassoc] theorem rightFirstStageComponentExteriorSymmetry_inclusion
    (z : genericPoints (G.incidence H)) :
    (F.rightFirstStageComponentExteriorSymmetry G H z).hom ≫
        F.rightFirstStageComponentExteriorInclusion G H z =
      componentExteriorInclusion (G.incidenceSource H ≫ Y.hom)
        (F.targetProjection ≫ Y.hom) z ≫ (F.rightFirstStageExteriorSymmetry G H).hom := by
  apply pullback.hom_ext <;>
    simp [rightFirstStageComponentExteriorInclusion, pullback.map]

/-- Reindexing by the component symmetry retains its whole fundamental cycle. -/
theorem rightFirstStageComponentExterior_finitePushforward_symmetry
    (z : genericPoints (G.incidence H)) :
    IntegralCycle.finitePushforward (F.rightFirstStageExteriorSymmetry G H).hom
      (IntegralCycle.finitePushforward
        (componentExteriorInclusion (G.incidenceSource H ≫ Y.hom)
          (F.targetProjection ≫ Y.hom) z)
        (fundamentalCycle (componentExterior (G.incidenceSource H ≫ Y.hom)
          (F.targetProjection ≫ Y.hom) z))) =
    IntegralCycle.finitePushforward (F.rightFirstStageComponentExteriorInclusion G H z)
      (fundamentalCycle (F.rightFirstStageComponentExterior G H z)) := by
  have hcongr {A B : Scheme.{u}} (f g : A ⟶ B) (hf : IsFinite f) (hg : IsFinite g)
      (h : f = g) (c : IntegralCycle A) :
      @IntegralCycle.finitePushforward A B f hf c =
        @IntegralCycle.finitePushforward A B g hg c := by
    cases h
    rfl
  calc
    _ = IntegralCycle.finitePushforward
        (componentExteriorInclusion (G.incidenceSource H ≫ Y.hom)
          (F.targetProjection ≫ Y.hom) z ≫ (F.rightFirstStageExteriorSymmetry G H).hom)
        (fundamentalCycle (componentExterior (G.incidenceSource H ≫ Y.hom)
          (F.targetProjection ≫ Y.hom) z)) := by
      rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
    _ = IntegralCycle.finitePushforward
        ((F.rightFirstStageComponentExteriorSymmetry G H z).hom ≫
          F.rightFirstStageComponentExteriorInclusion G H z)
        (fundamentalCycle (componentExterior (G.incidenceSource H ≫ Y.hom)
          (F.targetProjection ≫ Y.hom) z)) :=
      hcongr _ _ inferInstance inferInstance
        (F.rightFirstStageComponentExteriorSymmetry_inclusion G H z).symm _
    _ = _ := by
      rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
        finitePushforward_fundamentalCycle]

open Classical in
/-- The whole actual right exterior source cycle, indexed by every original G,H
incidence generic with its original signed Tor coefficient. -/
def rightFirstStageOriginalExteriorCycle : IntegralCycle (F.rightIntermediateSupportProduct G H) :=
  letI := IntegralCycle.genericPointFintype (G.incidence H)
  ∑ z : genericPoints (G.incidence H),
    G.incidenceTorCoefficient (S := Spec (.of k)) H z •
      IntegralCycle.finitePushforward (F.rightFirstStageComponentExteriorInclusion G H z)
        (fundamentalCycle (F.rightFirstStageComponentExterior G H z))

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)

/-- Pull back the identical actual whole right open by the product symmetry. -/
abbrev rightFirstStageSwappedOpen :=
  ((F.rightFirstStageExteriorSymmetry G H).hom ⁻¹ᵁ
    ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V)).toScheme

/-- The actual restriction of the whole symmetry is an isomorphism onto the
existing whole right inverse-image open. -/
abbrev rightFirstStageWholeSymmetry :
    F.rightFirstStageSwappedOpen G H V ⟶ F.rightFirstStageWholeOpen G H V :=
  (F.rightFirstStageExteriorSymmetry G H).hom ∣_ ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V)

local instance rightDecomposition_swappedOpenNoetherian :
    IsNoetherian (F.rightFirstStageSwappedOpen G H V) :=
  isNoetherian_of_finiteType (F.rightFirstStageWholeSymmetry G H V)

/-- The original G,H label is literally unchanged under whole-open symmetry. -/
theorem rightFirstStageWholeGenericPair_symmetry
    (w : genericPoints (F.rightFirstStageSwappedOpen G H V)) :
    F.rightFirstStageWholeGenericPair G H V
      (mapGenericPoint (F.rightFirstStageWholeSymmetry G H V) w) =
    componentGeneric (G.incidenceSource H ≫ Y.hom) (F.targetProjection ≫ Y.hom)
      ((F.rightFirstStageExteriorSymmetry G H).hom ⁻¹ᵁ
        ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V)) w := by
  apply Subtype.ext
  change F.rightExteriorPairProjection G H
    ((F.rightFirstStageWholeSymmetry G H V w.1).1) = _
  rw [morphismRestrict_base_coe]
  exact congrArg
    (fun f : (pullback (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom) : Scheme.{u}) ⟶ G.incidence H => f w.1.1)
    (pullbackSymmetry_hom_comp_snd (G.incidenceSource H ≫ Y.hom)
      (F.targetProjection ≫ Y.hom))

/-- The finite unreduced multiplicity of the ORIGINAL right closed fiber is
precisely the coefficient used by the general exterior engine. -/
theorem rightFirstStageWholeGenericFiberMultiplicity_symmetry
    (w : genericPoints (F.rightFirstStageSwappedOpen G H V)) :
    F.rightFirstStageWholeGenericFiberMultiplicity G H V
      (mapGenericPoint (F.rightFirstStageWholeSymmetry G H V) w) =
    closedFiberMultiplicity (G.incidenceSource H ≫ Y.hom) (F.targetProjection ≫ Y.hom)
      ((F.rightFirstStageExteriorSymmetry G H).hom ⁻¹ᵁ
        ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V)) w := by
  unfold rightFirstStageWholeGenericFiberMultiplicity closedFiberMultiplicity
    LengthEuler.integerLength
  apply congrArg (fun n : ℕ∞ => (n.toNat : ℤ))
  have hpoint := morphismRestrict_base_coe (F.rightFirstStageExteriorSymmetry G H).hom
    ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V) w.1
  exact (congrArg (fun x : F.rightIntermediateSupportProduct G H =>
    Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk x)
      (F.rightExteriorClosedFiber G H x)) hpoint).trans
        (F.rightExteriorClosedFiberSymmetry_length G H w.1.1)

/-- Source-cycle endpoint on the actual right whole inverse-image affine open.
It follows from the existing all-branch component decomposition, literal stalk
scalar transport, and open-restriction compatibility. No new cycle equality is assumed. -/
theorem rightFirstStageWholeTorGenericCycle_eq_openRestriction_originalExteriorCycle :
    F.rightFirstStageWholeTorGenericCycle G H V =
      IntegralCycle.openRestriction ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V)
        (F.rightFirstStageOriginalExteriorCycle G H) := by
  classical
  let := IntegralCycle.genericPointFintype (G.incidence H)
  let p := G.incidenceSource H ≫ Y.hom
  let t := F.targetProjection ≫ Y.hom
  let U := (F.rightIntermediateImageMap G H) ⁻¹ᵁ V
  let U' := (F.rightFirstStageExteriorSymmetry G H).hom ⁻¹ᵁ U
  let c := G.incidenceTorCoefficient (S := Spec (.of k)) H
  have hc := finitePushforward_genericCoefficients_iso
    (F.rightFirstStageWholeSymmetry G H V)
    (fun w => c (componentGeneric p t U' w) * closedFiberMultiplicity p t U' w)
    (F.rightFirstStageWholeTorGenericCoefficient G H V) (fun w => by
      rw [F.rightFirstStageWholeTorGenericCoefficient_eq_pair_mul G H V,
        F.rightFirstStageWholeGenericPair_symmetry G H V,
        F.rightFirstStageWholeGenericFiberMultiplicity_symmetry G H V])
  change IntegralCycle.finitePushforward (F.rightFirstStageWholeSymmetry G H V)
      (IntegralCycle.ofGenericCoefficients U'.toScheme
        (fun w => c (componentGeneric p t U' w) * closedFiberMultiplicity p t U' w)) =
      F.rightFirstStageWholeTorGenericCycle G H V at hc
  rw [← hc, ofGenericCoefficients_eq_openRestriction_component_sum,
    ← IntegralCycle.openRestriction_finitePushforward]
  apply congrArg (IntegralCycle.openRestriction U)
  change IntegralCycle.finitePushforward (F.rightFirstStageExteriorSymmetry G H).hom
      (∑ z : genericPoints (G.incidence H), c z •
        IntegralCycle.finitePushforward (componentExteriorInclusion p t z)
          (fundamentalCycle (componentExterior p t z))) = _
  rw [map_sum]
  unfold rightFirstStageOriginalExteriorCycle
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul, F.rightFirstStageComponentExterior_finitePushforward_symmetry G H z]

end Motivic.FiniteCorrespondenceGenerator
