/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.PolynomialOpenSpanIdentities
public import Motivic.Aglib.AlgebraicGeometry.PolynomialQuotientPencilGeometry
public import Motivic.AlgebraicGeometry.Correspondences.RelativeFiniteFlatSpanEndpoints
public import Motivic.AlgebraicGeometry.Correspondences.PolynomialPencilCycles
public import Motivic.AlgebraicGeometry.Correspondences.PencilA1Endpoints
/-! # Whole monic-polynomial homotopies with actual original endpoint graphs -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient Motivic.RelativeEndpointDiagram
universe u
namespace Motivic.PolynomialOpenSpans
variable {k R : Type u} [Field k] [CommRing R] [Algebra k R] [Algebra.Smooth k R]

/-- The literal parameterized coefficient map. -/
abbrev parameterCoefficients : k →+* R[X] := C.comp (algebraMap k R)

/-- Actual open-target compatibility for the whole polynomial family. -/
theorem family_open_base (p : R[X][X]) (f : k[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (k := k) (R := R))))) :
    familySource (algebraMap k R) p ≫
        (SmoothSite.a1Cylinder (.of k) (affineSite (k := k) (R := R))).hom =
      openTarget (parameterCoefficients (k := k) (R := R)) p f hf ≫ (openSite f).hom := by
  change familySource (algebraMap k R) p ≫ relativeLineHom
    (Spec.map (CommRingCat.ofHom (algebraMap k R))) =
      openTarget _ _ _ _ ≫ ((principalOpen f).ι ≫ polynomialProjection (.of k))
  exact (family_base (algebraMap k R) p).trans
    (congrArg (fun z ↦ z ≫ polynomialProjection (.of k))
      (openTarget_inclusion (parameterCoefficients (k := k) (R := R)) p f hf).symm)

/-- The family is a genuine finite correspondence from the original cylinder. -/
def familyCycle (p : R[X][X]) (hp : p.Monic) (f : k[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (k := k) (R := R))))) :
    Cor.mk (SmoothSite.a1Cylinder (.of k) (affineSite (k := k) (R := R))) ⟶
      Cor.mk (openSite f) := by
  let : IsFinite (familySource (algebraMap k R) p) := family_finite _ _ hp
  let : Flat (familySource (algebraMap k R) p) := family_flat _ _ hp
  exact Cor.ofFiniteFlatSpan (familySource (algebraMap k R) p)
    (openTarget _ p f hf) (family_open_base p f hf)

omit [Algebra.Smooth k R] in
/-- Coefficient specialization really fixes the original field. -/
theorem specialize_parameterCoefficients (a : k) :
    (evalRingHom (algebraMap k R a)).comp
      (parameterCoefficients (k := k) (R := R)) = algebraMap k R := by
  ext r
  exact eval_C

omit [Algebra.Smooth k R] in
/-- The entire specialized quotient still lands in the same original open. -/
theorem specialized_boundary_unit (p : R[X][X]) (f : k[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (k := k) (R := R)))))
    (a : k) :
    IsUnit (AdjoinRoot.mk (p.map (evalRingHom (algebraMap k R a)))
      (f.map (algebraMap k R))) := by
  simpa only [specialize_parameterCoefficients] using
    coefficient_boundary_unit (parameterCoefficients (k := k) (R := R))
      (evalRingHom (algebraMap k R a)) p f hf

/-- Graph evaluation is the original whole polynomial fiber, with all multiplicities. -/
theorem graph_familyCycle (p : R[X][X]) (hp : p.Monic) (f : k[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (k := k) (R := R)))))
    (a : k) :
    (Cor.graphFunctor k).map
        (SmoothSite.a1Section (.of k) (affineSite (k := k) (R := R)) a) ≫
      familyCycle p hp f hf =
        cycle (p.map (evalRingHom (algebraMap k R a)))
          (hp.map _) f (specialized_boundary_unit p f hf a) := by
  let σ := algebraMap k R
  let φ := evalRingHom (σ a)
  let : IsFinite (familySource σ p) := family_finite _ _ hp
  let : Flat (familySource σ p) := family_flat _ _ hp
  let : IsFinite (source (p.map φ)) := source_finite _ (hp.map φ)
  let : Flat (source (p.map φ)) := source_flat _ (hp.map φ)
  let : IsOpenImmersion (openInclusion f).left := inferInstanceAs
    (IsOpenImmersion (principalOpen f).ι)
  let : IsClosedImmersion (pullback.lift (familySource σ p)
      (target (parameterCoefficients (k := k) (R := R)) p) (family_base σ p)) :=
    family_joint_closed σ p
  apply Cor.comp_open_graph_injective (openInclusion f)
  dsimp only
  rw [Category.assoc, familyCycle, Cor.ofFiniteFlatSpan_comp_graph]
  have htarget : openTarget (parameterCoefficients (k := k) (R := R)) p f hf ≫
      (openInclusion f).left = target (parameterCoefficients (k := k) (R := R)) p :=
    openTarget_inclusion _ _ _ _
  simp only [htarget]
  have hend := @Cor.graph_relative_endpoint_ofFiniteFlatSpan k _
    (affineSite (k := k) (R := R)) (SmoothSite.affineLine (.of k))
    (Spec (.of (AdjoinRoot p))) (familySource σ p) inferInstance inferInstance
    (target (C.comp σ) p) (family_base σ p) (family_joint_closed σ p) a
  erw [← PencilA1Endpoints.endpointMorphism_eq_a1Section, hend, cycle_comp_inclusion]
  dsimp only [Cor.relativeFiniteFlatSpanEndpoint]
  symm
  apply PolynomialPencilCycles.span_eq_of_iso (familyEndpoint_isPullback σ p a).isoPullback
  · exact (familyEndpoint_isPullback σ p a).isoPullback_hom_fst
  · erw [← Category.assoc, (familyEndpoint_isPullback σ p a).isoPullback_hom_snd,
      coefficient_target]
    congr 1
    exact specialize_parameterCoefficients a

end Motivic.PolynomialOpenSpans
