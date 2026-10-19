/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.Relative.PencilEndpoints
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.Open.PencilEndpoints
/-! # Relative-target polynomial homotopies remain original k-correspondences -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent
open AlgebraicGeometry.PolynomialOpenQuotient
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
universe u
namespace AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLine
variable {k R A : Type u} [Field k] [CommRing R] [CommRing A]
    [Algebra k R] [Algebra.Smooth k R] [Algebra R A] [Algebra k A]
    [IsScalarTower k R A] [Algebra.Smooth k A]

omit [Algebra.Smooth k R] [Algebra.Smooth k A] [Algebra k R] [IsScalarTower k R A] in
/-- Coefficient specialization really fixes the original field. -/
theorem specialize_parameterCoefficients (a : k) :
    (evalRingHom (algebraMap k A a)).comp
      (parameterCoefficients (R := R) (A := A)) = algebraMap R A := by
  ext r
  exact eval_C

omit [Algebra.Smooth k R] [Algebra.Smooth k A] [Algebra k R] [IsScalarTower k R A] in
/-- The entire specialized quotient still lands in the same original open. -/
theorem specialized_boundary_unit (p : A[X][X]) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (R := R) (A := A)))))
    (a : k) :
    IsUnit (AdjoinRoot.mk (p.map (evalRingHom (algebraMap k A a)))
      (f.map (algebraMap R A))) := by
  simpa only [specialize_parameterCoefficients] using
    coefficient_boundary_unit (parameterCoefficients (R := R) (A := A))
      (evalRingHom (algebraMap k A a)) p f hf

/-- Graph evaluation is the original whole polynomial fiber, with all multiplicities. -/
theorem graph_familyCycle (p : A[X][X]) (hp : p.Monic) (f : R[X])
    (hf : IsUnit (AdjoinRoot.mk p (f.map (parameterCoefficients (R := R) (A := A)))))
    (a : k) :
    (_root_.Motivic.Cor.graphFunctor k).map
        (SmoothSite.a1Section (.of k) (sourceSite (k := k) (A := A)) a) ≫
      familyCycle p hp f hf =
        cycle (p.map (evalRingHom (algebraMap k A a)))
          (hp.map _) f (specialized_boundary_unit p f hf a) := by
  let σ := algebraMap k A
  let φ := evalRingHom (σ a)
  let : IsFinite (familySource σ p) := family_finite _ _ hp
  let : Flat (familySource σ p) := family_flat _ _ hp
  let : IsFinite (source (p.map φ)) := source_finite _ (hp.map φ)
  let : Flat (source (p.map φ)) := source_flat _ (hp.map φ)
  let : IsOpenImmersion (openInclusion (k := k) f).left := inferInstanceAs
    (IsOpenImmersion (principalOpen f).ι)
  let : IsClosedImmersion (pullback.lift (familySource σ p)
      (target (parameterCoefficients (R := R) (A := A)) p) (family_affine_base (k := k) p)) :=
    family_joint_closed (k := k) p
  apply _root_.Motivic.Cor.comp_open_graph_injective (openInclusion (k := k) f)
  dsimp only
  rw [Category.assoc, familyCycle, _root_.Motivic.Cor.ofFiniteFlatSpan_comp_graph]
  have htarget : openTarget (parameterCoefficients (R := R) (A := A)) p f hf ≫
      (openInclusion (k := k) f).left = target (parameterCoefficients (R := R) (A := A)) p :=
    openTarget_inclusion _ _ _ _
  simp only [htarget]
  have hend := @_root_.Motivic.Cor.graph_relative_endpoint_ofFiniteFlatSpan k _
    (sourceSite (k := k) (A := A)) (lineSite (k := k) (R := R))
    (Spec (.of (AdjoinRoot p))) (familySource σ p) inferInstance inferInstance
    (target (parameterCoefficients (R := R) (A := A)) p) (family_affine_base (k := k) p)
    (family_joint_closed (k := k) p) a
  erw [← Endpoints.endpointMorphism_eq_a1Section, hend, cycle_comp_inclusion]
  dsimp only [_root_.Motivic.Cor.relativeFiniteFlatSpanEndpoint]
  symm
  apply _root_.Motivic.PolynomialPencilCycles.span_eq_of_iso (familyEndpoint_isPullback σ p
      a).isoPullback
  · exact (familyEndpoint_isPullback σ p a).isoPullback_hom_fst
  · erw [← Category.assoc, (familyEndpoint_isPullback σ p a).isoPullback_hom_snd,
      coefficient_target]
    congr 1
    exact specialize_parameterCoefficients a

end AlgebraicGeometry.PolynomialOpenQuotient.SmoothSite
