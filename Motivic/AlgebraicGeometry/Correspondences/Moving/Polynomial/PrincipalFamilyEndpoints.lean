/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.RetainedGraphCycle
public import Motivic.AlgebraicGeometry.Correspondences.Endpoints.FinitePoint.RetainedPushforward
public import Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamilyPointCycle
public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyWholeEndpoints


/-!
# Original correspondence endpoints of the principal family

The correspondence remains the original signed order family. Its graph endpoints
are compared through the faithful native point-cycle map, using the original
retained support sums and the whole-cycle zero and one formulas. The original
function is a unit on the full prescribed boundary neighborhood.
-/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FiniteFlatCurve AlgebraicGeometry.PrincipalFamilyUnitOpen
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open PrincipalFamilyEndpointCuts

universe u

namespace Motivic.PrincipalFamilyCorrespondence

open _root_.AlgebraicGeometry.Scheme.IntegralCycle RelativeEndpointDiagram
open _root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram
  (endpointMorphism relativeLineSite)

attribute [local instance] _root_.AlgebraicGeometry.PrincipalFamilyUnitOpen.nonemptyTop
    _root_.AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialProductIntegral
    _root_.AlgebraicGeometry.PrincipalFamilyUnitOpen.polynomialProductNoetherian
  Scheme.functionField_nonempty_preimage Scheme.nonempty_image_open

/-- The original boundary neighborhood contains the entire omitted locus. -/
theorem original_boundary_cover {C V W B : Scheme.{u}}
    (j : V ⟶ C) (v : W ⟶ C) [IsOpenImmersion v] (b : B ⟶ W)
    (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v)) : (Set.range j)ᶜ ⊆ (v ''ᵁ ⊤ : Set C) := by
  intro x hx
  obtain ⟨z, hz⟩ := hcover hx
  exact ⟨b z, trivial, hz⟩

variable {k : Type u} [Field k] (X Y : SmoothSite (Spec (.of k)))
  [IsAffine X.left] [IsIntegral X.left]
  {C V W B : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  [IsNoetherian V] [V.IsQuasiAffine] [IsIntegral W] [IsNoetherian W]
  (q : C ⟶ X.left) [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (v : W ⟶ C) [IsOpenImmersion v] (b : B ⟶ W) [Nonempty B]
  (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
  (f : Γ(W, ⊤)) (hf : b.appTop f = 1)
  (g : V ⟶ Y.left) (hbase : j ≫ q ≫ X.hom = g ≫ Y.hom)

omit [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsNoetherian W] in
/-- The actual graph endpoint point cycle is the original retained family cycle,
followed by its original source-target map. -/
theorem toPoints_graph_endpoint (a : k) :
    let : Nonempty (ambientUnitOpen (q ≫ X.hom) v f) :=
      nonempty_ambientUnitOpen_of_boundary (q ≫ X.hom) v b f hf
    FiniteCorrespondence.toPoints (f := X.hom) (g := Y.hom)
      ((Cor.graphFunctor k).map (endpointMorphism X a) ≫
        correspondence X Y q j v b hcover f hf g hbase) =
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
      (pullback.lift (j ≫ q) g (by simpa only [Category.assoc] using hbase))
      (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (projection (j ≫ (q ≫
          X.hom)))
        (toPoints (wholeComponentFiber (parameterProjection (j ≫ (q ≫ X.hom))) a
          (openImmersionRestriction (retainedInclusion X q j)
            (originalOrderCycle (q ≫ X.hom) v f))))) := by
  let : Nonempty (ambientUnitOpen (q ≫ X.hom) v f) :=
    nonempty_ambientUnitOpen_of_boundary (q ≫ X.hom) v b f hf
  let : IsAffine ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsAffine X.left)
  let : IsAffineHom (projection X.hom) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let : IsAffine (parameterSpace X.hom) := isAffine_of_isAffineHom (projection X.hom)
  let U := ambientUnitOpen (q ≫ X.hom) v f
  let s := ambientUnitSection (q ≫ X.hom) v f
  let hs := isUnit_ambientUnitSection (q ≫ X.hom) v f
  let hc := complement_subset_ambientUnitOpen (q ≫ X.hom) j v b hcover f hf
  let c := _root_.AlgebraicGeometry.Scheme.principalOrderCycle U s hs
  let hr := _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_range (retainedInclusion X q
      j) U hc s hs
  let hfin := fun x : c.support =>
      _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_isFinite
    (familyProjection X q) (retainedInclusion X q j) U hc s hs x.val
      (Finsupp.mem_support_iff.mp x.property)
  let hdom := fun x : c.support =>
      _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_dominates_component
    (familyProjection X q) (retainedInclusion X q j) U hc s hs x.val
      (Finsupp.mem_support_iff.mp x.property)
  rw [correspondence_eq_originalPointCycle X Y q j v b hcover f hf g hbase]
  change toPoints (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
    ((Cor.graphFunctor k).map (endpointMorphism X a) ≫
      FinitePointCycleCorrespondence.correspondence (X := relativeLineSite X) (Y := Y)
        (familyProjection X q) (retainedInclusion X q j) c hr hfin hdom
        (projection (j ≫ (q ≫ X.hom)) ≫ g) (family_base X Y q j g hbase))) = _
  rw [FinitePointCycleCorrespondence.toPoints_graph_endpoint_retained_cycle]
  have hp : familyProjection X q ≫
      pullback.snd X.hom (_root_.AlgebraicGeometry.Scheme.SmoothSite.AffineLineField.line k).hom =
      parameterProjection (q ≫ X.hom) := by
    change lineMap X.hom q ≫ parameterProjection X.hom = _
    simp only [lineMap, parameterProjection, pullback.map, pullback.lift_snd,
      Category.comp_id]
  have hj : retainedInclusion X q j ≫ parameterProjection (q ≫ X.hom) =
      parameterProjection (j ≫ (q ≫ X.hom)) := by
    simp only [retainedInclusion, lineMap, parameterProjection, pullback.map,
      pullback.lift_snd, Category.comp_id]
  have hm : FinitePointCycleCorrespondence.retainedEndpointProduct X Y
      (familyProjection X q) (retainedInclusion X q j)
      (projection (j ≫ (q ≫ X.hom)) ≫ g) (family_base X Y q j g hbase) =
      projection (j ≫ (q ≫ X.hom)) ≫
        pullback.lift (j ≫ q) g (by simpa only [Category.assoc] using hbase) := by
    apply pullback.hom_ext
    · simp only [FinitePointCycleCorrespondence.retainedEndpointProduct,
        pullback.lift_fst, Category.assoc]
      change lineMap (q ≫ X.hom) j ≫ lineMap X.hom q ≫ projection X.hom = _
      rw [lineMap_projection, lineMap_projection_assoc]
    · simp only [FinitePointCycleCorrespondence.retainedEndpointProduct,
        pullback.lift_snd, Category.assoc]
  rw [hm, _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward_comp,
      AddMonoidHom.comp_apply]
  congr 2
  erw [hp, wholeComponentFiber_openImmersionRestriction, hj]
  rfl

/-- The same original signed family has zero endpoint zero and endpoint one
exactly the original principal correspondence, not a supplied cycle witness. -/
theorem graph_endpoints (hu : IsUnit f) :
    (Cor.graphFunctor k).map (endpointMorphism X 0) ≫
        correspondence X Y q j v b hcover f hf g hbase = 0 ∧
      (Cor.graphFunctor k).map (endpointMorphism X 1) ≫
        correspondence X Y q j v b hcover f hf g hbase =
      PrincipalOrderCorrespondence.correspondence q j (v ''ᵁ ⊤)
        (original_boundary_cover j v b hcover)
        ((v.appIso ⊤).inv f) (hu.map (v.appIso ⊤).inv.hom) g hbase := by
  let : Nonempty (ambientUnitOpen (q ≫ X.hom) v f) :=
    nonempty_ambientUnitOpen_of_boundary (q ≫ X.hom) v b f hf
  obtain ⟨hzero, hone⟩ :=
      _root_.AlgebraicGeometry.PrincipalFamilyUnitOpen.originalOrderCycle_whole_endpoints X q j v b
      hcover f hf hu
  constructor
  · apply FiniteCorrespondence.toPoints_injective
    erw [toPoints_graph_endpoint X Y q j v b hcover f hf g hbase 0, hzero, map_zero]
  · apply FiniteCorrespondence.toPoints_injective
    let U := v ''ᵁ ⊤
    let s := (v.appIso ⊤).inv f
    let hs := hu.map (v.appIso ⊤).inv.hom
    let hc := original_boundary_cover j v b hcover
    let c := _root_.AlgebraicGeometry.Scheme.principalOrderCycle U s hs
    let hr := _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_range j U hc s hs
    let hfin := fun x : c.support =>
        _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_isFinite q j U hc s hs
      x.val (Finsupp.mem_support_iff.mp x.property)
    let hdom := fun x : c.support =>
        _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_dominates_component
      q j U hc s hs x.val (Finsupp.mem_support_iff.mp x.property)
    have ht := FinitePointCycleCorrespondence.toPoints_correspondence_retained_pushforward
      X Y q j c hr hfin hdom g hbase
    have he := PrincipalOrderCorrespondence.correspondence_eq_finitePointCycle
      (X := X) (Y := Y) q j U hc s hs g hbase
    have hp := congrArg (FiniteCorrespondence.toPoints (f := X.hom) (g := Y.hom)) he
    have hz := toPoints_graph_endpoint X Y q j v b hcover f hf g hbase 1
    exact hz.trans ((congrArg
      (_root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward
        (pullback.lift (j ≫ q) g (by simpa only [Category.assoc] using hbase))) hone).trans
          (hp.trans ht).symm)

end Motivic.PrincipalFamilyCorrespondence
