/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyEndpointCoefficients
public import Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.WholeComponentFiberProjectionSupport
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Restriction.RetainedPointClosure
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Divisors.PrincipalOrder
public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.GeometricIntegrality


/-!
# Whole zero and one cycles of the original principal family

The retained cycle is the literal open restriction of the original ambient order
cycle. Its finite dominant supports are derived from the proper compactification
and whole boundary unit locus. Polynomial-product integrality is supplied by the
native geometrically integral projection. No endpoint or coheight family is input.
The final correspondence graph-composition identification is a separate interface.


Intended upstream module:
`Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.Faces.PrincipalFamilyWholeEndpoints`.
Incoming project consumers:
`Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamilyEndpoints`.
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

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

open _root_.AlgebraicGeometry.Scheme.IntegralCycle

attribute [local instance] Scheme.functionField_openImmersion_dominant
  Scheme.functionField_nonempty_preimage Scheme.nonempty_image_open

local instance nonemptyTop {P : Scheme.{u}} [IsIntegral P] : Nonempty (⊤ : P.Opens) :=
  ⟨⟨genericPoint P, trivial⟩⟩

local instance polynomialProductIntegral {k : Type u} [Field k] {P : Scheme.{u}}
    [IsIntegral P] [IsLocallyNoetherian P] (p : P ⟶ Spec (.of k)) :
    IsIntegral (parameterSpace p) := by
  change IsIntegral (pullback p (Scheme.PolynomialLaurent.polynomialProjection (.of k)))
  infer_instance

local instance polynomialProductNoetherian {k : Type u} [Field k] {P : Scheme.{u}}
    [IsNoetherian P] (p : P ⟶ Spec (.of k)) : IsNoetherian (parameterSpace p) := by
  have : LocallyOfFiniteType
      (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact _root_.AlgebraicGeometry.Scheme.isNoetherian_of_finiteType (projection p)

variable {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
  [IsAffine X.left] [IsIntegral X.left]
  {C V W B : Scheme.{u}} [IsIntegral C] [IsNoetherian C]
  [IsIntegral V] [IsNoetherian V] [V.IsQuasiAffine]
  [IsIntegral W] [IsNoetherian W]
  (q : C ⟶ X.left) [IsProper q]
  (j : V ⟶ C) [IsOpenImmersion j] [SmoothOfRelativeDimension 1 (j ≫ q)]
  (v : W ⟶ C) [IsOpenImmersion v] (b : B ⟶ W) [Nonempty B]
  (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
  (f : Γ(W, ⊤)) (hf : b.appTop f = 1)

local instance localUnitNonempty
    [Nonempty (ambientUnitOpen (q ≫ X.hom) v f)] : Nonempty (unitOpen (v ≫ (q ≫ X.hom)) f) := by
  obtain ⟨z⟩ := ‹Nonempty (ambientUnitOpen (q ≫ X.hom) v f)›
  obtain ⟨y, hy⟩ := (show z.1 ∈ (lineMap (q ≫ X.hom) v) ''ᵁ
      unitOpen (v ≫ (q ≫ X.hom)) f from z.2)
  exact ⟨⟨y, hy.1⟩⟩

include hcover hf in
omit [IsIntegral V] [AlgebraicGeometry.IsNoetherian V] [IsIntegral W]
  [AlgebraicGeometry.IsNoetherian W] [Nonempty B] in
private theorem retained_support_properties
    [Nonempty (ambientUnitOpen (q ≫ X.hom) v f)]
    (Z : _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme (parameterSpace (j ≫ (q ≫ X.hom))))
    (hZ : Z ∈ (openImmersionRestriction (lineMap (q ≫ X.hom) j)
      (originalOrderCycle (q ≫ X.hom) v f)).support) :
    IsFinite (Z.val.subschemeι ≫ lineMap X.hom (j ≫ q)) ∧
      IsDominant (Z.val.subschemeι ≫ lineMap X.hom (j ≫ q)) := by
  let : IsAffine ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsAffine X.left)
  let : IsIntegral ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsIntegral X.left)
  let : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsLocallyNoetherian X.left)
  let : IsAffineHom (projection X.hom) := MorphismProperty.pullback_fst _ _ inferInstance
  let : IsAffine (parameterSpace X.hom) := isAffine_of_isAffineHom (projection X.hom)
  let : IsAffineHom (projection (j ≫ (q ≫ X.hom))) :=
    MorphismProperty.pullback_fst _ _ inferInstance
  let : (parameterSpace (j ≫ (q ≫ X.hom))).IsQuasiAffine :=
    Scheme.IsQuasiAffine.of_isAffineHom (projection (j ≫ (q ≫ X.hom)))
  let : IsProper (lineMap X.hom q) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (lineMap_isPullback X.hom q).flip inferInstance
  let i := lineMap (q ≫ X.hom) j
  have hm : i ≫ lineMap X.hom q = lineMap X.hom (j ≫ q) := by
    dsimp only [i, lineMap]
    ext <;> simp [pullback.map] <;> rfl
  let : SmoothOfRelativeDimension 1 (i ≫ lineMap X.hom q) := by
    rw [hm]
    exact MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1)
      (lineMap_isPullback X.hom (j ≫ q)).flip inferInstance
  let U := ambientUnitOpen (q ≫ X.hom) v f
  let s := ambientUnitSection (q ≫ X.hom) v f
  let hs := isUnit_ambientUnitSection (q ≫ X.hom) v f
  have hU := complement_subset_ambientUnitOpen (q ≫ X.hom) j v b hcover f hf
  have hn : _root_.AlgebraicGeometry.Scheme.principalOrderCycle U s hs (i Z.point) ≠ 0 := by
    have h := toPoints_openImmersionRestriction i (originalOrderCycle (q ≫ X.hom) v f)
      Z.point
    have hval : toPoints (openImmersionRestriction i
        (originalOrderCycle (q ≫ X.hom) v f)) Z.point =
        (openImmersionRestriction i (originalOrderCycle (q ≫ X.hom) v f)) Z :=
      Finsupp.mapDomain_apply_of_injective
          _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.point_injective _ Z
    rw [hval] at h
    have hn' := Finsupp.mem_support_iff.mp hZ
    rw [h] at hn'
    simpa only [originalOrderCycle, toPoints_fromPoints] using hn'
  have hr := _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_range i U hU s hs
    ⟨i Z.point, Finsupp.mem_support_iff.mpr hn⟩
  let : IsFinite ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (i
      Z.point)).val.subschemeι ≫
      lineMap X.hom q) :=
    _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_isFinite (lineMap X.hom q) i U hU s
        hs _ hn
  have hd := _root_.AlgebraicGeometry.Scheme.principalOrderCycle_support_dominates_component
    (lineMap X.hom q) i U hU s hs (i Z.point) hn
  have hsurj : Function.Surjective
      ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (i
          Z.point)).val.subschemeι ≫
        lineMap X.hom q) := by
    rw [irreducibleComponents_eq_singleton, Set.mem_singleton_iff] at hd
    exact Set.range_eq_univ.mp hd
  let : Surjective ((_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure (i
      Z.point)).val.subschemeι ≫
      lineMap X.hom q) := (surjective_iff _).mpr hsurj
  have ht :=
      _root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.retainedPointClosure_finite_dominant
    i Z.point hr (lineMap X.hom q)
  rw [_root_.AlgebraicGeometry.Scheme.IntegralClosedSubscheme.pointClosure_point] at ht
  simpa only [hm] using ht

include hcover hf in
omit [IsIntegral V] in
/-- The actual whole retained family has endpoint zero equal to zero and endpoint
one equal to the original signed principal cycle, with all multiplicities retained. -/
theorem originalOrderCycle_whole_endpoints (hu : IsUnit f) :
    let : Nonempty (ambientUnitOpen (q ≫ X.hom) v f) :=
      nonempty_ambientUnitOpen_of_boundary (q ≫ X.hom) v b f hf
    let c := openImmersionRestriction (lineMap (q ≫ X.hom) j)
      (originalOrderCycle (q ≫ X.hom) v f)
    let target := openImmersionRestriction j (fromPoints
      (_root_.AlgebraicGeometry.Scheme.principalOrderCycle (v ''ᵁ ⊤) ((v.appIso ⊤).inv f) (hu.map
          (v.appIso ⊤).inv.hom)))
    _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (projection (j ≫ (q ≫
        X.hom)))
        (toPoints (wholeComponentFiber (parameterProjection (j ≫ (q ≫ X.hom))) 0 c)) = 0 ∧
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (projection (j ≫ (q ≫
          X.hom)))
        (toPoints (wholeComponentFiber (parameterProjection (j ≫ (q ≫ X.hom))) 1 c)) =
        toPoints target := by
  let : Nonempty (ambientUnitOpen (q ≫ X.hom) v f) :=
    nonempty_ambientUnitOpen_of_boundary (q ≫ X.hom) v b f hf
  let : IsNoetherian (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine
      ((j ≫ q) ≫ X.hom)) :=
    inferInstanceAs (IsNoetherian (parameterSpace ((j ≫ q) ≫ X.hom)))
  let : IsNoetherian (_root_.AlgebraicGeometry.Scheme.Products.RelativeEndpointDiagram.relativeLine
      (j ≫ (q ≫ X.hom))) :=
    inferInstanceAs (IsNoetherian (parameterSpace (j ≫ (q ≫ X.hom))))
  dsimp only
  let c := openImmersionRestriction (lineMap (q ≫ X.hom) j)
    (originalOrderCycle (q ≫ X.hom) v f)
  have hfin := fun Z hZ => (retained_support_properties X q j v b hcover f hf Z hZ).1
  have hdom := fun Z hZ => (retained_support_properties X q j v b hcover f hf Z hZ).2
  have hcoeff (a : k) (x : V) :
      _root_.AlgebraicGeometry.Scheme.FiniteSupportCycle.residuePushforward (projection (j ≫ (q ≫
          X.hom)))
        (toPoints (wholeComponentFiber (parameterProjection (j ≫ (q ≫ X.hom))) a c)) x =
      toPoints (wholeComponentFiber (parameterProjection (q ≫ X.hom)) a
        (originalOrderCycle (q ≫ X.hom) v f)) (endpoint (q ≫ X.hom) a (j x)) := by
    erw [wholeComponentFiber_projection_coefficient (j ≫ (q ≫ X.hom)) a c x]
    change toPoints (wholeComponentFiber (parameterProjection (j ≫ (q ≫ X.hom))) a c)
      (endpoint (j ≫ (q ≫ X.hom)) a x) = _
    have hp : lineMap (q ≫ X.hom) j ≫ parameterProjection (q ≫ X.hom) =
        parameterProjection (j ≫ (q ≫ X.hom)) := by
      simp only [lineMap, parameterProjection, pullback.map, pullback.lift_snd, Category.comp_id]
    rw [← hp, ← wholeComponentFiber_openImmersionRestriction,
      toPoints_openImmersionRestriction]
    exact congrArg (toPoints (wholeComponentFiber (parameterProjection (q ≫ X.hom)) a
      (originalOrderCycle (q ≫ X.hom) v f)))
      (congrArg (fun m => m x) (endpoint_parameterMap (q ≫ X.hom) j a))
  constructor
  · ext x
    by_cases hx : Order.coheight x = 1
    · rw [hcoeff]
      exact (originalOrderCycle_endpoint_coefficients (q ≫ X.hom) v f hu.ne_zero
        (j x) (by rwa [coheight_eq_of_isOpenImmersion j])).1
    · exact wholeComponentFiber_projection_eq_zero_of_coheight_ne
        X (j ≫ q) c hfin hdom 0 x hx
  · ext x
    rw [toPoints_openImmersionRestriction, toPoints_fromPoints,
        _root_.AlgebraicGeometry.Scheme.principalOrderCycle_apply]
    by_cases hx : Order.coheight x = 1
    · rw [hcoeff]
      exact (originalOrderCycle_endpoint_coefficients (q ≫ X.hom) v f hu.ne_zero
        (j x) (by rwa [coheight_eq_of_isOpenImmersion j])).2
    · exact (wholeComponentFiber_projection_eq_zero_of_coheight_ne
        X (j ≫ q) c hfin hdom 1 x hx).trans
        (Scheme.ord_eq_zero_of_coheight_neq_one
          (by rwa [coheight_eq_of_isOpenImmersion j]) _).symm

end AlgebraicGeometry.PrincipalFamilyUnitOpen
