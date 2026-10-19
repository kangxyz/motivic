/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Motivic.Aglib.AlgebraicGeometry.Scheme.FunctionField.NonzeroAffineFraction
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyEndpointCuts
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen

/-!
# Local fractions of the original principal polynomial family

All rational maps are the native generic-point stalk maps. Local equations use
sections on the prescribed open and their literal pullback under the original
polynomial projection. No reduced support or endpoint multiplicity is substituted.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyLocalFraction`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Cycles.PrincipalDivisor.PrincipalFamilySignedOrderCycle`,
`Motivic.Aglib.AlgebraicGeometry.Divisors.Order.OpenImmersion`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Scheme.Modules.Invertible.PolynomialBoundaryPencil

universe u

local instance nonempty_top (X : Scheme.{u}) [Nonempty X] : Nonempty (⊤ : X.Opens) :=
  ⟨⟨Classical.choice ‹Nonempty X›, trivial⟩⟩

namespace AlgebraicGeometry.Scheme

local instance functionField_nonempty_preimage {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (U : Y.Opens) [Nonempty U] : Nonempty (f ⁻¹ᵁ U) := by
  refine ⟨⟨genericPoint X, ?_⟩⟩
  change f (genericPoint X) ∈ U
  rw [map_genericPoint_of_isDominant X f]
  exact ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
    (by simpa using ‹Nonempty U›)

local instance functionField_openImmersion_dominant {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsOpenImmersion f] : IsDominant f := by
  constructor
  rw [denseRange_iff_closure_range, ← Set.univ_subset_iff,
    ← (genericPoint_spec Y).def]
  apply closure_mono
  rw [Set.singleton_subset_iff]
  exact ⟨genericPoint X, genericPoint_eq_of_isOpenImmersion f⟩

local instance nonempty_image_open {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) [Nonempty U] : Nonempty (f ''ᵁ U) := by
  obtain ⟨x, hx⟩ := ‹Nonempty U›
  exact ⟨⟨f x, ⟨x, hx, rfl⟩⟩⟩

/-- Native function-field pullback agrees with the germ of the actual open-section pullback. -/
theorem functionFieldMap_germ_open {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (U : Y.Opens) [Nonempty U]
    [Nonempty (f ⁻¹ᵁ U)] :
    Y.germToFunctionField U ≫ CommRingCat.ofHom (functionFieldMap f) =
      f.app U ≫ X.germToFunctionField (f ⁻¹ᵁ U) := by
  change Y.presheaf.germ U _ _ ≫
      (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap _) = _
  rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes,
    Scheme.Hom.germ_stalkMap]

/-- Native function-field maps compose through the actual scheme morphisms. -/
theorem functionFieldMap_comp {X Y Z : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] [IsIntegral Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [IsDominant f] [IsDominant g] :
    functionFieldMap (f ≫ g) = (functionFieldMap f).comp (functionFieldMap g) := by
  apply CommRingCat.hom_ext_iff.mp
  change Z.presheaf.stalkSpecializes _ ≫ (f ≫ g).stalkMap _ =
    (Z.presheaf.stalkSpecializes _ ≫ g.stalkMap _) ≫
      (Y.presheaf.stalkSpecializes _ ≫ f.stalkMap _)
  rw [Scheme.Hom.stalkMap_comp]
  simp only [Category.assoc]
  rw [← Category.assoc (g.stalkMap _), ← Scheme.Hom.stalkSpecializes_stalkMap]
  simp only [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]

/-- Open-immersion transport preserves the specified section's native rational germ. -/
theorem functionFieldMap_germ_appIso {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsOpenImmersion f]
    (U : X.Opens) [Nonempty U] (s : Γ(X, U)) :
    functionFieldMap f (Y.germToFunctionField (f ''ᵁ U) ((f.appIso U).inv s)) =
      X.germToFunctionField U s := by
  have h : (f.appIso U).inv ≫ Y.germToFunctionField (f ''ᵁ U) ≫
      CommRingCat.ofHom (functionFieldMap f) = X.germToFunctionField U := by
    rw [functionFieldMap_germ_open, ← Category.assoc, Scheme.Hom.appIso_inv_app]
    exact X.presheaf.germ_res _ _ _
  exact ConcreteCategory.congr_hom h s

/-- Restriction to the original open chart uses its canonical top-section isomorphism. -/
theorem functionFieldMap_germ_topIso {C : Scheme.{u}} [IsIntegral C]
    (U : C.Opens) [Nonempty U] (a : Γ(C, U)) :
    functionFieldMap U.ι (C.germToFunctionField U a) =
      U.toScheme.germToFunctionField ⊤ (U.topIso.inv a) := by
  have h := functionFieldMap_germ_appIso U.ι ⊤ (U.topIso.inv a)
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv] at h
  change functionFieldMap U.ι
    (C.germToFunctionField (U.ι ''ᵁ ⊤) (U.topIso.inv a)) =
      U.toScheme.germToFunctionField ⊤ (U.topIso.inv a) at h
  have he : C.germToFunctionField (U.ι ''ᵁ ⊤) (U.topIso.inv a) =
      C.germToFunctionField U a :=
    C.presheaf.germ_res_apply (eqToHom U.ι_image_top) _ _ a
  rwa [he] at h

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

attribute [local instance] Scheme.functionField_nonempty_preimage
  Scheme.functionField_openImmersion_dominant Scheme.nonempty_image_open

/-- The unchanged polynomial projection is surjective, by its literal zero section. -/
instance projection_surjective {R : Type u} [CommRing R] {C : Scheme.{u}}
    (p : C ⟶ Spec (.of R)) : Surjective (projection p) := by
  constructor
  intro x
  refine ⟨endpoint p 0 x, ?_⟩
  exact congrArg (fun f : C ⟶ C => f x) (endpoint_projection p 0)

/-- The literal parameter is preserved by the original open product map. -/
theorem lineMap_parameter {R : Type u} [CommRing R] {C W : Scheme.{u}}
    (p : C ⟶ Spec (.of R)) (v : W ⟶ C) :
    (lineMap p v).appTop (parameter p) = parameter (v ≫ p) := by
  unfold parameter
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop]
  simp only [lineMap, pullback.map, pullback.lift_snd, Category.comp_id]

variable {R : Type u} [CommRing R] {C W : Scheme.{u}}
    (p : C ⟶ Spec (.of R)) (v : W ⟶ C) [IsOpenImmersion v]
    [IsIntegral C] [IsIntegral W] [IsIntegral (parameterSpace p)]
    [IsIntegral (parameterSpace (v ≫ p))]

omit [IsIntegral C] [IsIntegral W] in
/-- Restricting the specified ambient rational function recovers the original polynomial. -/
theorem ambientRationalFunction_pullback (f : Γ(W, ⊤))
    [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)] :
    Scheme.functionFieldMap (lineMap p v) (ambientRationalFunction p v f) =
      (parameterSpace (v ≫ p)).germToFunctionField ⊤ (familySection (v ≫ p) f) := by
  unfold ambientRationalFunction ambientUnitSection ambientUnitOpen
  rw [Scheme.functionFieldMap_germ_appIso]
  exact (parameterSpace (v ≫ p)).presheaf.germ_res_apply _ _ _ _

/-- The specified unit-open rational function is the literal polynomial in the
pullback of the original rational function on the compactification. -/
theorem ambientRationalFunction_eq_polynomial (f : Γ(W, ⊤))
    [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)] :
    ambientRationalFunction p v f =
      (parameterSpace p).germToFunctionField ⊤ (parameter p) *
        Scheme.functionFieldMap (projection p)
          (C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f)) +
        (1 - (parameterSpace p).germToFunctionField ⊤ (parameter p)) := by
  apply (Scheme.functionFieldMap_injective (lineMap p v))
  rw [ambientRationalFunction_pullback]
  have ht : Scheme.functionFieldMap (lineMap p v)
      ((parameterSpace p).germToFunctionField ⊤ (parameter p)) =
      (parameterSpace (v ≫ p)).germToFunctionField ⊤ (parameter (v ≫ p)) := by
    have h := ConcreteCategory.congr_hom (Scheme.functionFieldMap_germ (lineMap p v))
      (parameter p)
    change Scheme.functionFieldMap (lineMap p v)
      ((parameterSpace p).germToFunctionField ⊤ (parameter p)) =
      (parameterSpace (v ≫ p)).germToFunctionField ⊤
        ((lineMap p v).appTop (parameter p)) at h
    simpa only [lineMap_parameter] using h
  have hp : (Scheme.functionFieldMap (lineMap p v)).comp
      (Scheme.functionFieldMap (projection p)) =
      (Scheme.functionFieldMap (projection (v ≫ p))).comp (Scheme.functionFieldMap v) := by
    simp only [← Scheme.functionFieldMap_comp, lineMap_projection]
  have hf := ConcreteCategory.congr_hom (Scheme.functionFieldMap_germ (projection (v ≫ p))) f
  change Scheme.functionFieldMap (projection (v ≫ p)) (W.germToFunctionField ⊤ f) =
    (parameterSpace (v ≫ p)).germToFunctionField ⊤ ((projection (v ≫ p)).appTop f) at hf
  simp only [map_add, map_mul, map_sub, map_one, ht]
  rw [← RingHom.comp_apply, hp, RingHom.comp_apply, Scheme.functionFieldMap_germ_appIso, hf]
  simp only [familySection, map_add, map_mul, map_sub, map_one]

/-- The original coordinate restricted to the literal inverse image of an open. -/
def localParameter (U : C.Opens) : Γ(parameterSpace p, (projection p) ⁻¹ᵁ U) :=
  (parameterSpace p).presheaf.map (homOfLE le_top).op (parameter p)

/-- The literal numerator on the original projection-preimage chart. -/
def localNumerator (U : C.Opens) (a b : Γ(C, U)) :
    Γ(parameterSpace p, (projection p) ⁻¹ᵁ U) :=
  localParameter p U * (projection p).app U a +
    (1 - localParameter p U) * (projection p).app U b

/-- The literal denominator on the same original projection-preimage chart. -/
def localDenominator (U : C.Opens) (b : Γ(C, U)) :
    Γ(parameterSpace p, (projection p) ⁻¹ᵁ U) := (projection p).app U b

/-- An actual fraction for the original rational function gives N/D for the
specified ambient principal family, without assuming the family equality. -/
theorem ambientRationalFunction_eq_local_fraction (f : Γ(W, ⊤))
    [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)]
    (U : C.Opens) [Nonempty U] (a b : Γ(C, U)) (hb : b ≠ 0)
    (hab : C.germToFunctionField U a / C.germToFunctionField U b =
      C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f)) :
    ambientRationalFunction p v f =
      (parameterSpace p).germToFunctionField ((projection p) ⁻¹ᵁ U)
          (localNumerator p U a b) /
        (parameterSpace p).germToFunctionField ((projection p) ⁻¹ᵁ U)
          (localDenominator p U b) := by
  have hs (s : Γ(C, U)) :
      (parameterSpace p).germToFunctionField ((projection p) ⁻¹ᵁ U)
        ((projection p).app U s) =
      Scheme.functionFieldMap (projection p) (C.germToFunctionField U s) := by
    exact (ConcreteCategory.congr_hom
      (Scheme.functionFieldMap_germ_open (projection p) U) s).symm
  have ht : (parameterSpace p).germToFunctionField ((projection p) ⁻¹ᵁ U)
      (localParameter p U) = (parameterSpace p).germToFunctionField ⊤ (parameter p) :=
    (parameterSpace p).presheaf.germ_res_apply _ _ _ _
  have hb' : Scheme.functionFieldMap (projection p) (C.germToFunctionField U b) ≠ 0 :=
    (map_ne_zero_iff _ (Scheme.functionFieldMap_injective (projection p))).mpr
      ((map_ne_zero_iff _ (C.germToFunctionField_injective U)).mpr hb)
  rw [ambientRationalFunction_eq_polynomial, ← hab, map_div₀]
  simp only [localNumerator, localDenominator, map_add, map_mul, map_sub, map_one, ht, hs]
  field_simp [hb']

/-- The same local equations compute H through each original ambient stalk map. -/
theorem ambientRationalFunction_eq_local_stalk_fraction (f : Γ(W, ⊤))
    [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)]
    (U : C.Opens) [Nonempty U] (a b : Γ(C, U)) (hb : b ≠ 0)
    (hab : C.germToFunctionField U a / C.germToFunctionField U b =
      C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f))
    (y : parameterSpace p) (hy : y ∈ (projection p) ⁻¹ᵁ U) :
    ambientRationalFunction p v f =
      algebraMap ((parameterSpace p).presheaf.stalk y) (parameterSpace p).functionField
          ((parameterSpace p).presheaf.germ ((projection p) ⁻¹ᵁ U) y hy
            (localNumerator p U a b)) /
        algebraMap ((parameterSpace p).presheaf.stalk y) (parameterSpace p).functionField
          ((parameterSpace p).presheaf.germ ((projection p) ⁻¹ᵁ U) y hy
            (localDenominator p U b)) := by
  simpa only [Scheme.algebraMap_germ_eq_germToFunctionField] using
    ambientRationalFunction_eq_local_fraction p v f U a b hb hab

/-- On every prescribed nonempty affine open, representatives of the actual
original rational function produce the exact ambient family fraction. -/
theorem exists_affine_ambientRationalFunction_fraction (f : Γ(W, ⊤))
    [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)]
    (hf : C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f) ≠ 0)
    (U : C.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    ∃ a b : Γ(C, U),
      (∀ (x : C) (hx : x ∈ U),
        C.presheaf.germ U x hx a ≠ 0 ∧ C.presheaf.germ U x hx b ≠ 0) ∧
      C.germToFunctionField U a / C.germToFunctionField U b =
        C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f) ∧
      ambientRationalFunction p v f =
        (parameterSpace p).germToFunctionField ((projection p) ⁻¹ᵁ U)
            (localNumerator p U a b) /
          (parameterSpace p).germToFunctionField ((projection p) ⁻¹ᵁ U)
            (localDenominator p U b) := by
  obtain ⟨a, b, hn, hab⟩ := C.exists_nonzero_affine_fraction U hU _ hf
  refine ⟨a, b, hn, hab, ambientRationalFunction_eq_local_fraction p v f U a b ?_ hab⟩
  obtain ⟨x, hx⟩ := ‹Nonempty U›
  intro hz
  exact (hn x hx).2 (by simp [hz])

section LiteralChart

variable {k : Type u} [Field k] (p : C ⟶ Spec (.of k))
    [IsIntegral (parameterSpace p)] [IsIntegral (parameterSpace (v ≫ p))]

/-- The native pullback of the specified ambient H to the original open chart
is the ratio of the literal endpoint-cut numerator and denominator. -/
theorem ambientRationalFunction_chart_fraction (f : Γ(W, ⊤))
    [Nonempty (unitOpen (v ≫ p) f)] [Nonempty (ambientUnitOpen p v f)]
    (U : C.Opens) [Nonempty U] [IsIntegral (parameterSpace (U.ι ≫ p))]
    (a b : Γ(C, U)) (hb : b ≠ 0)
    (hab : C.germToFunctionField U a / C.germToFunctionField U b =
      C.germToFunctionField (v ''ᵁ ⊤) ((v.appIso ⊤).inv f)) :
    Scheme.functionFieldMap (lineMap p U.ι) (ambientRationalFunction p v f) =
      (parameterSpace (U.ι ≫ p)).germToFunctionField ⊤
          (PrincipalFamilyEndpointCuts.numerator (U.ι ≫ p) (U.topIso.inv a) (U.topIso.inv b)) /
        (parameterSpace (U.ι ≫ p)).germToFunctionField ⊤
          (PrincipalFamilyEndpointCuts.denominator (U.ι ≫ p) (U.topIso.inv b)) := by
  have ht : Scheme.functionFieldMap (lineMap p U.ι)
      ((parameterSpace p).germToFunctionField ⊤ (parameter p)) =
      (parameterSpace (U.ι ≫ p)).germToFunctionField ⊤ (parameter (U.ι ≫ p)) := by
    have h := ConcreteCategory.congr_hom (Scheme.functionFieldMap_germ (lineMap p U.ι))
      (parameter p)
    change Scheme.functionFieldMap (lineMap p U.ι)
      ((parameterSpace p).germToFunctionField ⊤ (parameter p)) =
      (parameterSpace (U.ι ≫ p)).germToFunctionField ⊤
        ((lineMap p U.ι).appTop (parameter p)) at h
    simpa only [lineMap_parameter] using h
  have hp : (Scheme.functionFieldMap (lineMap p U.ι)).comp
      (Scheme.functionFieldMap (projection p)) =
      (Scheme.functionFieldMap (projection (U.ι ≫ p))).comp (Scheme.functionFieldMap U.ι) := by
    simp only [← Scheme.functionFieldMap_comp, lineMap_projection]
  have hs (s : Γ(C, U)) :
      Scheme.functionFieldMap (projection (U.ι ≫ p))
        (Scheme.functionFieldMap U.ι (C.germToFunctionField U s)) =
      (parameterSpace (U.ι ≫ p)).germToFunctionField ⊤
        ((projection (U.ι ≫ p)).appTop (U.topIso.inv s)) := by
    rw [Scheme.functionFieldMap_germ_topIso]
    exact ConcreteCategory.congr_hom (Scheme.functionFieldMap_germ (projection (U.ι ≫ p)))
      (U.topIso.inv s)
  have hb' : (parameterSpace (U.ι ≫ p)).germToFunctionField ⊤
      ((projection (U.ι ≫ p)).appTop (U.topIso.inv b)) ≠ 0 := by
    rw [← hs]
    exact (map_ne_zero_iff _ (Scheme.functionFieldMap_injective _)).mpr
      ((map_ne_zero_iff _ (Scheme.functionFieldMap_injective _)).mpr
        ((map_ne_zero_iff _ (C.germToFunctionField_injective U)).mpr hb))
  rw [ambientRationalFunction_eq_polynomial]
  simp only [map_add, map_mul, map_sub, map_one, ht]
  rw [← RingHom.comp_apply, hp, RingHom.comp_apply, ← hab]
  simp only [map_div₀, hs, PrincipalFamilyEndpointCuts.numerator,
    PrincipalFamilyEndpointCuts.denominator, map_add, map_mul, map_sub, map_one]
  field_simp [hb']

end LiteralChart

end AlgebraicGeometry.PrincipalFamilyUnitOpen
