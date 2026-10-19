/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.PolynomialBoundaryPencil
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# The actual boundary-unit open of a principal polynomial family

The function is literally `t * f + (1 - t)` on the given neighborhood times
the polynomial line. Its unit locus need not be a product open. The entire
original boundary times the line lies in that locus when the original boundary
restriction of `f` is one. Transport to the unchanged ambient product uses the
native open-immersion section isomorphism. No finiteness or principal homotopy
relation is asserted here.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyUnitOpen`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.ComponentFacePlacement`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.PolynomialFamily.PrincipalFamilyLocalFraction`,
`Motivic.AlgebraicGeometry.Correspondences.Moving.Polynomial.PrincipalFamily`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.Invertible.PolynomialBoundaryPencil

universe u

namespace AlgebraicGeometry.PrincipalFamilyUnitOpen

variable {R : Type u} [CommRing R] {C W B : Scheme.{u}}

/-- The original map on products with the literal polynomial line. -/
def lineMap (p : C ⟶ Spec (.of R)) (v : W ⟶ C) :
    parameterSpace (v ≫ p) ⟶ parameterSpace p :=
  pullback.map (v ≫ p) _ p _ v (𝟙 _) (𝟙 _)
    (by simp) (by simp)

@[reassoc (attr := simp)] theorem lineMap_projection
    (p : C ⟶ Spec (.of R)) (v : W ⟶ C) :
    lineMap p v ≫ projection p = projection (v ≫ p) ≫ v := by
  simp only [lineMap, projection, pullback.map, pullback.lift_fst]

instance (p : C ⟶ Spec (.of R)) (v : W ⟶ C) [IsOpenImmersion v] :
    IsOpenImmersion (lineMap p v) := by
  unfold lineMap
  infer_instance

/-- The original numerator of the homotopy, before taking any unit open. -/
def familySection (p : W ⟶ Spec (.of R)) (f : Γ(W, ⊤)) :
    Γ(parameterSpace p, ⊤) :=
  parameter p * (projection p).appTop f + (1 - parameter p)

/-- Normalization holds on the whole original boundary product. -/
theorem boundary_familySection (p : W ⟶ Spec (.of R)) (b : B ⟶ W)
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1) :
    (lineMap p b).appTop (familySection p f) = 1 := by
  have h : (lineMap p b).appTop ((projection p).appTop f) = 1 := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
      lineMap_projection, Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hf, map_one]
  simp only [familySection, map_add, map_mul, map_sub, map_one, h, mul_one]
  ring

/-- The actual, possibly non-product, unit open of the literal family section. -/
def unitOpen (p : W ⟶ Spec (.of R)) (f : Γ(W, ⊤)) :
    (parameterSpace p).Opens :=
  (parameterSpace p).basicOpen (familySection p f)

/-- No boundary points are discarded when passing to the unit locus. -/
theorem boundary_mem_unitOpen (p : W ⟶ Spec (.of R)) (b : B ⟶ W)
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1) (x : parameterSpace (b ≫ p)) :
    lineMap p b x ∈ unitOpen p f := by
  have h : (lineMap p b) ⁻¹ᵁ unitOpen p f = ⊤ := by
    rw [unitOpen, Scheme.preimage_basicOpen_top, boundary_familySection p b f hf,
      Scheme.basicOpen_one]
  change x ∈ (lineMap p b) ⁻¹ᵁ unitOpen p f
  rw [h]
  trivial

/-- The section on the unit open is the literal restriction, not a new rational function. -/
def unitSection (p : W ⟶ Spec (.of R)) (f : Γ(W, ⊤)) :
    Γ(parameterSpace p, unitOpen p f) :=
  (parameterSpace p).presheaf.map
    ((parameterSpace p).basicOpen_le (familySection p f)).hom.op (familySection p f)

theorem isUnit_unitSection (p : W ⟶ Spec (.of R)) (f : Γ(W, ⊤)) :
    IsUnit (unitSection p f) :=
  (parameterSpace p).toRingedSpace.isUnit_res_basicOpen (familySection p f)

variable (p : C ⟶ Spec (.of R)) (v : W ⟶ C) [IsOpenImmersion v]

/-- The unit open inside the unchanged original ambient product. -/
def ambientUnitOpen (f : Γ(W, ⊤)) : (parameterSpace p).Opens :=
  lineMap p v ''ᵁ unitOpen (v ≫ p) f

/-- The exact original section transported along the original open immersion. -/
def ambientUnitSection (f : Γ(W, ⊤)) :
    Γ(parameterSpace p, ambientUnitOpen p v f) :=
  ((lineMap p v).appIso (unitOpen (v ≫ p) f)).inv (unitSection (v ≫ p) f)

theorem isUnit_ambientUnitSection (f : Γ(W, ⊤)) :
    IsUnit (ambientUnitSection p v f) :=
  (isUnit_unitSection (v ≫ p) f).map
    ((lineMap p v).appIso (unitOpen (v ≫ p) f)).inv.hom

/-- The complete original boundary product remains inside the original ambient unit open. -/
theorem boundary_mem_ambientUnitOpen (b : B ⟶ W) (f : Γ(W, ⊤))
    (hf : b.appTop f = 1) (x : parameterSpace (b ≫ (v ≫ p))) :
    (lineMap (v ≫ p) b ≫ lineMap p v) x ∈ ambientUnitOpen p v f := by
  exact ⟨lineMap (v ≫ p) b x, boundary_mem_unitOpen (v ≫ p) b f hf x, rfl⟩

/-- A nonempty original boundary supplies an actual point of the ambient unit
open, using the literal zero section of the parameter line. -/
theorem nonempty_ambientUnitOpen_of_boundary (b : B ⟶ W) [Nonempty B]
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1) :
    Nonempty (ambientUnitOpen p v f) := by
  obtain ⟨x⟩ := ‹Nonempty B›
  let y := endpoint (b ≫ (v ≫ p)) 0 x
  exact ⟨⟨(lineMap (v ≫ p) b ≫ lineMap p v) y,
    boundary_mem_ambientUnitOpen p v b f hf y⟩⟩

/-- The literal polynomial section on the full original neighborhood image. -/
def ambientSection (f : Γ(W, ⊤)) :
    Γ(parameterSpace p, lineMap p v ''ᵁ ⊤) :=
  ((lineMap p v).appIso ⊤).inv (familySection (v ≫ p) f)

/-- Transport and restriction commute for the same polynomial, before taking its germ. -/
theorem ambientUnitSection_eq_restriction (f : Γ(W, ⊤)) :
    ambientUnitSection p v f =
      (parameterSpace p).presheaf.map
        ((lineMap p v).opensFunctor.map
          (((parameterSpace (v ≫ p)).basicOpen_le
            (familySection (v ≫ p) f)).hom)).op
        (ambientSection p v f) := by
  exact ConcreteCategory.congr_hom
    ((lineMap p v).appIso_inv_naturality
      (((parameterSpace (v ≫ p)).basicOpen_le (familySection (v ≫ p) f)).hom.op))
    (familySection (v ≫ p) f)

/-- Pulling back recovers exactly the literal polynomial restriction. -/
theorem ambientUnitSection_pullback (f : Γ(W, ⊤)) :
    ((lineMap p v).appIso (unitOpen (v ≫ p) f)).hom
      (ambientUnitSection p v f) = unitSection (v ≫ p) f := by
  exact ConcreteCategory.congr_hom
    ((lineMap p v).appIso (unitOpen (v ≫ p) f)).inv_hom_id (unitSection (v ≫ p) f)

/-- The native rational germ belongs to the unchanged ambient product. Integrality
and nonemptiness are explicit; no connected-component assembly is hidden. -/
def ambientRationalFunction [IsIntegral (parameterSpace p)] (f : Γ(W, ⊤))
    [Nonempty (ambientUnitOpen p v f)] : (parameterSpace p).functionField :=
  (parameterSpace p).germToFunctionField (ambientUnitOpen p v f)
    (ambientUnitSection p v f)

end AlgebraicGeometry.PrincipalFamilyUnitOpen

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open AlgebraicGeometry.PrincipalFamilyUnitOpen
namespace AlgebraicGeometry.PrincipalFamilyUnitOpen
/-- The literal map on polynomial products is a base change of the original map. -/
theorem lineMap_isPullback {R : Type u} [CommRing R] {C W : Scheme.{u}}
    (p : C ⟶ Spec (.of R)) (v : W ⟶ C) :
    IsPullback (lineMap p v) (projection (v ≫ p)) (projection p) v := by
  let a := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  have h := (IsPullback.of_hasPullback (v ≫ p) a).flip.of_right'
    (IsPullback.of_hasPullback p a).flip
  convert h using 1
  apply pullback.hom_ext
  · simpa only [lineMap, pullback.map, pullback.lift_fst] using
      ((IsPullback.of_hasPullback p a).flip.lift_snd
        (pullback.snd (v ≫ p) a) (pullback.fst (v ≫ p) a ≫ v) _).symm
  · simpa only [lineMap, pullback.map, pullback.lift_snd, Category.comp_id] using
      ((IsPullback.of_hasPullback p a).flip.lift_fst
        (pullback.snd (v ≫ p) a) (pullback.fst (v ≫ p) a ≫ v) _).symm


end AlgebraicGeometry.PrincipalFamilyUnitOpen
end

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
open AlgebraicGeometry.PrincipalFamilyUnitOpen
namespace AlgebraicGeometry.PrincipalFamilyUnitOpen
/-- The complete original boundary cover gives the complete family boundary cover. -/
theorem complement_subset_ambientUnitOpen {R : Type u} [CommRing R]
    {C V W B : Scheme.{u}} (p : C ⟶ Spec (.of R))
    (j : V ⟶ C) (v : W ⟶ C) [IsOpenImmersion v] (b : B ⟶ W)
    (hcover : (Set.range j)ᶜ ⊆ Set.range (b ≫ v))
    (f : Γ(W, ⊤)) (hf : b.appTop f = 1) :
    (Set.range (lineMap p j))ᶜ ⊆ (ambientUnitOpen p v f : Set (parameterSpace p)) := by
  intro x hx
  have hx' : projection p x ∉ Set.range j := by
    rintro ⟨y, hy⟩
    obtain ⟨z, hzx, -⟩ := Scheme.exists_preimage_of_isPullback
      (lineMap_isPullback p j) x y hy.symm
    exact hx ⟨z, hzx⟩
  obtain ⟨y, hy⟩ := hcover hx'
  obtain ⟨z, hzx, hzy⟩ := Scheme.exists_preimage_of_isPullback
    (lineMap_isPullback p v) x (b y) hy.symm
  obtain ⟨w, hwz, -⟩ := Scheme.exists_preimage_of_isPullback
    (lineMap_isPullback (v ≫ p) b) z y hzy
  have hw := boundary_mem_ambientUnitOpen p v b f hf w
  change x ∈ ambientUnitOpen p v f
  simpa only [Scheme.Hom.comp_apply, hwz, hzx] using hw


end AlgebraicGeometry.PrincipalFamilyUnitOpen
end
