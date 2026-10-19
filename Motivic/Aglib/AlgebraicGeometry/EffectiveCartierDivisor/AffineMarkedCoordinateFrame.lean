/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.EtaleBoundaryIdeal

/-! # A canonical coordinate frame on the original affine marked domain

Only the canonical spectrum presentation of the marked domain is used. The final
frame lives on the original whole affine-line product with the original marked
scheme. No reduction, domain hypothesis, or further shrink is involved.


Intended upstream module:
`Aglib.AlgebraicGeometry.EffectiveCartierDivisor.AffineMarkedCoordinateFrame`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeCanonicalFrame`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Hom
variable (R : Type u) [CommRing R] {Z : Scheme.{u}} [IsAffine Z]
  (z : Z ⟶ Spec (.of (Polynomial R)))

/-- The literal coordinate map in the canonical spectrum presentation of Z. -/
abbrev affineMarkedCoordinateMap := Z.isoSpec.inv ≫ z

/-- The coordinate frame in that spectrum presentation is produced, not assumed. -/
def affineMarkedSpecFrame :
    SheafOfModules.unit (pullback (boundaryLineProjection R)
      (affineMarkedCoordinateMap R z ≫ boundaryLineProjection R)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget (boundaryLineProjection R)
        (affineMarkedCoordinateMap R z)) := by
  let ρ := (Spec.preimage (affineMarkedCoordinateMap R z)).hom
  have hρ : boundaryCoordinateMap R Γ(Z, ⊤) ρ = affineMarkedCoordinateMap R z :=
    Spec.map_preimage _
  rw [← hρ]
  exact boundaryCoordinateIdealIso R Γ(Z, ⊤) ρ

/-- Canonical product comparison, with the original Z retained on the left. -/
def affineMarkedProductIso :
    pullback (boundaryLineProjection R) (z ≫ boundaryLineProjection R) ≅
      pullback (boundaryLineProjection R)
        (affineMarkedCoordinateMap R z ≫ boundaryLineProjection R) where
  hom := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Z.isoSpec.hom) (by
    simpa only [affineMarkedCoordinateMap, Category.assoc, Iso.hom_inv_id_assoc] using
      (pullback.condition (f := boundaryLineProjection R) (g := z ≫ boundaryLineProjection R)))
  inv := pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Z.isoSpec.inv) (by
    simpa only [affineMarkedCoordinateMap, Category.assoc] using
      (pullback.condition (f := boundaryLineProjection R)
        (g := affineMarkedCoordinateMap R z ≫ boundaryLineProjection R)))
  hom_inv_id := by apply pullback.hom_ext <;> simp
  inv_hom_id := by apply pullback.hom_ext <;> simp

/-- This comparison identifies the actual graph maps, not only their supports. -/
@[reassoc]
theorem affineMarkedProductIso_graph :
    Z.isoSpec.hom ≫ boundaryGraphTarget (boundaryLineProjection R)
        (affineMarkedCoordinateMap R z) =
      boundaryGraphTarget (boundaryLineProjection R) z ≫
        (affineMarkedProductIso R z).hom := by
  apply pullback.hom_ext <;>
    simp [boundaryGraphTarget, affineMarkedProductIso, affineMarkedCoordinateMap]

/-- The single canonical target frame on the original whole affine-line product. -/
def affineMarkedCoordinateFrame :
    SheafOfModules.unit (pullback (boundaryLineProjection R)
      (z ≫ boundaryLineProjection R)).ringCatSheaf ≅
      idealModule (boundaryGraphTarget (boundaryLineProjection R) z) := by
  let v := idealPullbackMap
    (boundaryGraphTarget (boundaryLineProjection R) (affineMarkedCoordinateMap R z))
    (boundaryGraphTarget (boundaryLineProjection R) z)
    (affineMarkedProductIso R z).hom Z.isoSpec.hom (affineMarkedProductIso_graph R z)
  have : IsIso v := idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  exact (pullbackUnitIso (affineMarkedProductIso R z).hom).symm ≪≫
    (Modules.pullback (affineMarkedProductIso R z).hom).mapIso
      (affineMarkedSpecFrame R z) ≪≫ asIso v

/-- The final unit-to-ideal frame has exactly the original coordinate functional,
transported by the canonical marked-domain iso and no subsequent frame choice. -/
theorem affineMarkedCoordinateFrame_coordinate :
    (affineMarkedCoordinateFrame R z).hom ≫
        idealInclusion (boundaryGraphTarget (boundaryLineProjection R) z) =
      (pullbackUnitIso (affineMarkedProductIso R z).hom).inv ≫
        (Modules.pullback (affineMarkedProductIso R z).hom).map
          ((affineMarkedSpecFrame R z).hom ≫
            idealInclusion (boundaryGraphTarget (boundaryLineProjection R)
              (affineMarkedCoordinateMap R z))) ≫
          (pullbackUnitIso (affineMarkedProductIso R z).hom).hom := by
  dsimp only [affineMarkedCoordinateFrame, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, asIso_hom]
  simp only [Category.assoc]
  rw [idealPullbackMap_inclusion, Functor.map_comp]
  rfl

end AlgebraicGeometry.Scheme.Hom
