module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.OpenBoundaryCoordinate
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.CoproductUnitEndomorphism
/-! # The literal local canonical coordinate is the original unit-endomorphism pullback -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

theorem openDualBoundaryFrame_coordinate {Z C : Scheme.{u}} (z : Z ⟶ C) (U : C.Opens)
    (I : LineBundle C) (φ : I.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (E : (Modules.pullback z).obj (dualLineBundle C I).val ≅
      SheafOfModules.unit Z.ringCatSheaf) :
    pullbackSectionMap (z ∣_ U)
        (canonicalDualHom U.toScheme (restrictLineBundle U.ι I).val
          ((restrictFunctor U.ι).map φ ≫ (restrictUnitIso U.ι).hom)) ≫
        (openDualBoundaryFrame z U I E).hom =
      Scheme.Hom.unitEndomorphismPullback (z ⁻¹ᵁ U).ι
        (pullbackSectionMap z (canonicalDualHom C I.val φ) ≫ E.hom) := by
  symm
  apply Scheme.Hom.unitEndomorphismPullback_eq_of_restrict
  rw [pullbackSectionMap_openDualBoundaryFrame]
  simp only [Iso.hom_inv_id_assoc]

end AlgebraicGeometry.Scheme.Modules.Invertible
