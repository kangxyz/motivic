module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.RestrictDual
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestrictionUnit
/-! # The original boundary frame in the actual restricted dual coefficient -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Pullback.OpenRestriction
universe u
namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Transport a boundary frame through the actual open tensor coefficient comparison. -/
def openBoundaryFrame {Z C : Scheme.{u}} (z : Z ⟶ C) (U : C.Opens)
    (M : C.Modules) {N : U.toScheme.Modules}
    (q : (restrictFunctor U.ι).obj M ≅ N)
    (E : (Modules.pullback z).obj M ≅ SheafOfModules.unit Z.ringCatSheaf) :
    (Modules.pullback (z ∣_ U)).obj N ≅ SheafOfModules.unit (z ⁻¹ᵁ U).toScheme.ringCatSheaf :=
  ((Modules.pullback (z ∣_ U)).mapIso q).symm ≪≫
    ((localPullbackIso z U).app M).symm ≪≫
    (restrictFunctor (z ⁻¹ᵁ U).ι).mapIso E ≪≫ restrictUnitIso (z ⁻¹ᵁ U).ι

/-- The restricted original dual boundary frame, with no changed coordinate. -/
def openDualBoundaryFrame {Z C : Scheme.{u}} (z : Z ⟶ C) (U : C.Opens)
    (I : LineBundle C)
    (E : (Modules.pullback z).obj (dualLineBundle C I).val ≅
      SheafOfModules.unit Z.ringCatSheaf) :
    (Modules.pullback (z ∣_ U)).obj (dualLineBundle U.toScheme
      (restrictLineBundle U.ι I)).val ≅
        SheafOfModules.unit (z ⁻¹ᵁ U).toScheme.ringCatSheaf :=
  openBoundaryFrame z U (dualLineBundle C I).val (restrictDualIso U.ι I) E

end AlgebraicGeometry.Scheme.Modules.Invertible
