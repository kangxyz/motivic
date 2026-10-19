/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Scheme.Coproduct.OpenRestriction
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.TwistFrame

/-! # Transport the same whole-boundary frame to the original restricted summands

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.CoproductFrame`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.FiniteCoproduct`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme.Hom

@[reassoc]
theorem coprodBoundaryPreimageIso_hom_wholeMap
    {D Z C S : Scheme.{u}} (π : C ⟶ S) (d : D ⟶ C) (z : Z ⟶ C) (O : S.Opens) :
    (coprodBoundaryPreimageIso π d z O).hom ≫
      boundaryBaseWholeMap π (coprod.desc d z) O =
      coprod.desc (boundaryBaseWholeMap π d O) (boundaryBaseWholeMap π z O) := by
  rw [← cancel_mono (pullback.snd O.ι π)]
  simp only [Category.assoc, boundaryBaseWholeMap_snd, coprod.desc_comp]
  exact coprodBoundaryPreimageIso_hom_map π d z O

/-- Pull back the identical coefficient-base frame along the canonical coproduct iso.
No frame is reselected, and both restricted summands retain their full scheme structure. -/
def boundaryBaseCoproductTwistFrame
    (R : Type u) [CommRing R] (ι : Type u) {C D Z : Scheme.{u}}
    (f : C ⟶ ProjectiveSpace R ι) (d : D ⟶ C) (z : Z ⟶ C)
    (O : (Spec (.of R)).Opens) [IsAffine O.toScheme] (n : ℕ)
    (e : (Modules.pullback
      (((coprod.desc d z ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ O).ι ≫ coprod.desc d z ≫ f)).obj
      (twistingSheaf R ι (n : ℤ)) ≅
        SheafOfModules.unit
          ((coprod.desc d z ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ O).toScheme.ringCatSheaf) :
    (Modules.pullback
      (coprod.desc (boundaryBaseWholeMap (f ≫ toSpec R ι) d O)
        (boundaryBaseWholeMap (f ≫ toSpec R ι) z O) ≫
          boundaryBaseProjectiveMap R ι f O)).obj
      (twistingSheaf Γ(O.toScheme, ⊤) ι (n : ℤ)) ≅
        SheafOfModules.unit
          ((((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ O).toScheme ⨿
            ((z ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ O).toScheme)).ringCatSheaf := by
  rw [← coprodBoundaryPreimageIso_hom_wholeMap_assoc]
  exact (Modules.pullbackComp (coprodBoundaryPreimageIso (f ≫ toSpec R ι) d z O).hom
      (boundaryBaseWholeMap (f ≫ toSpec R ι) (coprod.desc d z) O ≫
        boundaryBaseProjectiveMap R ι f O)).symm.app _ ≪≫
    (Modules.pullback (coprodBoundaryPreimageIso (f ≫ toSpec R ι) d z O).hom).mapIso
      (boundaryBaseWholeTwistFrame R ι f (coprod.desc d z) O n e) ≪≫
    pullbackUnitIso (coprodBoundaryPreimageIso (f ≫ toSpec R ι) d z O).hom

end AlgebraicGeometry.Scheme.Hom
