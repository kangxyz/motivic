/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.Compactification
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.BaseChange
public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The original projective and affine lines over the smaller coefficient base

The affine-line identification uses the actual polynomial coefficient pushout.
It preserves the entire affine line; no smaller parameter open is introduced.


Intended upstream module: `Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.BaseChange`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.MarkedBaseChange`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] {Y : Scheme.{u}} [IsAffine Y]
  (b : Y ⟶ Spec (.of R))

/-- The actual projective coordinate map for the identity presentation is an iso. -/
def targetProjectiveBaseIso :
    pullback b ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2))) ≅
      ProjectiveSpace Γ(Y, ⊤) (ULift.{u} (Fin 2)) := by
  let f := Scheme.ConstantCurve.affineSourceToProjectiveSpace R (ULift.{u} (Fin 2)) b (𝟙 _)
  have : IsIso f :=
    (Scheme.ConstantCurve.affineSourceToProjectiveSpace_isPullback
      R (ULift.{u} (Fin 2)) b (𝟙 _)).isIso_snd_of_isIso
  exact asIso f

/-- The native affine line is the whole original affine line after coefficient change. -/
theorem targetAffineLineSquare :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (Scheme.ConstantCurve.affineSourceCoefficientMap R b))))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(Y, ⊤) →+* Polynomial Γ(Y, ⊤))) ≫
        Y.isoSpec.inv)
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) b := by
  have h := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.PolynomialLaurent.polynomial_isPushout
      (CommRingCat.ofHom (Scheme.ConstantCurve.affineSourceCoefficientMap R b)))
  have h' : IsPullback
      (Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (Scheme.ConstantCurve.affineSourceCoefficientMap R b))))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(Y, ⊤) →+* Polynomial Γ(Y, ⊤))))
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))
      (Y.isoSpec.inv ≫ b) := by
    simpa only [CommRingCat.PolynomialLaurent.polynomialMap,
      CommRingCat.PolynomialLaurent.coefficient, CommRingCat.hom_ofHom,
      Scheme.ConstantCurve.affineSourceCoefficientMap,
      Scheme.ConstantCurve.map_coefficientMap] using h.flip
  exact h'.of_iso (Iso.refl _) (Iso.refl _) Y.isoSpec.symm (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.symm_hom, Iso.refl_hom, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom])

/-- This iso keeps both literal coefficient-change projections. -/
def targetAffineBaseIso :
    Spec (.of (Polynomial Γ(Y, ⊤))) ≅
      pullback b (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) :=
  (targetAffineLineSquare R b).flip.isoPullback

@[reassoc]
theorem targetAffineBaseIso_hom_snd :
    (targetAffineBaseIso R b).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (Scheme.ConstantCurve.affineSourceCoefficientMap R b))) :=
  (targetAffineLineSquare R b).flip.isoPullback_hom_snd

/-- The original chart, base changed without changing either projection. -/
def targetBaseChart :
    pullback b (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ⟶
      pullback b ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2))) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ chart R 0) (by
    rw [Category.id_comp, Category.assoc, chart_toSpec]
    exact pullback.condition)

/-- Under the actual coefficient-change isos, the chart remains the original native chart. -/
theorem targetBaseChart_native :
    (targetAffineBaseIso R b).hom ≫ targetBaseChart R b ≫
      (targetProjectiveBaseIso R b).hom = chart Γ(Y, ⊤) 0 := by
  apply (Scheme.ConstantCurve.affineSourceProjectiveSquare
    R (ULift.{u} (Fin 2)) b).hom_ext
  · change (targetAffineBaseIso R b).hom ≫ targetBaseChart R b ≫
        Scheme.ConstantCurve.affineSourceToProjectiveSpace R (ULift.{u} (Fin 2)) b (𝟙 _) ≫
          ProjectiveSpace.map (Scheme.ConstantCurve.affineSourceCoefficientMap R b) _ = _
    rw [Scheme.ConstantCurve.affineSourceToProjectiveSpace_map,
      Category.comp_id]
    simp only [targetBaseChart, pullback.lift_snd, ← Category.assoc,
      targetAffineBaseIso_hom_snd]
    exact (chart_map (Scheme.ConstantCurve.affineSourceCoefficientMap R b) 0).symm
  · change (targetAffineBaseIso R b).hom ≫ targetBaseChart R b ≫
        Scheme.ConstantCurve.affineSourceToProjectiveSpace R (ULift.{u} (Fin 2)) b (𝟙 _) ≫
          toSpec Γ(Y, ⊤) _ ≫ Y.isoSpec.inv = _
    rw [Scheme.ConstantCurve.affineSourceToProjectiveSpace_toSpec_assoc]
    simp only [Iso.hom_inv_id, Category.comp_id,
      targetBaseChart, pullback.lift_fst, targetAffineBaseIso,
      IsPullback.isoPullback_hom_fst, ← Category.assoc, chart_toSpec]

/-- The native affine-line parameter is the full inverse image of the coefficient open. -/
def targetAffineOpenIso (O : (Spec (.of R)).Opens) [IsAffine O.toScheme] :
    Spec (.of (Polynomial Γ(O.toScheme, ⊤))) ≅
      ((Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) ⁻¹ᵁ O).toScheme :=
  targetAffineBaseIso R O.ι ≪≫
    (isPullback_morphismRestrict
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) O).isoPullback.symm

end AlgebraicGeometry.RelativeProjectiveLine
