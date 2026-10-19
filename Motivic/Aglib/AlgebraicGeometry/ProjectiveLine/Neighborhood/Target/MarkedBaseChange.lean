/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.BaseChange
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.MarkedDiagram
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.FullBoundaryTwistFrames

/-! # The original marked domain and full target boundary in native base coordinates

Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.MarkedBaseChange`.
Incoming project consumers:
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.`
Module suffix: `RelativeAffineLine.Diagrams.AffineRefinement`,
`Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Source.NativeParameter`,
`Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeCanonicalFrame`,
`Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeGeometry`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme Scheme.Modules Scheme.Hom Scheme.RelativeCurvePencil
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R]
  (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]

@[reassoc]
theorem targetAffineOpenIso_inv_coordinate :
    (targetAffineOpenIso R O).inv ≫
      Spec.map (CommRingCat.ofHom
        (Polynomial.mapRingHom (Scheme.ConstantCurve.affineSourceCoefficientMap R O.ι))) =
      ((boundaryLineProjection R) ⁻¹ᵁ O).ι := by
  rw [← targetAffineBaseIso_hom_snd R O.ι]
  simp only [targetAffineOpenIso, Iso.trans_inv, Iso.symm_inv, Category.assoc,
    Iso.inv_hom_id_assoc, IsPullback.isoPullback_hom_snd]

/-- The whole native affine-line projection is exactly the original restricted
projection followed by the canonical spectrum presentation of the base. -/
@[reassoc]
theorem targetAffineOpenIso_inv_projection :
    (targetAffineOpenIso R O).inv ≫ boundaryLineProjection Γ(O.toScheme, ⊤) =
      ((boundaryLineProjection R) ∣_ O) ≫ O.toScheme.isoSpec.hom := by
  rw [← cancel_mono O.toScheme.isoSpec.inv]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← (targetAffineLineSquare R O.ι).flip.isoPullback_hom_fst]
  simp only [targetAffineOpenIso, targetAffineBaseIso, Iso.trans_inv, Iso.symm_inv,
    Category.assoc, Iso.inv_hom_id_assoc]
  exact (isPullback_morphismRestrict (boundaryLineProjection R) O).isoPullback_hom_fst

variable {Z D : Scheme.{u}} (z : Z ⟶ Spec (.of (Polynomial R)))

/-- The original marked scheme over O, mapped into the whole native affine line. -/
def targetNativeMarked : ((z ≫ boundaryLineProjection R) ⁻¹ᵁ O).toScheme ⟶
    Spec (.of (Polynomial Γ(O.toScheme, ⊤))) :=
  (z ∣_ ((boundaryLineProjection R) ⁻¹ᵁ O)) ≫ (targetAffineOpenIso R O).inv

/-- Use the checked original marked-open comparison, not a substitute marked scheme. -/
def targetMarkedOpenIso :
    ((z ≫ boundaryLineProjection R) ⁻¹ᵁ O).toScheme ≅
      (((z ≫ chart R 0) ≫ ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ O).toScheme :=
  boundaryBaseMarkedOpenIso (boundaryLineProjection R) (𝟙 _)
    ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2))) (chart R 0)
    (by simp only [Category.id_comp, chart_toSpec]) z z (Category.comp_id z) O

/-- The native marked point followed by the native chart is the actual restricted
original marked-to-projective map. -/
theorem targetNativeMarked_chart :
    targetNativeMarked R O z ≫ chart Γ(O.toScheme, ⊤) 0 =
      (targetMarkedOpenIso R O z).hom ≫
        boundaryBaseWholeMap ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2))) (z ≫ chart R 0) O ≫
          (targetProjectiveBaseIso R O.ι).hom := by
  have : IsOpenImmersion
      (ProjectiveSpace.map (Scheme.ConstantCurve.affineSourceCoefficientMap R O.ι)
        (ULift.{u} (Fin 2))) := MorphismProperty.of_isPullback
    (Scheme.ConstantCurve.affineSourceProjectiveSquare R (ULift.{u} (Fin 2)) O.ι).flip
    inferInstance
  rw [← cancel_mono
    (ProjectiveSpace.map (Scheme.ConstantCurve.affineSourceCoefficientMap R O.ι)
      (ULift.{u} (Fin 2)))]
  simp only [Category.assoc, chart_map]
  change targetNativeMarked R O z ≫ _ ≫ chart R 0 =
    (targetMarkedOpenIso R O z).hom ≫ _ ≫
      Scheme.ConstantCurve.affineSourceToProjectiveSpace R (ULift.{u} (Fin 2)) O.ι (𝟙 _) ≫ _
  rw [Scheme.ConstantCurve.affineSourceToProjectiveSpace_map, Category.comp_id]
  simp only [targetNativeMarked, Category.assoc, targetAffineOpenIso_inv_coordinate_assoc,
    morphismRestrict_ι_assoc, boundaryBaseWholeMap_snd,
    targetMarkedOpenIso, boundaryBaseMarkedOpenIso]
  exact (Scheme.isoOfEq_hom_ι_assoc Z _ (z ≫ chart R 0)).symm

variable (d : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))

/-- The actual original infinity, in native coordinates over O. -/
def targetNativeInfinity :
    ((d ≫ ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ O).toScheme ⟶
      ProjectiveSpace Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)) :=
  boundaryBaseWholeMap ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2))) d O ≫
    (targetProjectiveBaseIso R O.ι).hom

/-- The exact full target boundary map, with original scheme structures retained. -/
@[reassoc]
theorem targetFullBoundary_native :
    (coprod.mapIso (Iso.refl
      (((d ≫ ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ O).toScheme))
        (targetMarkedOpenIso R O z)).hom ≫
      (coprod.desc (boundaryBaseWholeMap ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2))) d O)
        (boundaryBaseWholeMap ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2))) (z ≫ chart R 0) O) ≫
          (targetProjectiveBaseIso R O.ι).hom) =
      fullTargetBoundaryMap (chart Γ(O.toScheme, ⊤) 0)
        (targetNativeMarked R O z) (targetNativeInfinity R O d) := by
  apply coprod.hom_ext
  · simp [fullTargetBoundaryMap, targetNativeInfinity]
  · simpa only [coprod.mapIso_hom, coprod.inr_map_assoc, Category.assoc,
      coprod.inr_desc, coprod.inr_desc_assoc, fullTargetBoundaryMap] using
        (targetNativeMarked_chart R O z).symm

/-- Transport the same full-boundary frame; no new choice is made. -/
def targetNativeFullBoundaryFrame (n : ℕ)
    (e : (Modules.pullback
      (coprod.desc (boundaryBaseWholeMap ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2))) d O)
        (boundaryBaseWholeMap ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2))) (z ≫ chart R 0) O) ≫
          (targetProjectiveBaseIso R O.ι).hom)).obj
      (twistingSheaf Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit
          ((((d ≫ ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ O).toScheme ⨿
            (((z ≫ chart R 0) ≫
              ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ O).toScheme).ringCatSheaf)) :
    (Modules.pullback
      (fullTargetBoundaryMap (chart Γ(O.toScheme, ⊤) 0)
        (targetNativeMarked R O z) (targetNativeInfinity R O d))).obj
      (twistingSheaf Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)) (n : ℤ)) ≅
        SheafOfModules.unit
          ((((d ≫ ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ O).toScheme ⨿
            ((z ≫ boundaryLineProjection R) ⁻¹ᵁ O).toScheme).ringCatSheaf) := by
  rw [← targetFullBoundary_native R O z d]
  exact (Modules.pullbackComp _ _).symm.app _ ≪≫
    (Modules.pullback _).mapIso e ≪≫ pullbackUnitIso _

end AlgebraicGeometry.RelativeProjectiveLine
