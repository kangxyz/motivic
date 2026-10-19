/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.CommonFiniteBase
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.FiniteCoproduct

/-! # Keep both original O(1) boundary frames on the same coefficient open

Intended upstream module: `Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.CommonFrames`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.NativeSimultaneousSectionChoice`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- All native positive twists are induced from this one supplied original O(1) frame.
This construction chooses neither a graph frame nor any section. -/
def boundaryBaseCoproductTwistFramesOfUnitIso
    (R : Type u) [CommRing R] (ι : Type u) {C D Z : Scheme.{u}}
    (f : C ⟶ ProjectiveSpace R ι) (d : D ⟶ C) (z : Z ⟶ C)
    (O : (Spec (.of R)).Opens) [IsAffine O.toScheme]
    (e : (Modules.restrictFunctor
      ((coprod.desc d z ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ O).ι).obj
        (pullbackLineBundle (coprod.desc d z ≫ f) (twistingLineBundle R ι 1)).val ≅
          SheafOfModules.unit
            ((coprod.desc d z ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ O).toScheme.ringCatSheaf)
    (n : ℕ) :
    (Modules.pullback
      (coprod.desc (boundaryBaseWholeMap (f ≫ toSpec R ι) d O)
        (boundaryBaseWholeMap (f ≫ toSpec R ι) z O) ≫
          boundaryBaseProjectiveMap R ι f O)).obj
      (twistingSheaf Γ(O.toScheme, ⊤) ι (n : ℤ)) ≅
        SheafOfModules.unit
          ((((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ O).toScheme ⨿
            ((z ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ O).toScheme)).ringCatSheaf := by
  let g := coprod.desc d z
  let W := (g ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ O
  let e₁ : (Modules.pullback (W.ι ≫ g ≫ f)).obj (twistingSheaf R ι 1) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Modules.pullbackComp W.ι (g ≫ f)).symm.app (twistingSheaf R ι 1) ≪≫
      (restrictFunctorIsoPullback W.ι).symm.app
        ((Modules.pullback (g ≫ f)).obj (twistingSheaf R ι 1)) ≪≫ e
  exact boundaryBaseCoproductTwistFrame R ι f d z O n
    (CoherentGraph.positiveTwistUnitIso R ι (W.ι ≫ g ≫ f) e₁ n)

/-- A common affine coefficient open inside the previously established free-chart base.
The two original O(1) frames are retained, before choosing the canonical marked frame
or any of the independently graded source and target sections. -/
theorem exists_common_base_boundary_unit_frames
    (R : Type u) [CommRing R] (ι κ : Type u)
    {C₁ D₁ Z₁ C₂ D₂ Z₂ : Scheme.{u}}
    (f₁ : C₁ ⟶ ProjectiveSpace R ι) (d₁ : D₁ ⟶ C₁) (z₁ : Z₁ ⟶ C₁)
    (f₂ : C₂ ⟶ ProjectiveSpace R κ) (d₂ : D₂ ⟶ C₂) (z₂ : Z₂ ⟶ C₂)
    [IsFinite (d₁ ≫ (f₁ ≫ toSpec R ι))] [IsFinite (z₁ ≫ (f₁ ≫ toSpec R ι))]
    [IsFinite (d₂ ≫ (f₂ ≫ toSpec R κ))] [IsFinite (z₂ ≫ (f₂ ≫ toSpec R κ))]
    (W : (Spec (.of R)).Opens) (x : Spec (.of R)) (hx : x ∈ W) :
    ∃ (O : (Spec (.of R)).Opens) (_hO : IsAffineOpen O), x ∈ O ∧ O ≤ W ∧
      Nonempty (((Modules.restrictFunctor
        ((coprod.desc d₁ z₁ ≫ (f₁ ≫ toSpec R ι)) ⁻¹ᵁ O).ι).obj
          (pullbackLineBundle (coprod.desc d₁ z₁ ≫ f₁) (twistingLineBundle R ι 1)).val ≅
            SheafOfModules.unit
              ((coprod.desc d₁ z₁ ≫ (f₁ ≫ toSpec R ι)) ⁻¹ᵁ O).toScheme.ringCatSheaf) ×
        ((Modules.restrictFunctor
          ((coprod.desc d₂ z₂ ≫ (f₂ ≫ toSpec R κ)) ⁻¹ᵁ O).ι).obj
            (pullbackLineBundle (coprod.desc d₂ z₂ ≫ f₂) (twistingLineBundle R κ 1)).val ≅
              SheafOfModules.unit
                ((coprod.desc d₂ z₂ ≫ (f₂ ≫ toSpec R κ)) ⁻¹ᵁ O).toScheme.ringCatSheaf)) := by
  have : IsFinite (coprod.desc d₁ z₁ ≫ (f₁ ≫ toSpec R ι)) := by
    rw [coprod.desc_comp]
    infer_instance
  have : IsFinite (coprod.desc d₂ z₂ ≫ (f₂ ≫ toSpec R κ)) := by
    rw [coprod.desc_comp]
    infer_instance
  exact exists_common_affine_base_unitIso_of_isFinite _ _ _ _ W x hx

end AlgebraicGeometry.Scheme.Hom
