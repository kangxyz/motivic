/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.CoproductFrame
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Twists.Finite

/-! # One coefficient neighborhood frames the full original finite boundary coproduct

Intended upstream module: `Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.FiniteCoproduct`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.ThickenedTwistFrames`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.CommonFrames`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom

/-- The boundary can be the actual thickened infinity: neither summand is reduced.
Choose O(1) once, restrict it to one affine coefficient open, and transport all degrees. -/
theorem exists_base_open_coproduct_boundary_twist_frames
    (R : Type u) [CommRing R] (ι : Type u) {C D Z : Scheme.{u}}
    (f : C ⟶ ProjectiveSpace R ι) (d : D ⟶ C) (z : Z ⟶ C)
    [IsFinite (d ≫ (f ≫ toSpec R ι))] [IsFinite (z ≫ (f ≫ toSpec R ι))]
    (x : Spec (.of R)) :
    ∃ (O : (Spec (.of R)).Opens) (hO : IsAffineOpen O),
      let : IsAffine O.toScheme := hO
      x ∈ O ∧ Nonempty ((n : ℕ) →
        (Modules.pullback
          (coprod.desc (boundaryBaseWholeMap (f ≫ toSpec R ι) d O)
            (boundaryBaseWholeMap (f ≫ toSpec R ι) z O) ≫
              boundaryBaseProjectiveMap R ι f O)).obj
          (twistingSheaf Γ(O.toScheme, ⊤) ι (n : ℤ)) ≅
            SheafOfModules.unit
              ((((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ O).toScheme ⨿
                ((z ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ O).toScheme)).ringCatSheaf) := by
  let g := coprod.desc d z
  let b := g ≫ (f ≫ toSpec R ι)
  have hb : b = coprod.desc (d ≫ (f ≫ toSpec R ι)) (z ≫ (f ≫ toSpec R ι)) := by
    simp only [b, g, coprod.desc_comp]
  have : IsFinite b := by rw [hb]; infer_instance
  let L := pullbackLineBundle (g ≫ f) (twistingLineBundle R ι 1)
  obtain ⟨V, hx, ⟨eV⟩⟩ := exists_base_open_unitIso_of_isFinite b x L
  obtain ⟨O, hO, hxO, hOV⟩ := exists_isAffineOpen_mem_and_subset hx
  let : IsAffine O.toScheme := hO
  let W := b ⁻¹ᵁ O
  let eW := restrictUnitIsoOfLE L.val
    (show W ≤ b ⁻¹ᵁ V from fun _ ht => hOV ht) eV
  let e₁ : (Modules.pullback (W.ι ≫ g ≫ f)).obj (twistingSheaf R ι 1) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Modules.pullbackComp W.ι (g ≫ f)).symm.app (twistingSheaf R ι 1) ≪≫
      (restrictFunctorIsoPullback W.ι).symm.app
        ((Modules.pullback (g ≫ f)).obj (twistingSheaf R ι 1)) ≪≫ eW
  let e := CoherentGraph.positiveTwistUnitIso R ι (W.ι ≫ g ≫ f) e₁
  exact ⟨O, hO, hxO, ⟨fun n => boundaryBaseCoproductTwistFrame R ι f d z O n (e n)⟩⟩

end AlgebraicGeometry.Scheme.Hom
