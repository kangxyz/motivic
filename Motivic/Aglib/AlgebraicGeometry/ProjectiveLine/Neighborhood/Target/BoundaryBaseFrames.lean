/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.FullBoundaryTwistFrames
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.TwistFrame
public import Motivic.Aglib.AlgebraicGeometry.Cohomology.Projective.Boundary.Twists.Finite
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Basic

/-! # Target boundary twist frames after coefficient-base restriction

The entire original infinity and marked scheme are retained, including their
nonreduced structure. Only the coefficient base is restricted. In particular,
this construction does not replace the whole affine-line parameter by a smaller
open. The native twists are transported along the actual coefficient-change map.


Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.BoundaryBaseFrames`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme Scheme.Modules Scheme.Modules.Invertible Scheme.RelativeCurvePencil
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine

/-- One genuine O(1) frame on the entire finite target boundary gives all degrees
on the same affine coefficient neighborhood. No degree has yet been selected. -/
theorem exists_target_base_open_boundary_twist_frames
    (R : Type u) [CommRing R] {D Z : Scheme.{u}}
    (d : D ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
    (z : Z ⟶ Spec (.of (Polynomial R)))
    [IsFinite (d ≫ toSpec R (ULift.{u} (Fin 2)))]
    [IsFinite ((z ≫ chart R 0) ≫ toSpec R (ULift.{u} (Fin 2)))]
    (x : Spec (.of R)) :
    ∃ (O : (Spec (.of R)).Opens) (hO : IsAffineOpen O),
      let : IsAffine O.toScheme := hO
      x ∈ O ∧ Nonempty ((n : ℕ) →
        (Modules.pullback
          (Scheme.Hom.boundaryBaseWholeMap
            ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))
            (fullTargetBoundaryMap (chart R 0) z d) O ≫
              Scheme.Hom.boundaryBaseProjectiveMap R (ULift.{u} (Fin 2)) (𝟙 _) O)).obj
          (twistingSheaf Γ(O.toScheme, ⊤) (ULift.{u} (Fin 2)) (n : ℤ)) ≅
            SheafOfModules.unit
              ((fullTargetBoundaryMap (chart R 0) z d ≫
                ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) ⁻¹ᵁ O).toScheme.ringCatSheaf) := by
  let f := 𝟙 (ProjectiveSpace R (ULift.{u} (Fin 2)))
  let g := fullTargetBoundaryMap (chart R 0) z d
  let b := g ≫ (f ≫ toSpec R (ULift.{u} (Fin 2)))
  have hb : b = coprod.desc (d ≫ toSpec R (ULift.{u} (Fin 2)))
      ((z ≫ chart R 0) ≫ toSpec R (ULift.{u} (Fin 2))) := by
    simp only [b, g, f, Category.id_comp, coprod.desc_comp]
  have : IsFinite b := by rw [hb]; infer_instance
  let L := pullbackLineBundle (g ≫ f) (twistingLineBundle R (ULift.{u} (Fin 2)) 1)
  obtain ⟨V, hx, ⟨eV⟩⟩ := exists_base_open_unitIso_of_isFinite b x L
  obtain ⟨O, hO, hxO, hOV⟩ := exists_isAffineOpen_mem_and_subset hx
  let : IsAffine O.toScheme := hO
  let W := b ⁻¹ᵁ O
  let eW := restrictUnitIsoOfLE L.val
    (show W ≤ b ⁻¹ᵁ V from fun _ ht => hOV ht) eV
  let e₁ : (Modules.pullback (W.ι ≫ g ≫ f)).obj
      (twistingSheaf R (ULift.{u} (Fin 2)) 1) ≅
        SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Modules.pullbackComp W.ι (g ≫ f)).symm.app
        (twistingSheaf R (ULift.{u} (Fin 2)) 1) ≪≫
      (restrictFunctorIsoPullback W.ι).symm.app
        ((Modules.pullback (g ≫ f)).obj (twistingSheaf R (ULift.{u} (Fin 2)) 1)) ≪≫ eW
  let e := Scheme.CoherentGraph.positiveTwistUnitIso R (ULift.{u} (Fin 2))
    (W.ι ≫ g ≫ f) e₁
  exact ⟨O, hO, hxO, ⟨fun n =>
    Scheme.Hom.boundaryBaseWholeTwistFrame R (ULift.{u} (Fin 2)) f g O n (e n)⟩⟩

end AlgebraicGeometry.RelativeProjectiveLine
