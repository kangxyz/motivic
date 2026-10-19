/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedBaseRefinement
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.SimultaneousNativeFrames
/-! # The original full-boundary frames on the actual one-sided refinement -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Hom Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Moving
variable {S X C Z D : Scheme.{u}} (q : X ⟶ S) (π : C ⟶ S)
  (x : X ⟶ C) (hx : x ≫ π = q) (U : X.Opens) (W : S.Opens)
  (z : Z ⟶ X) (h : ∀ b : Z, (z ≫ q) b ∈ W → z b ∈ U) (d : D ⟶ C)

def refinedFullBoundaryFrame (M : (boundaryBaseCompactification π W).Modules)
    (e : (Modules.pullback (boundaryBaseWholeMap π (coprod.desc d (z ≫ x)) W)).obj M ≅
      SheafOfModules.unit ((coprod.desc d (z ≫ x) ≫ π) ⁻¹ᵁ W).toScheme.ringCatSheaf) :
    (Modules.pullback (coprod.desc (boundaryBaseWholeMap π d W)
      (boundaryBaseLift q z U W h ≫ refinedParameterInclusion q π x hx U W))).obj M ≅
      SheafOfModules.unit
        (((d ≫ π) ⁻¹ᵁ W).toScheme ⨿ (boundaryBaseClosedOpen q z W).toScheme).ringCatSheaf := by
  rw [refinedZero_eq_cover]
  exact boundaryBaseSourceBoundaryFrame q (𝟙 X) z z (by simp) π x
    (by simpa using hx) d U W h M e

theorem refinedParameter_disjoint [IsOpenImmersion x]
    (hd : Disjoint (Set.range x) (Set.range d)) :
    Disjoint (Set.range (refinedParameterInclusion q π x hx U W))
      (Set.range (boundaryBaseWholeMap π d W)) := by
  apply Set.disjoint_left.mpr
  rintro c ⟨a, rfl⟩ ⟨b, he⟩
  have he' := congrArg (fun c => (pullback.snd W.ι π) c) he
  change (boundaryBaseWholeMap π d W ≫ pullback.snd W.ι π) b =
    (refinedParameterInclusion q π x hx U W ≫ pullback.snd W.ι π) a at he'
  rw [boundaryBaseWholeMap_snd, refinedParameterInclusion_snd] at he'
  exact Set.disjoint_iff_forall_ne.mp hd ⟨_, rfl⟩ ⟨_, rfl⟩ he'.symm

theorem refinedGood_cover {A : Scheme.{u}} (a : A ⟶ X)
    (hc : ∀ c : C, c ∈ Set.range (a ≫ x) ∨
      c ∈ Set.range d ∨ c ∈ Set.range (z ≫ x)) :
    ∀ c : boundaryBaseCompactification π W,
      c ∈ Set.range (boundaryBaseRetainedTarget π W (a ≫ x)) ∨
      c ∈ Set.range (boundaryBaseWholeMap π d W) ∨
      c ∈ Set.range (boundaryBaseLift q z U W h ≫
        refinedParameterInclusion q π x hx U W) := by
  rw [refinedZero_eq_cover]
  exact boundaryBaseSourceBoundary_cover q (𝟙 X) z z (by simp) π x
    (by simpa using hx) d U W h (a ≫ x) hc

section Projective
variable (R : Type u) [CommRing R] (ι : Type u) {X C Z D : Scheme.{u}}
  (f : C ⟶ ProjectiveSpace R ι) (x : X ⟶ C)
  (U : X.Opens) (W : (Spec (.of R)).Opens) [IsAffine W.toScheme]
  (z : Z ⟶ X) (h : ∀ b : Z, (z ≫ (x ≫ f ≫ toSpec R ι)) b ∈ W → z b ∈ U)
  (d : D ⟶ C)

def refinedFullTwistFrame (n : ℕ)
    (e : (Modules.pullback
      (boundaryBaseWholeMap (f ≫ toSpec R ι) (coprod.desc d (z ≫ x)) W ≫
        boundaryBaseProjectiveMap R ι f W)).obj
      (twistingSheaf Γ(W.toScheme, ⊤) ι (n : ℤ)) ≅
        SheafOfModules.unit
          ((coprod.desc d (z ≫ x) ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ W).toScheme.ringCatSheaf) :
    (Modules.pullback (coprod.desc (boundaryBaseWholeMap (f ≫ toSpec R ι) d W)
      (boundaryBaseLift (x ≫ f ≫ toSpec R ι) z U W h ≫
        refinedParameterInclusion (x ≫ f ≫ toSpec R ι) (f ≫ toSpec R ι) x rfl U W) ≫
          boundaryBaseProjectiveMap R ι f W)).obj
      (twistingSheaf Γ(W.toScheme, ⊤) ι (n : ℤ)) ≅
        SheafOfModules.unit
          (((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ W).toScheme ⨿
            (boundaryBaseClosedOpen (x ≫ f ≫ toSpec R ι) z W).toScheme).ringCatSheaf :=
  (Modules.pullbackComp _ _).symm.app _ ≪≫
    refinedFullBoundaryFrame (x ≫ f ≫ toSpec R ι) (f ≫ toSpec R ι) x rfl U W z h d
      ((Modules.pullback (boundaryBaseProjectiveMap R ι f W)).obj
        (twistingSheaf Γ(W.toScheme, ⊤) ι (n : ℤ)))
      ((Modules.pullbackComp _ _).app _ ≪≫ e)
end Projective
end AlgebraicGeometry.Scheme.Moving
