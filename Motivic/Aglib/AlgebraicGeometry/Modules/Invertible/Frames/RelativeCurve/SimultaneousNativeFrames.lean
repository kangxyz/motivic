/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.SimultaneousBoundaryFrames
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.BoundaryGraphBaseIso
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.BaseChange.TwistFrame
/-! # Constructed graph and full-boundary frames on one actual affine base

The compact target and its full finite boundary are only base changed. The smaller source
open is a parameter domain for the pencil and is not substituted for the retained target.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Hom
/-- The two required frames are genuinely produced, and both already use the native
spectrum presentation and projective twists of exactly the same smaller affine base. -/
theorem exists_simultaneous_native_boundary_frames
    (R : Type u) [CommRing R] (ι : Type u)
    {X Z C D : Scheme.{u}} [IsAffine X]
    (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
    (z : Z ⟶ X) [IsFinite (z ≫ q)]
    (f : C ⟶ ProjectiveSpace R ι) (d : D ⟶ C)
    [IsFinite ((d ≫ f) ≫ toSpec R ι)] (x : X) :
    ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧
    ∃ (V : (Spec (.of R)).Opens) (hV : IsAffineOpen V),
      let : IsAffine V.toScheme := hV
      q x ∈ V ∧
      ∃ h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U,
        IsAffineOpen (boundaryBaseSourceOpen q U V) ∧
        Nonempty (SheafOfModules.unit
          (pullback (boundaryBaseSourceProjection q U V ≫ V.toScheme.isoSpec.hom)
            (boundaryBaseLift q z U V h ≫ boundaryBaseSourceProjection q U V ≫
              V.toScheme.isoSpec.hom)).ringCatSheaf ≅
          idealModule (boundaryGraphTarget
            (boundaryBaseSourceProjection q U V ≫ V.toScheme.isoSpec.hom)
            (boundaryBaseLift q z U V h))) ∧
        Nonempty ((n : ℕ) →
          (Modules.pullback (boundaryBaseWholeMap (f ≫ toSpec R ι) d V ≫
            boundaryBaseProjectiveMap R ι f V)).obj
              (twistingSheaf Γ(V.toScheme, ⊤) ι (n : ℤ)) ≅
          SheafOfModules.unit ((d ≫ (f ≫ toSpec R ι)) ⁻¹ᵁ V).toScheme.ringCatSheaf) := by
  obtain ⟨U, hU, hx, V₁, hx₁, hz, ⟨a⟩⟩ :=
    exists_affine_relativeBoundaryFrame_over_base_neighborhood q z x
  let b := d ≫ (f ≫ toSpec R ι)
  have : IsFinite b := by simpa only [b, Category.assoc] using
    (inferInstance : IsFinite ((d ≫ f) ≫ toSpec R ι))
  let L := pullbackLineBundle (d ≫ f) (twistingLineBundle R ι 1)
  obtain ⟨V₂, hx₂, ⟨e₂⟩⟩ := exists_base_open_unitIso_of_isFinite b (q x) L
  obtain ⟨V, hV, hxV, hVV⟩ := exists_isAffineOpen_mem_and_subset
    (show q x ∈ V₁ ⊓ V₂ from ⟨hx₁, hx₂⟩)
  let : IsAffine V.toScheme := hV
  let h : ∀ t : Z, (z ≫ q) t ∈ V → z t ∈ U := fun t ht => hz t (hVV ht).1
  let W := b ⁻¹ᵁ V
  let eW := restrictUnitIsoOfLE L.val
    (show W ≤ b ⁻¹ᵁ V₂ from fun _ ht => (hVV ht).2) e₂
  let e₁ : (Modules.pullback (W.ι ≫ d ≫ f)).obj (twistingSheaf R ι 1) ≅
      SheafOfModules.unit W.toScheme.ringCatSheaf :=
    (Modules.pullbackComp W.ι (d ≫ f)).symm.app (twistingSheaf R ι 1) ≪≫
      (restrictFunctorIsoPullback W.ι).symm.app
        ((Modules.pullback (d ≫ f)).obj (twistingSheaf R ι 1)) ≪≫ eW
  let e := CoherentGraph.positiveTwistUnitIso R ι (W.ι ≫ d ≫ f) e₁
  have := boundaryBaseSourceProjection_smooth q U V
  have : IsSeparated (boundaryBaseSourceProjection q U V) := by
    dsimp [boundaryBaseSourceProjection]
    infer_instance
  refine ⟨U, hU, hx, V, hV, hxV, h, boundaryBaseSourceOpen_affine q U V hU hV,
    ⟨boundaryGraphFrameBaseIso _ _ V.toScheme.isoSpec
      (boundaryBaseCanonicalFrame q z U V h a)⟩,
    ⟨fun n => boundaryBaseWholeTwistFrame R ι f d V n (e n)⟩⟩
end AlgebraicGeometry.Scheme.Hom
