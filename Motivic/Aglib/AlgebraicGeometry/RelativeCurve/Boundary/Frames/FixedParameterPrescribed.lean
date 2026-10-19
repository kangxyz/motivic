/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.FixedParameterBoundaryNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Prescribed.OpenRangeFrame
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Exact prescribed frames over an unchanged affine parameter

An actual affine ambient containing the whole original boundary pulls back to
an affine ambient over the unchanged affine parameter. The given boundary frame
then extends by the existing prescribed-frame theorem, with its exact equation.


Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.FixedParameterPrescribed`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.FiniteSourceGraph`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible

universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- The full inverse image of the source affine ambient is affine over the
unchanged affine parameter, not just over a new generic parameter open. -/
theorem isAffineOpen_fixedParameter_preimage
    {S C T : Scheme.{u}} [IsAffine S] [IsAffine T]
    (q : C ⟶ S) (a : T ⟶ S) (W : C.Opens) (hW : IsAffineOpen W) :
    IsAffineOpen ((pullback.snd a q) ⁻¹ᵁ W) := by
  have : IsAffine W.toScheme := hW
  have : IsAffine (pullback a (W.ι ≫ q)) := inferInstance
  let E := (pullbackRestrictIsoRestrict (pullback.snd a q) W).symm ≪≫
    pullbackLeftPullbackSndIso a q W.ι
  exact IsAffine.of_isIso E.hom

/-- Extend the GIVEN full boundary frame after pulling an actual source affine
ambient to the unchanged parameter. No new boundary-frame choice is made. -/
theorem exists_fixedParameter_prescribedAffineFrameExtension
    {S C T B : Scheme.{u}} [IsAffine S] [IsAffine T]
    (q : C ⟶ S) (a : T ⟶ S) (b : B ⟶ C) [IsClosedImmersion b]
    (W : C.Opens) (hW : IsAffineOpen W)
    (t : B ⟶ W.toScheme) (ht : t ≫ W.ι = b)
    (L : LineBundle (pullback a q))
    (e : (Modules.pullback (pullback.fst (pullback.snd a q) b)).obj L.val ≅
      SheafOfModules.unit (pullback (pullback.snd a q) b).ringCatSheaf) :
    ∃ A : (pullback a q).affineOpens,
      ∃ c : pullback (pullback.snd a q) b ⟶ A.val.toScheme,
      ∃ hc : c ≫ A.val.ι = pullback.fst (pullback.snd a q) b,
      Nonempty (PrescribedAffineFrameExtension A c L
        ((Modules.pullbackComp c A.val.ι).app L.val ≪≫
          (Modules.pullbackCongr hc).app L.val ≪≫ e)) := by
  let U := (pullback.snd a q) ⁻¹ᵁ W
  have hU : IsAffineOpen U := isAffineOpen_fixedParameter_preimage q a W hW
  let γ := pullback.fst (pullback.snd a q) b
  have hγ : Set.range γ ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (γ ≫ pullback.snd a q) x ∈ W
    rw [pullback.condition]
    have hp := congrArg (fun k : B ⟶ C =>
      k ((pullback.snd (pullback.snd a q) b) x)) ht
    exact hp ▸ (t ((pullback.snd (pullback.snd a q) b) x)).property
  let c := IsOpenImmersion.lift U.ι γ hγ
  have hc : c ≫ U.ι = γ := IsOpenImmersion.lift_fac U.ι γ hγ
  have : IsClosedImmersion (c ≫ U.ι) := by rw [hc]; infer_instance
  have : IsClosedImmersion c := IsClosedImmersion.of_comp c U.ι
  let A : (pullback a q).affineOpens := ⟨U, hU⟩
  refine ⟨A, c, hc, ?_⟩
  exact nonempty_prescribedAffineFrameExtension A c L
    ((Modules.pullbackComp c U.ι).app L.val ≪≫ (Modules.pullbackCongr hc).app L.val ≪≫ e)

end AlgebraicGeometry.Scheme.RelativeCurve
