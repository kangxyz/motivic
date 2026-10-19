/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Boundary.FiniteSourceBoundaryAffineNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.FixedParameterPrescribed
public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Graph.Retained

/-!
# Actual original graph frames after a coefficient-only shrink

The full-source affine ambient is constructed before the affine parameter and
its given whole-boundary graph frame are supplied. The parameter is unchanged,
and the exact original graph ideal and prescribed frame are retained.


Intended upstream module: `Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.FiniteSourceGraph`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom

universe u
namespace AlgebraicGeometry.Scheme.RelativeCurve

/-- One original coefficient localization constructs affine extension data for
any GIVEN whole-boundary frame of the original graph over each unchanged affine
smooth parameter. No affine ambient or replacement boundary frame is assumed. -/
theorem exists_coefficient_original_graph_frame
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {C B : Scheme.{u}}
    (f : C ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsFinite f]
    (b : B ⟶ C) [IsClosedImmersion b]
    [IsFinite ((b ≫ f) ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2)))] :
    ∃ r : R, r ≠ 0 ∧
      let m := ProjectiveSpace.map (algebraMap R (Localization.Away r)) (ULift.{u} (Fin 2))
      let Cr := pullback f m
      let br := pullback.lift (pullback.fst (b ≫ f) m ≫ b)
        (pullback.snd (b ≫ f) m) (by simp [Category.assoc, pullback.condition])
      let q := pullback.snd f m ≫ ProjectiveSpace.toSpec (Localization.Away r) (ULift.{u} (Fin 2))
      ∀ (T : Scheme.{u}) [IsAffine T] (j : T ⟶ Cr) [IsOpenImmersion j]
        [SmoothOfRelativeDimension 1 (j ≫ q)],
      let L := relativeCompactificationGraphLine q j
      ∀ e : (Modules.pullback (pullback.fst (pullback.snd (j ≫ q) q) br)).obj L.val ≅
          SheafOfModules.unit (pullback (pullback.snd (j ≫ q) q) br).ringCatSheaf,
      ∃ A : (pullback (j ≫ q) q).affineOpens,
        ∃ c : pullback (pullback.snd (j ≫ q) q) br ⟶ A.val.toScheme,
        ∃ hc : c ≫ A.val.ι = pullback.fst (pullback.snd (j ≫ q) q) br,
        Nonempty (PrescribedAffineFrameExtension A c L
          ((Modules.pullbackComp c A.val.ι).app L.val ≪≫
            (Modules.pullbackCongr hc).app L.val ≪≫ e)) := by
  obtain ⟨r, hr, W, hW, t, ht⟩ :=
    ProjectiveSpace.exists_affine_full_boundary_coefficient_neighborhood R
      (ULift.{u} (Fin 2)) 1 Equiv.ulift f b
  refine ⟨r, hr, ?_⟩
  let m := ProjectiveSpace.map (algebraMap R (Localization.Away r)) (ULift.{u} (Fin 2))
  let br : pullback (b ≫ f) m ⟶ pullback f m :=
    pullback.lift (pullback.fst (b ≫ f) m ≫ b) (pullback.snd (b ≫ f) m)
      (by simp [Category.assoc, pullback.condition])
  have hbr : br = (pullbackRightPullbackFstIso f m b).inv ≫
      pullback.snd b (pullback.fst f m) := by
    apply pullback.hom_ext <;> simp [br]
  have : IsClosedImmersion br := by rw [hbr]; infer_instance
  dsimp only
  intro T _ j _ _ e
  exact exists_fixedParameter_prescribedAffineFrameExtension
    (pullback.snd f m ≫ ProjectiveSpace.toSpec (Localization.Away r) (ULift.{u} (Fin 2)))
    _ br W hW t ht _ e

end AlgebraicGeometry.Scheme.RelativeCurve
