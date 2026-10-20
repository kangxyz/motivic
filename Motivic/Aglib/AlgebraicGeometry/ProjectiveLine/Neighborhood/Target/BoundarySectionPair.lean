/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.FullBoundaryTwistFrames
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Basic
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.EtaleCurve

/-! # The original target graph pair on the relative projective line

The source is the entire original affine line and the compactification is the
actual relative projective line, with its identity projective presentation.
A single fixed marked graph frame determines the prescribed full boundary.
The target Serre degree is independent of all covering-curve and correction
degrees. The output retains both global sections, their exact boundary equation,
and both whole-zero finite-flat records. No norm or transfer identity is asserted.

The actual closed infinity, retained complement cover, and full-boundary twist
frames after the original-base restriction remain explicit geometric inputs.


Intended upstream module:
`Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.BoundarySectionPair`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.Target.NativeSectionPair`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ProjectiveSpace Scheme Scheme.Modules Scheme.Modules.Invertible
open Scheme.RelativeCurvePencil

universe u
namespace AlgebraicGeometry.RelativeProjectiveLine

variable (R : Type u) [CommRing R]

local notation "P₁" => ProjectiveSpace R (ULift (Fin 2))
local notation "π₁" => (𝟙 P₁) ≫ toSpec R (ULift (Fin 2))
local notation "j₁" => chart R 0

local instance : SmoothOfRelativeDimension 1 (Scheme.Hom.boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

local instance : SmoothOfRelativeDimension 1 (j₁ ≫ π₁) := by
  simpa only [Category.id_comp, chart_toSpec] using
    Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

/-- The whole target boundary frame uses the fixed original marked ideal frame,
and the canonical graph value at the chosen actual infinity. -/
def targetFullBoundaryFrame {Z D : Scheme.{u}}
    (z : Z ⟶ Spec (.of (Polynomial R)))
    (e : SheafOfModules.unit (pullback (Scheme.Hom.boundaryLineProjection R)
      (z ≫ Scheme.Hom.boundaryLineProjection R)).ringCatSheaf ≅
        Scheme.Hom.idealModule (Scheme.Hom.boundaryGraphTarget
          (Scheme.Hom.boundaryLineProjection R) z))
    (d : D ⟶ P₁) (hd : Disjoint (Set.range j₁) (Set.range d)) :
    (Modules.pullback (Scheme.Hom.fullBoundaryProductMap π₁ j₁ d z)).obj
      (dualLineBundle _ (Scheme.Hom.relativeCompactificationGraphLine π₁ j₁)).val ≅
        SheafOfModules.unit
          (pullback (pullback.snd (j₁ ≫ π₁) π₁) d ⨿
            pullback (j₁ ≫ π₁) (z ≫ j₁ ≫ π₁)).ringCatSheaf :=
  Scheme.Hom.relativeFullBoundaryFrame (Scheme.Hom.boundaryLineProjection R) π₁ j₁
    (𝟙 _) (by simp only [Category.id_comp, chart_toSpec]) z z (Category.comp_id z)
    (IsPullback.id_vert z) e d hd

/-- Serre produces the target pair using the identity map of the actual relative
projective line. Its own degree bound has no relation to the source-pair degree. -/
theorem exists_target_boundary_section_pair
    {Z D V : Scheme.{u}} [IsAffine V]
    [IsNoetherianRing Γ(Spec (.of (Polynomial R)), ⊤)]
    [IsLocallyNoetherian (pullback (j₁ ≫ π₁) π₁)]
    (z : Z ⟶ Spec (.of (Polynomial R))) [IsClosedImmersion (z ≫ j₁)]
    (e : SheafOfModules.unit (pullback (Scheme.Hom.boundaryLineProjection R)
      (z ≫ Scheme.Hom.boundaryLineProjection R)).ringCatSheaf ≅
        Scheme.Hom.idealModule (Scheme.Hom.boundaryGraphTarget
          (Scheme.Hom.boundaryLineProjection R) z))
    (d : D ⟶ P₁) [IsClosedImmersion d]
    (hd : Disjoint (Set.range j₁) (Set.range d))
    (v : V ⟶ P₁) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ π₁)]
    (hc : ∀ x : P₁, x ∈ Set.range v ∨ x ∈ Set.range d ∨ x ∈ Set.range (z ≫ j₁))
    (eFull : ∀ n : ℕ,
      (Modules.pullback (fullTargetBoundaryMap j₁ z d ≫ 𝟙 P₁)).obj
        (twistingSheaf R (ULift.{u} (Fin 2)) (n : ℤ)) ≅
          SheafOfModules.unit (D ⨿ Z).ringCatSheaf) :
    ∃ bound : ℕ, ∀ degree : ℕ, bound ≤ degree →
      let T := pullbackLineBundle
        (Scheme.ConstantCurve.affineSourceToProjectiveSpace R (ULift.{u} (Fin 2))
          (j₁ ≫ π₁) (𝟙 P₁))
        (twistingLineBundle Γ(Spec (.of (Polynomial R)), ⊤)
          (ULift.{u} (Fin 2)) (degree : ℤ))
      let M := dualLineBundle _ (Scheme.Hom.relativeCompactificationGraphLine π₁ j₁)
      let zA := Scheme.Hom.fullBoundaryProductMap π₁ j₁ d z
      let iA := retainedProductInclusion (j₁ ≫ π₁) π₁ v
      ∃ aS : SheafOfModules.unit (pullback (j₁ ≫ π₁) π₁).ringCatSheaf ⟶
        (tensorLineBundle _ T M).val,
      ∃ bS : SheafOfModules.unit (pullback (j₁ ≫ π₁) π₁).ringCatSheaf ⟶ T.val,
        pullbackSectionMap zA aS ≫ pullbackTensorMap zA T.val M.val =
          tensorUnitSection (pullbackSectionMap zA bS)
            (targetFullBoundaryFrame R z e d hd).inv ∧
        IsIso (pullbackSectionMap zA aS) ∧ IsIso (pullbackSectionMap zA bS) ∧
        Scheme.CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (j₁ ≫ π₁) π₁)
          iA (tensorLineBundle _ T M) aS ∧
        Scheme.CoherentGraph.SectionDivisorFiniteFlat (pullback.fst (j₁ ≫ π₁) π₁)
          iA T bS := by
  let zA := Scheme.Hom.fullBoundaryProductMap π₁ j₁ d z
  let iA := retainedProductInclusion (j₁ ≫ π₁) π₁ v
  have : IsClosedImmersion zA := Scheme.Hom.fullBoundaryProduct_isClosedImmersion π₁ j₁ d z hd
  have : IsAffine (retainedProduct (j₁ ≫ π₁) π₁ v) :=
    retainedProduct_affine (j₁ ≫ π₁) π₁ v
  have : SmoothOfRelativeDimension 1 (iA ≫ pullback.fst (j₁ ≫ π₁) π₁) :=
    retainedProduct_smooth (j₁ ≫ π₁) π₁ v
  exact Scheme.CoherentGraph.exists_affineSource_normalized_divisor_pair
    R (ULift.{u} (Fin 2)) 1 Equiv.ulift (j₁ ≫ π₁) (𝟙 P₁) zA
    (lambdaTwistFramesOfFullTargetFrame R (ULift.{u} (Fin 2)) (𝟙 P₁) j₁ z d eFull)
    iA (lambdaBoundary_retained_cover π₁ j₁ z d v hc)
    (dualLineBundle _ (Scheme.Hom.relativeCompactificationGraphLine π₁ j₁))
    (targetFullBoundaryFrame R z e d hd)

end AlgebraicGeometry.RelativeProjectiveLine
