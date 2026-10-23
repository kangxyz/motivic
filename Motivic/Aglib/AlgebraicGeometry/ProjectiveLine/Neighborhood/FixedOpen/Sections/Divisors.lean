/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.FixedOpen.RetainedGeometry
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Neighborhood.FixedOpen.Sections.SerrePair
/-! # Whole finite flat psi zero schemes on the unchanged punctured neighborhood -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.RelativeProjectiveLine
variable (R : Type u) [CommRing R] (r : R)
  (V : (Spec (.of (Polynomial R))).Opens) [IsAffine V.toScheme]

/-- Every actual boundary-unit section has a whole finite flat zero scheme;
its original Cartier equation on V minus zero remains a monomorphism. -/
theorem fixedPsiSectionDivisor_finite_mono_flat
    (L : LineBundle (fixedPsiAmbient R r))
    (t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶ L.val)
    [IsIso (pullbackSectionMap (fixedPsiBoundaryMap R r V) t)] :
    let q := pullback.fst (fixedPsiProjection R r) (ProjectiveSpace.toSpec R _)
    let j := fixedPsiRetainedInclusion R r V
    let a := sectionDualFunctional (fixedPsiAmbient R r) L t
    IsFinite (Scheme.Modules.Hom.zeroInclusion a ≫ q) ∧
      Flat (Scheme.Modules.Hom.zeroInclusion a ≫ q) ∧
      Set.range (Scheme.Modules.Hom.zeroInclusion a) ⊆ Set.range j ∧
      IsFinite (Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Hom.pullbackToUnit a j) ≫ j ≫ q) ∧
      Mono (Scheme.Modules.Hom.pullbackToUnit a j) ∧
      Flat (Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Hom.pullbackToUnit a j) ≫ j ≫ q) := by
  have := fixedPsiRetainedCurve_affine R r V
  have := fixedPsiRetainedCurve_smooth R r V
  obtain ⟨hfin, hflat⟩ := sectionDualFunctional_whole_zero_finite_flat
    (fixedPsiBoundaryMap R r V) (pullback.fst (fixedPsiProjection R r)
      (ProjectiveSpace.toSpec R _)) (fixedPsiRetainedInclusion R r V) L t
    (fixedPsiRetained_boundary_cover R r V)
  exact ⟨hfin, hflat,
    sectionDualFunctional_zero_range (fixedPsiBoundaryMap R r V)
      (fixedPsiRetainedInclusion R r V) L t (fixedPsiRetained_boundary_cover R r V),
    sectionDualFunctional_finite_mono_flat_on_open (fixedPsiBoundaryMap R r V)
      (pullback.fst (fixedPsiProjection R r) (ProjectiveSpace.toSpec R _))
      (fixedPsiRetainedInclusion R r V) L t (fixedPsiRetained_boundary_cover R r V)⟩

/-- The actual native positive twist tensored with the actual unit line. -/
def fixedPsiSectionLine (d : ℕ) : LineBundle (fixedPsiAmbient R r) :=
  tensorLineBundle _ (pullbackLineBundle (fixedPsiProjectiveIso R r).hom
    (ProjectiveSpace.twistingLineBundle Γ((fixedPsiSource R r).toScheme, ⊤)
      (ULift.{u} (Fin 2)) (d : ℤ)))
    ⟨SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf,
      isLocallyRankOne_of_iso _
        (coproductUniqueIso (fun _ : PUnit.{u + 1} =>
          SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf))
        (trivialLineBundle (fixedPsiAmbient R r)).property⟩

/-- The entire zero scheme and the retained Cartier equation, with no source refinement. -/
def FixedPsiSectionFiniteFlat (d : ℕ)
    (t : SheafOfModules.unit (fixedPsiAmbient R r).ringCatSheaf ⟶
      (fixedPsiSectionLine R r d).val) : Prop :=
  let q := pullback.fst (fixedPsiProjection R r) (ProjectiveSpace.toSpec R _)
  let j := fixedPsiRetainedInclusion R r V
  let a := sectionDualFunctional (fixedPsiAmbient R r) (fixedPsiSectionLine R r d) t
  IsFinite (Scheme.Modules.Hom.zeroInclusion a ≫ q) ∧
    Flat (Scheme.Modules.Hom.zeroInclusion a ≫ q) ∧
    Set.range (Scheme.Modules.Hom.zeroInclusion a) ⊆ Set.range j ∧
    IsFinite (Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Hom.pullbackToUnit a j) ≫ j ≫ q) ∧
    Mono (Scheme.Modules.Hom.pullbackToUnit a j) ∧
    Flat (Scheme.Modules.Hom.zeroInclusion (Scheme.Modules.Hom.pullbackToUnit a j) ≫ j ≫ q)

end AlgebraicGeometry.RelativeProjectiveLine
