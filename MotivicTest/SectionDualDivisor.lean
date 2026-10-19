module
import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.SectionDualDivisor

/-! # Actual global sections give whole finite flat zero schemes -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u

variable {X B U S : Scheme.{u}} (i : B ⟶ X) (q : X ⟶ S) [IsProper q] [IsAffine S]
  (j : U ⟶ X) [IsOpenImmersion j] [U.IsQuasiAffine]
  [SmoothOfRelativeDimension 1 (j ≫ q)] (L : LineBundle X)
  (s : SheafOfModules.unit X.ringCatSheaf ⟶ L.val) [IsIso (pullbackSectionMap i s)]
  (hcover : ∀ x : X, x ∈ Set.range j ∨ x ∈ Set.range i)

example : IsFinite (Hom.zeroInclusion (sectionDualFunctional X L s) ≫ q) ∧
    Flat (Hom.zeroInclusion (sectionDualFunctional X L s) ≫ q) :=
  sectionDualFunctional_whole_zero_finite_flat i q j L s hcover

example : Mono (Hom.pullbackToUnit (sectionDualFunctional X L s) j) :=
  (sectionDualFunctional_finite_mono_flat_on_open i q j L s hcover).2.1
