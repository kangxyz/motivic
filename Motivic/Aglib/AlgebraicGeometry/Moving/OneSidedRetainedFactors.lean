/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedSectionTransport
/-! # Original moving divisor factors in the larger homotopy target -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible PolynomialBoundaryPencil
universe u
namespace AlgebraicGeometry.Scheme.Moving

/-- An actual coefficient isomorphism preserves support after actual open restriction. -/
theorem zeroSupport_precomp_restrict {C X V : Scheme.{u}} {M : C.Modules}
    (a : M ⟶ SheafOfModules.unit C.ringCatSheaf) [M.IsQuasicoherent]
    (j : X ⟶ C) [IsOpenImmersion j] (w : V ⟶ X)
    (h : Set.range (Hom.zeroInclusion a) ⊆ Set.range (w ≫ j))
    {N : X.Modules} (e : N ≅ (Modules.pullback j).obj M) :
    Set.range (Hom.zeroInclusion (e.hom ≫ Hom.pullbackToUnit a j)) ⊆ Set.range w := by
  change Set.range (Hom.imageIdealData (e.hom ≫ Hom.pullbackToUnit a j)).subschemeι ⊆ _
  rw [imageIdealData_precompIso]
  exact zeroSupport_restrict a j w h

/-- The same original denominator also has a finite-flat regular divisor on X,
although it was constructed to avoid the larger boundary and lie in V. -/
theorem OneSidedSections.denominator_on_target
    {R : Type u} [CommRing R] {S C B D X V : Scheme.{u}}
    (bS : S ⟶ Spec (.of R)) [IsAffine S] (q : C ⟶ S) [IsProper q]
    (z : B ⟶ C) (i : D ⟶ B) (j : X ⟶ C) [IsOpenImmersion j] [X.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)] (v : V ⟶ C)
    (I T : LineBundle C) (φ : I.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (E : (Modules.pullback z).obj (dualLineBundle C I).val ≅
      SheafOfModules.unit B.ringCatSheaf)
    (s : OneSidedSections bS q z i j v I T φ E)
    (hc : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range z) :
    CoherentGraph.SectionDivisorFiniteFlat q j T s.denominator := by
  let := s.denominator_unit
  exact CoherentGraph.sectionDivisorFiniteFlat_of_boundary_unit z q j hc T s.denominator

/-- Both actual endpoint supports lie in the good retained open. -/
theorem OneSidedSections.retained_supports
    {R : Type u} [CommRing R] {S C B D X V : Scheme.{u}}
    (bS : S ⟶ Spec (.of R)) (q : C ⟶ S)
    (z : B ⟶ C) (i : D ⟶ B) (j : X ⟶ C) [IsOpenImmersion j] (w : V ⟶ X)
    (I T : LineBundle C) (φ : I.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (E : (Modules.pullback z).obj (dualLineBundle C I).val ≅
      SheafOfModules.unit B.ringCatSheaf)
    (s : OneSidedSections bS q z i j (w ≫ j) I T φ E)
    {N : X.Modules}
    (e : N ≅ (Modules.pullback j).obj
      (dualLineBundle C (tensorLineBundle C T (dualLineBundle C I))).val) :
    Set.range (Hom.zeroInclusion (e.hom ≫ Hom.pullbackToUnit
      (sectionDualFunctional C (tensorLineBundle C T (dualLineBundle C I)) s.numerator) j))
        ⊆ Set.range w ∧
      Set.range (Hom.zeroInclusion (Hom.pullbackToUnit
        (sectionDualFunctional C T s.denominator) j)) ⊆ Set.range w := by
  have : (dualLineBundle C T).val.IsQuasicoherent := by
    have := finiteLocallyFree_of_isLocallyRankOne (dualLineBundle C T).val
      (dualLineBundle C T).property
    infer_instance
  let A := tensorLineBundle C T (dualLineBundle C I)
  have : (dualLineBundle C A).val.IsQuasicoherent := by
    have := finiteLocallyFree_of_isLocallyRankOne (dualLineBundle C A).val
      (dualLineBundle C A).property
    infer_instance
  exact ⟨zeroSupport_precomp_restrict (sectionDualFunctional C A s.numerator) j w
      s.numerator_divisor.2.2.1 e,
    zeroSupport_restrict (sectionDualFunctional C T s.denominator) j w
      s.denominator_divisor.2.2.1⟩

end AlgebraicGeometry.Scheme.Moving
