/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedBoundary
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Boundary.PrescribedPairPullback
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.Polynomial.FiniteFlat
/-! # The actual one-sided moving family

The full boundary controls the two moving divisors. Only its missing-boundary
part controls this family; the diagonal is allowed to meet the bad closed set.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
universe u
namespace AlgebraicGeometry.Scheme.Moving

/-- A genuine prescribed pair gives a finite-flat whole polynomial zero family on
original X, not merely on the smaller good open where its endpoint divisors lie. -/
theorem oneSided_pencil_finite_flat
    {R : Type u} [CommRing R] {S C X B D : Scheme.{u}}
    (bS : S ⟶ Spec (.of R)) [IsAffine S]
    (q : C ⟶ S) [IsProper q]
    (j : X ⟶ C) [IsOpenImmersion j] [X.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ q)]
    (z : B ⟶ C) (i : D ⟶ B)
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range (i ≫ z))
    (I T : LineBundle C) (φ : I.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (E : (Modules.pullback z).obj (dualLineBundle C I).val ≅
      SheafOfModules.unit B.ringCatSheaf)
    (a : SheafOfModules.unit C.ringCatSheaf ⟶
      (tensorLineBundle C T (dualLineBundle C I)).val)
    (b : SheafOfModules.unit C.ringCatSheaf ⟶ T.val)
    (ha : pullbackSectionMap z a ≫ pullbackTensorMap z T.val (dualLineBundle C I).val =
      tensorUnitSection (pullbackSectionMap z b) E.inv)
    [IsIso (pullbackSectionMap z a)]
    (hδ : pullbackSectionMap (i ≫ z) (canonicalDualHom C I.val φ) ≫
      (compositeBoundaryFrame i z (dualLineBundle C I).val E).hom = 𝟙 _) :
    let L := dualLineBundle C (tensorLineBundle C T (dualLineBundle C I))
    let a0 := sectionDualFunctional C (tensorLineBundle C T (dualLineBundle C I))
      (twistedIdealSection C I T φ b)
    let a1 := sectionDualFunctional C (tensorLineBundle C T (dualLineBundle C I)) a
    let f := familyMap ((j ≫ q) ≫ bS) (pullbackLineBundle j L)
      (Hom.pullbackToUnit a0 j) (Hom.pullbackToUnit a1 j)
    IsFinite (Hom.zeroInclusion f ≫ parameterMap bS (j ≫ q)) ∧
      Flat (Hom.zeroInclusion f ≫ parameterMap bS (j ≫ q)) := by
  have ha' := prescribed_pair_pullback i z T.val (dualLineBundle C I).val E a b ha
  have hs := oneSided_boundary_section (i ≫ z) I T φ b a
    (compositeBoundaryFrame i z (dualLineBundle C I).val E) ha' hδ
  have hi : IsIso (pullbackSectionMap (i ≫ z) a) := by
    rw [← pullbackSectionMap_comp i z a]
    change IsIso (((pullbackUnitIso i).inv ≫
      (Modules.pullback i).map (pullbackSectionMap z a)) ≫
        (Modules.pullbackComp i z).hom.app _)
    infer_instance
  have he : Hom.pullbackToUnit (sectionDualFunctional C
      (tensorLineBundle C T (dualLineBundle C I)) (twistedIdealSection C I T φ b))
      (i ≫ z) = Hom.pullbackToUnit (sectionDualFunctional C
      (tensorLineBundle C T (dualLineBundle C I)) a) (i ≫ z) := by
    rw [sectionDualFunctional_pullback, sectionDualFunctional_pullback]
    simp only [pulledSectionDualFunctional, hs]
  have hu := sectionDualFunctional_pullback_isIso (i ≫ z)
    (tensorLineBundle C T (dualLineBundle C I)) a
  have hu0 : IsIso (Hom.pullbackToUnit (sectionDualFunctional C
      (tensorLineBundle C T (dualLineBundle C I)) (twistedIdealSection C I T φ b))
      (i ≫ z)) := he ▸ hu
  have : IsIso ((Modules.pullback (i ≫ z)).map (sectionDualFunctional C
      (tensorLineBundle C T (dualLineBundle C I)) (twistedIdealSection C I T φ b))) := by
    have : IsIso ((Modules.pullback (i ≫ z)).map (sectionDualFunctional C
        (tensorLineBundle C T (dualLineBundle C I)) (twistedIdealSection C I T φ b)) ≫
        (pullbackUnitIso (i ≫ z)).hom) := hu0
    exact IsIso.of_isIso_comp_right _ (pullbackUnitIso (i ≫ z)).hom
  exact retained_familySource_finite_flat bS q j (i ≫ z) _ _ _ he hcover

end AlgebraicGeometry.Scheme.Moving
