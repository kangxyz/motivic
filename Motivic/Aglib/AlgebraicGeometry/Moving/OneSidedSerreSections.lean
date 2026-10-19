/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedPencil
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Sections.DivisorPairs.Normalized
/-! # Serre constructs the one-sided moving sections and their whole zero family

This intermediate producer retains the genuine compact curve and prescribed full
boundary frame as input. It assumes no sections, correspondences, zero finiteness,
or homotopy. The good open V and the larger homotopy target X are kept distinct.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open ProjectiveSpace Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
universe u
namespace AlgebraicGeometry.Scheme.Moving

/-- Actual moving sections, including finite-flat divisors in V and the whole
finite-flat polynomial family in X. -/
structure OneSidedSections {R : Type u} [CommRing R]
    {S C B D X V : Scheme.{u}} (bS : S ⟶ Spec (.of R)) (q : C ⟶ S)
    (z : B ⟶ C) (i : D ⟶ B) (j : X ⟶ C) (v : V ⟶ C)
    (I T : LineBundle C) (φ : I.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (E : (Modules.pullback z).obj (dualLineBundle C I).val ≅
      SheafOfModules.unit B.ringCatSheaf) where
  numerator : SheafOfModules.unit C.ringCatSheaf ⟶
    (tensorLineBundle C T (dualLineBundle C I)).val
  denominator : SheafOfModules.unit C.ringCatSheaf ⟶ T.val
  boundary_value : pullbackSectionMap z numerator ≫
    pullbackTensorMap z T.val (dualLineBundle C I).val =
      tensorUnitSection (pullbackSectionMap z denominator) E.inv
  numerator_unit : IsIso (pullbackSectionMap z numerator)
  denominator_unit : IsIso (pullbackSectionMap z denominator)
  numerator_divisor : CoherentGraph.SectionDivisorFiniteFlat q v
    (tensorLineBundle C T (dualLineBundle C I)) numerator
  denominator_divisor : CoherentGraph.SectionDivisorFiniteFlat q v T denominator
  family_finite_flat :
    let L := dualLineBundle C (tensorLineBundle C T (dualLineBundle C I))
    let a0 := sectionDualFunctional C (tensorLineBundle C T (dualLineBundle C I))
      (twistedIdealSection C I T φ denominator)
    let a1 := sectionDualFunctional C (tensorLineBundle C T (dualLineBundle C I)) numerator
    let f := familyMap ((j ≫ q) ≫ bS) (pullbackLineBundle j L)
      (Hom.pullbackToUnit a0 j) (Hom.pullbackToUnit a1 j)
    IsFinite (Hom.zeroInclusion f ≫ parameterMap bS (j ≫ q)) ∧
      Flat (Hom.zeroInclusion f ≫ parameterMap bS (j ≫ q))

/-- One sufficiently positive twist gives both moving divisors and the actual
one-sided polynomial homotopy. No finiteness of its zeros is an input. -/
theorem exists_oneSidedSerreSections
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (K : Type u) [CommRing K] (bS : Spec (.of R) ⟶ Spec (.of K))
    (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C B D X V : Scheme.{u}} [IsLocallyNoetherian C]
    (a : C ⟶ ProjectiveSpace R ι) [IsFinite a]
    (z : B ⟶ C) [IsClosedImmersion z] (i : D ⟶ B)
    (eQ : ∀ d : ℕ, (moduleTensorLeftFunctor B
      ((Modules.pullback z).obj ((Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))))).obj
        ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf)) ≅
          SheafOfModules.unit B.ringCatSheaf)
    (j : X ⟶ C) [IsOpenImmersion j] [X.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ a ≫ toSpec R ι)]
    (v : V ⟶ C) [IsOpenImmersion v] [V.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (v ≫ a ≫ toSpec R ι)]
    (hX : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range (i ≫ z))
    (hV : ∀ x : C, x ∈ Set.range v ∨ x ∈ Set.range z)
    (I : LineBundle C) (φ : I.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    (E : (Modules.pullback z).obj (dualLineBundle C I).val ≅
      SheafOfModules.unit B.ringCatSheaf)
    (hδ : pullbackSectionMap (i ≫ z) (canonicalDualHom C I.val φ) ≫
      (compositeBoundaryFrame i z (dualLineBundle C I).val E).hom = 𝟙 _) :
    ∃ N : ℕ, ∀ d : ℕ, N ≤ d → Nonempty (OneSidedSections bS
      (a ≫ toSpec R ι) z i j v I
      (pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))) φ E) := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) e.symm
  have : IsProper (a ≫ toSpec R ι) := inferInstance
  obtain ⟨N, hN⟩ := CoherentGraph.exists_normalized_boundary_divisor_pair
    R ι n e a z eQ v hV (dualLineBundle C I) E
  refine ⟨N, fun d hd => ?_⟩
  obtain ⟨s, t, hs, hsi, hti, hsf, htf⟩ := hN d hd
  let T := pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))
  let := hsi
  exact ⟨⟨s, t, hs, hsi, hti, hsf, htf,
    oneSided_pencil_finite_flat bS (a ≫ toSpec R ι) j z i hX I T φ E s t hs hδ⟩⟩

end AlgebraicGeometry.Scheme.Moving
