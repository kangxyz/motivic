/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedSerreSections
public import Motivic.Aglib.AlgebraicGeometry.Moving.OpenGraphLine
public import Motivic.Aglib.AlgebraicGeometry.Moving.ZeroSupportOpen
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Pencils.Polynomial.PrecompIso
/-! # The actual Serre family in the retained graph domain -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
open Scheme.Modules.Invertible.PolynomialBoundaryPencil
universe u
namespace AlgebraicGeometry.Scheme.Moving

/-- Transport the whole finite-flat family by the original graph-ideal comparison.
The zero endpoint is literally graph inclusion times denominator. -/
theorem OneSidedSections.graph_family_finite_flat
    {R : Type u} [CommRing R] {S C B D X V : Scheme.{u}}
    (bS : S ⟶ Spec (.of R)) (q : C ⟶ S)
    (z : B ⟶ C) (i : D ⟶ B) (j : X ⟶ C) [IsOpenImmersion j] (v : V ⟶ C)
    (δ : S ⟶ C) [IsClosedImmersion δ] (γ : S ⟶ X) (hγ : γ ≫ j = δ)
    (hI : IsLocallyRankOne C (Scheme.Hom.idealModule δ)) (T : LineBundle C)
    (E : (Modules.pullback z).obj
      (dualLineBundle C ⟨Scheme.Hom.idealModule δ, hI⟩).val ≅
        SheafOfModules.unit B.ringCatSheaf)
    (s : OneSidedSections bS q z i j v ⟨Scheme.Hom.idealModule δ, hI⟩ T
      (Scheme.Hom.idealInclusion δ) E) :
    let J : LineBundle X := ⟨Scheme.Hom.idealModule γ, openGraph_locallyRankOne j δ γ hγ hI⟩
    let M := pullbackLineBundle j (dualLineBundle C T)
    let L := tensorLineBundle X J M
    let b := Hom.pullbackToUnit (sectionDualFunctional C T s.denominator) j
    let a := (openGraphPencilLineIso j δ γ hγ hI T).hom ≫
      Hom.pullbackToUnit (sectionDualFunctional C
        (tensorLineBundle C T (dualLineBundle C ⟨Scheme.Hom.idealModule δ, hI⟩)) s.numerator) j
    let f := familyMap ((j ≫ q) ≫ bS) L
      (Hom.productSection (Scheme.Hom.idealInclusion γ) b) a
    IsFinite (Hom.zeroInclusion f ≫ parameterMap bS (j ≫ q)) ∧
      Flat (Hom.zeroInclusion f ≫ parameterMap bS (j ≫ q)) := by
  let I : LineBundle C := ⟨Scheme.Hom.idealModule δ, hI⟩
  let J : LineBundle X := ⟨Scheme.Hom.idealModule γ, openGraph_locallyRankOne j δ γ hγ hI⟩
  let M := pullbackLineBundle j (dualLineBundle C T)
  let L := tensorLineBundle X J M
  let L0 := pullbackLineBundle j (dualLineBundle C (tensorLineBundle C T (dualLineBundle C I)))
  let a0 := Hom.pullbackToUnit (sectionDualFunctional C (tensorLineBundle C T (dualLineBundle C I))
    (twistedIdealSection C I T (Scheme.Hom.idealInclusion δ) s.denominator)) j
  let a1 := Hom.pullbackToUnit (sectionDualFunctional C (tensorLineBundle C T (dualLineBundle C I))
    s.numerator) j
  let e := openGraphPencilLineIso j δ γ hγ hI T
  have hf := s.family_finite_flat
  let := hf.1
  let := hf.2
  have hfin := familyZeroPrecomp_isFinite ((j ≫ q) ≫ bS) L L0 e a0 a1
    (parameterMap bS (j ≫ q))
  have hflat := familyZeroPrecomp_flat ((j ≫ q) ≫ bS) L L0 e a0 a1
    (parameterMap bS (j ≫ q))
  have he : e.hom ≫ a0 = Hom.productSection (Scheme.Hom.idealInclusion γ)
      (Hom.pullbackToUnit (sectionDualFunctional C T s.denominator) j) :=
    openGraphPencilLineIso_start j δ γ hγ hI T s.denominator
  change IsFinite (Hom.zeroInclusion (familyMap ((j ≫ q) ≫ bS) L
      (Hom.productSection (Scheme.Hom.idealInclusion γ)
        (Hom.pullbackToUnit (sectionDualFunctional C T s.denominator) j)) (e.hom ≫ a1)) ≫
      parameterMap bS (j ≫ q)) ∧ Flat (Hom.zeroInclusion (familyMap ((j ≫ q) ≫ bS) L
      (Hom.productSection (Scheme.Hom.idealInclusion γ)
        (Hom.pullbackToUnit (sectionDualFunctional C T s.denominator) j)) (e.hom ≫ a1)) ≫
      parameterMap bS (j ≫ q))
  rw [← he]
  exact ⟨hfin, hflat⟩

end AlgebraicGeometry.Scheme.Moving
