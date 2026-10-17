/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.HypercohomologyNaturality

/-!
# Naturality of the unbounded evaluation theorem

The evaluation comparison intertwines the hypercohomology map induced by an
actual coefficient cochain map with the ordinary cohomology map of its
evaluated complex. The proof follows actual cocycles through the Hom complex,
homotopy classes, localization and the standard shift isomorphisms.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex

namespace Motivic.Hypercohomology

section General

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The cohomology-class map is conjugate to actual postcomposition in the homotopy category. -/
theorem cohomologyClassPostcomp_apply (P : CochainComplex A ℤ) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (p : ℤ) (x : CohomologyClass P K p) :
    cohomologyClassPostcomp P f p x = CohomologyClass.homAddEquiv.symm
      (CohomologyClass.homAddEquiv x ≫ (HomotopyCategory.quotient _ _).map (f⟦p⟧')) := rfl

/-- The actual additive postcomposition map on Hom-complex cocycles. -/
def cocyclePostcomp (P : CochainComplex A ℤ) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (p : ℤ) : Cocycle P K p →+ Cocycle P L p where
  toFun x := x.postcomp f
  map_zero' := by ext; simp [Cocycle.postcomp]
  map_add' x y := by ext; simp [Cocycle.postcomp]

/-- The concrete cycles and cohomology-class maps compute the map on Hom-complex cohomology. -/
def homComplexPostcompHomologyData (P : CochainComplex A ℤ) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (p : ℤ) :
    ShortComplex.LeftHomologyMapData
      ((HomologicalComplex.shortComplexFunctor _ _ p).map (homComplexPostcomp P f))
      (HomComplex.leftHomologyData P K p) (HomComplex.leftHomologyData P L p) where
  φK := AddCommGrpCat.ofHom (cocyclePostcomp P f p)
  φH := AddCommGrpCat.ofHom (cohomologyClassPostcomp P f p)
  commi := rfl
  commf' := by
    apply (cancel_mono (HomComplex.leftHomologyData P L p).i).mp
    simp only [Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    change (HomComplex.leftHomologyData P K p).f' ≫
      ((HomComplex.leftHomologyData P K p).i ≫ (homComplexPostcomp P f).f p) = _
    erw [← Category.assoc, ShortComplex.LeftHomologyData.f'_i]
    exact ((homComplexPostcomp P f).comm _ _).symm
  commπ := by
    ext x
    exact cohomologyClassPostcomp_mk P f p x

/-- The Hom-complex cohomology/class equivalence respects actual coefficient maps. -/
theorem homologyAddEquiv_postcomp (P : CochainComplex A ℤ) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (p : ℤ) (x : (CochainComplex.HomComplex P K).homology p) :
    HomComplex.homologyAddEquiv P L p (HomologicalComplex.homologyMap
      (homComplexPostcomp P f) p x) =
      cohomologyClassPostcomp P f p (HomComplex.homologyAddEquiv P K p x) :=
  ConcreteCategory.congr_hom (homComplexPostcompHomologyData P f p).homologyMap_comm x

variable [HasDerivedCategory.{w} A]

/-- The underlying morphism of the K-projective derived-Hom comparison. -/
theorem homComplexDerivedEquiv_apply (P K : CochainComplex A ℤ) [P.IsKProjective]
    (p : ℤ) (x : (CochainComplex.HomComplex P K).homology p) :
    homComplexDerivedEquiv P K p x =
      ((DerivedCategory.quotientCompQhIso A).app P).inv ≫
        DerivedCategory.Qh.map
          (CohomologyClass.homAddEquiv (HomComplex.homologyAddEquiv P K p x)) ≫
        ((DerivedCategory.quotientCompQhIso A).app (K⟦p⟧)).hom ≫
        (DerivedCategory.Q.commShiftIso p).hom.app K := rfl

/-- The K-projective Hom-complex/derived-Hom equivalence is natural in coefficient cochain maps. -/
theorem homComplexDerivedEquiv_naturality (P : CochainComplex A ℤ) [P.IsKProjective]
    {K L : CochainComplex A ℤ} (f : K ⟶ L) (p : ℤ)
    (x : (CochainComplex.HomComplex P K).homology p) :
    homComplexDerivedEquiv P L p (HomologicalComplex.homologyMap
      (homComplexPostcomp P f) p x) =
      homComplexDerivedEquiv P K p x ≫ (DerivedCategory.Q.map f)⟦p⟧' := by
  rw [homComplexDerivedEquiv_apply, homologyAddEquiv_postcomp,
    homComplexDerivedEquiv_apply]
  simp only [cohomologyClassPostcomp_apply,
    AddEquiv.apply_symm_apply, Functor.map_comp, Category.assoc, Iso.app_hom,
    DerivedCategory.quotientCompQhIso_hom_naturality_assoc,
    Functor.commShiftIso_hom_naturality]

end General

section Evaluation

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max u v})]

/-- The unbounded evaluation theorem preserves the exact map induced by every coefficient map. -/
theorem evaluationComparison_naturality (X : C) [Projective (freeAbelianSheaf J X)]
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{max u v}) ℤ} (f : K ⟶ L)
    (p : ℤ) (x : H J K p X) :
    evaluationComparison J X L p (map J f p X x) =
      HomologicalComplex.homologyMap
        (((evaluation J X).mapHomologicalComplex (.up ℤ)).map f) p
        (evaluationComparison J X K p x) := by
  obtain ⟨y, rfl⟩ := (homComplexDerivedEquiv (sectionsSourceComplex J X) K p).surjective x
  rw [map_apply, ← homComplexDerivedEquiv_naturality]
  simp only [evaluationComparison, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
  have h := congrArg (fun φ ↦ HomologicalComplex.homologyMap φ p)
    (homComplexEvaluationIso_naturality J X f)
  simp only [HomologicalComplex.homologyMap_comp] at h
  exact ConcreteCategory.congr_hom h y

end Evaluation

end Motivic.Hypercohomology
