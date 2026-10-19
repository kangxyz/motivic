/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.Evaluation

/-!
# Coefficient maps in the hypercohomology evaluation comparison

The Hom-complex map is actual postcomposition with a cochain map. Its
identification with the evaluated complex commutes with coefficient maps.
The cohomology-class description below tracks these maps through homotopy
classes, so the resulting statements retain the canonical maps.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex

namespace CategoryTheory.Sheaf.Hypercohomology

section General

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- Postcomposition by an actual cochain map defines a map of actual Hom complexes. -/
def homComplexPostcomp (P : CochainComplex A ℤ) {K L : CochainComplex A ℤ} (f : K ⟶ L) :
    CochainComplex.HomComplex P K ⟶ CochainComplex.HomComplex P L where
  f p := AddCommGrpCat.ofHom
    { toFun x := x.comp (Cochain.ofHom f) (add_zero p)
      map_zero' := by simp
      map_add' x y := by simp }
  comm' p q _ := by
    ext x
    exact δ_comp_ofHom x f q

/-- Postcomposition on cohomology classes, via the actual homotopy-category morphisms. -/
def cohomologyClassPostcomp (P : CochainComplex A ℤ) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (p : ℤ) : CohomologyClass P K p →+ CohomologyClass P L p where
  toFun x := CohomologyClass.homAddEquiv.symm
    (CohomologyClass.homAddEquiv x ≫ (HomotopyCategory.quotient _ _).map (f⟦p⟧'))
  map_zero' := by simp
  map_add' x y := by simp [Preadditive.add_comp]

/-- The induced cohomology-class map sends an actual cocycle to its postcomposition. -/
theorem cohomologyClassPostcomp_mk (P : CochainComplex A ℤ) {K L : CochainComplex A ℤ}
    (f : K ⟶ L) (p : ℤ) (x : Cocycle P K p) :
    cohomologyClassPostcomp P f p (CohomologyClass.mk x) =
      CohomologyClass.mk (x.postcomp f) := by
  apply CohomologyClass.homAddEquiv.injective
  simp [cohomologyClassPostcomp, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_postcomp]

end General

section Evaluation

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]

/-- The actual Hom-complex/evaluation identification respects every coefficient cochain map. -/
theorem homComplexEvaluationIso_naturality (X : C)
    {K L : CochainComplex (Sheaf J AddCommGrpCat.{max u v}) ℤ} (f : K ⟶ L) :
    homComplexPostcomp (sectionsSourceComplex J X) f ≫ (homComplexEvaluationIso J X L).hom =
      (homComplexEvaluationIso J X K).hom ≫
        ((evaluation J X).mapHomologicalComplex (.up ℤ)).map f := by
  ext p x
  obtain ⟨g, rfl⟩ := Cochain.fromSingleMk_surjective x p (zero_add p)
  change sectionsAddEquiv J X (L.X p) (Cochain.fromSingleEquiv (zero_add p)
      ((Cochain.fromSingleMk g (zero_add p)).comp (Cochain.ofHom f) (add_zero p))) =
    (f.f p).hom.app (op X) (sectionsAddEquiv J X (K.X p)
      (Cochain.fromSingleEquiv (zero_add p) (Cochain.fromSingleMk g (zero_add p))))
  rw [← Cochain.fromSingleMk_postcomp g (zero_add p) f]
  simp only [Cochain.fromSingleEquiv_fromSingleMk]
  exact sectionsEquiv_naturality J X g (f.f p)

end Evaluation

end CategoryTheory.Sheaf.Hypercohomology
