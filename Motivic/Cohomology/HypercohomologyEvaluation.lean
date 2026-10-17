/-
Copyright (c) 2026 Motivic cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Hypercohomology
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Computing unbounded hypercohomology at exact evaluation objects

The free abelian representable sheaf is projective whenever evaluation sends
epimorphisms to surjections. Its degree-zero complex is K-projective. This
computes the derived-Hom definition of hypercohomology against arbitrary
integer-indexed complexes, with no bounded-below hypothesis on the target.

The evaluation-complex comparison uses the actual Hom complex, the additive
section-representing equivalence and its differential compatibility. A
geometric site must supply its own exact-evaluation proof before applying it.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite
open CochainComplex CochainComplex.HomComplex

namespace Motivic.Hypercohomology

section HomComplex

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Transport of derived morphisms along specified isomorphisms is additive. -/
def homCongrAddEquiv {P P' Q Q' : DerivedCategory A} (eP : P ≅ P') (eQ : Q ≅ Q') :
    (P ⟶ Q) ≃+ (P' ⟶ Q') where
  toEquiv := Iso.homCongr eP eQ
  map_add' f g := by simp [Iso.homCongr]

/-- For a K-projective source, the actual Hom-complex cohomology computes unbounded derived Hom. -/
def homComplexDerivedEquiv (P K : CochainComplex A ℤ) [P.IsKProjective] (p : ℤ) :
    (CochainComplex.HomComplex P K).homology p ≃+
      (DerivedCategory.Q.obj P ⟶ (DerivedCategory.Q.obj K)⟦p⟧) :=
  (HomComplex.homologyAddEquiv P K p).trans <|
    (CohomologyClass.homAddEquiv).trans <|
      (AddEquiv.ofBijective DerivedCategory.Qh.mapAddHom
        (IsKProjective.Qh_map_bijective P
          ((HomotopyCategory.quotient _ _).obj (K⟦p⟧)))).trans <|
        homCongrAddEquiv ((DerivedCategory.quotientCompQhIso A).app P)
          (((DerivedCategory.quotientCompQhIso A).app (K⟦p⟧)) ≪≫
            (DerivedCategory.Q.commShiftIso p).app K)

end HomComplex

section Evaluation

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max u v}]

/-- The ordinary section functor at an object of the site, in a universe containing the site. -/
def evaluation (X : C) : Sheaf J AddCommGrpCat.{max u v} ⥤ AddCommGrpCat.{max u v} :=
  sheafToPresheaf J _ ⋙ (CategoryTheory.evaluation _ _).obj (op X)

instance (X : C) : (evaluation J X).Additive := by
  dsimp [evaluation]
  infer_instance

/-- The actual cochain complex obtained by evaluating every sheaf and every differential at X. -/
abbrev evaluationComplex (X : C) (K : CochainComplex (Sheaf J AddCommGrpCat.{max u v}) ℤ) :
    CochainComplex AddCommGrpCat.{max u v} ℤ :=
  ((evaluation J X).mapHomologicalComplex (.up ℤ)).obj K

/-- The complex representing sections is the single complex of the free abelian representable. -/
abbrev sectionsSourceComplex (X : C) : CochainComplex (Sheaf J AddCommGrpCat.{max u v}) ℤ :=
  (CochainComplex.singleFunctor _ 0).obj (freeAbelianSheaf J X)

/-- Projectivity of the representing sheaf implies K-projectivity of its single complex. -/
instance sourceComplex_isKProjective (X : C) [Projective (freeAbelianSheaf J X)] :
    (sectionsSourceComplex J X).IsKProjective :=
  CochainComplex.isKProjective_of_projective _ 0

/-- The actual Hom complex from the source sheaf in degree zero is the evaluated complex. -/
def homComplexEvaluationIso (X : C) (K : CochainComplex (Sheaf J AddCommGrpCat.{max u v}) ℤ) :
    CochainComplex.HomComplex (sectionsSourceComplex J X) K ≅ evaluationComplex J X K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p ↦ ((Cochain.fromSingleEquiv (zero_add p)).trans
      (sectionsAddEquiv J X (K.X p))).toAddCommGrpIso) (by
        intro i j _
        apply AddCommGrpCat.ext
        intro x
        obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective x i (zero_add i)
        change (K.d i j).hom.app (op X)
            (sectionsAddEquiv J X (K.X i) (Cochain.fromSingleEquiv (zero_add i)
              (Cochain.fromSingleMk f (zero_add i)))) =
          sectionsAddEquiv J X (K.X j) (Cochain.fromSingleEquiv (zero_add j)
            (δ i j (Cochain.fromSingleMk f (zero_add i))))
        rw [Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j)]
        simp only [Cochain.fromSingleEquiv_fromSingleMk]
        exact (sectionsEquiv_naturality J X f (K.d i j)).symm)

variable [HasDerivedCategory.{w} (Sheaf J AddCommGrpCat.{max u v})]

/-- At a projective section-representing object, unbounded hypercohomology equals the cohomology
of the actual evaluated complex. The identification is induced by the Hom-complex comparison. -/
def evaluationComparison (X : C) [Projective (freeAbelianSheaf J X)]
    (K : CochainComplex (Sheaf J AddCommGrpCat.{max u v}) ℤ) (p : ℤ) :
    H J K p X ≃+ (evaluationComplex J X K).homology p :=
  (homComplexDerivedEquiv (sectionsSourceComplex J X) K p).symm.trans
    (HomologicalComplex.homologyMapIso (homComplexEvaluationIso J X K) p).addCommGroupIsoToAddEquiv

end Evaluation

end Motivic.Hypercohomology
