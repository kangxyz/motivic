/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SuslinVoevodsky.Complex
public import Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.Evaluation
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Evaluation

/-!
# Motivic cohomology as actual Nisnevich hypercohomology

For every field `k`, integer degree `p`, nonnegative weight `q`, and smooth
separated finite-type `k`-scheme `X`, `motivicCohomology k p q X` is the
unbounded derived-Hom hypercohomology of the actual canonical motivic complex,
after forgetting transfers to ordinary Nisnevich sheaves.

The derived-localization universe is explicit. The construction does not use
bounded-below derived functors for the bounded-above motivic complex. At the
base object `Spec k`, the proved split-cover theorem makes its section
representative projective, giving a canonical additive equivalence with
cohomology of the literal evaluated complex. This comparison is a theorem
about the derived definition, rather than the definition of a substitute group.

No weight computation or arbitrary change-of-ground-field claim is made.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic
open _root_.AlgebraicGeometry.Scheme
open _root_.CategoryTheory.Sheaf
open _root_.CategoryTheory.SingularComplex

variable (k : Type u) [Field k]

/-- The canonical motivic complex as an actual complex of ordinary Nisnevich sheaves. -/
def motivicSheafComplex (q : ℕ) :
    CochainComplex (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      AddCommGrpCat.{u + 1}) ℤ :=
  ((SheafWithTransfers.toSheaf k).mapHomologicalComplex (.up ℤ)).obj
    (motivicComplex k q)

/-- Each ordinary term is exactly the transfer-sheaf term with transfers forgotten. -/
@[simp]
theorem motivicSheafComplex_X (q : ℕ) (i : ℤ) :
    (motivicSheafComplex k q).X i =
      (SheafWithTransfers.toSheaf k).obj ((motivicComplex k q).X i) := rfl

/-- The differential is the actual signed motivic differential with transfers forgotten. -/
@[simp]
theorem motivicSheafComplex_d (q : ℕ) (i j : ℤ) :
    (motivicSheafComplex k q).d i j =
      (SheafWithTransfers.toSheaf k).map ((motivicComplex k q).d i j) := rfl

/-- The full underlying complex retains the proved ordinary sheafification term dictionary. -/
def motivicSheafComplexXIso (q r : ℕ) :
    (motivicSheafComplex k q).X (Indexing.singularDegree q r) ≅
      (presheafToSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        AddCommGrpCat.{u + 1}).obj (motivicSingularPresheaf k q r) :=
  motivicComplexUnderlyingXIso k q r

/-- The actual cochain complex of base-field sections of the canonical sheaf complex. -/
def motivicBaseComplex (q : ℕ) : CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  ((SmoothSite.nisnevichBaseEvaluation k).mapHomologicalComplex (.up ℤ)).obj
    (motivicSheafComplex k q)

/-- Base evaluation uses the literal term at the actual base object. -/
@[simp]
theorem motivicBaseComplex_X (q : ℕ) (i : ℤ) :
    (motivicBaseComplex k q).X i =
      ((motivicSheafComplex k q).X i).obj.obj (op (SmoothSite.base (Spec (.of k)))) := rfl

/-- Base evaluation uses the literal component of the actual sheaf differential. -/
@[simp]
theorem motivicBaseComplex_d (q : ℕ) (i j : ℤ) :
    (motivicBaseComplex k q).d i j =
      ((motivicSheafComplex k q).d i j).hom.app
        (op (SmoothSite.base (Spec (.of k)))) := rfl

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Integral motivic cohomology is genuine unbounded Nisnevich hypercohomology. -/
abbrev motivicCohomology (p : ℤ) (q : ℕ) (X : SmoothSite (Spec (.of k))) : Type w :=
  Hypercohomology.H.{w, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) (motivicSheafComplex k q) p X

/-- Motivic cohomology is an additive presheaf in the actual smooth scheme. -/
def motivicCohomologyPresheaf (p : ℤ) (q : ℕ) :
    (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  Hypercohomology.presheaf.{w, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k)))
    (motivicSheafComplex k q) p

/-- The presheaf has the stated actual derived-Hom groups as its values. -/
@[simp]
theorem motivicCohomologyPresheaf_obj (p : ℤ) (q : ℕ) (X : SmoothSite (Spec (.of k))) :
    (motivicCohomologyPresheaf k p q).obj (op X) =
      AddCommGrpCat.of (motivicCohomology k p q X) := rfl

/-- Pullback in motivic cohomology along an actual morphism of smooth schemes over `k`. -/
abbrev motivicCohomologyRestriction (p : ℤ) (q : ℕ)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    AddCommGrpCat.of (motivicCohomology k p q Y) ⟶
      AddCommGrpCat.of (motivicCohomology k p q X) :=
  (motivicCohomologyPresheaf k p q).map f.op

/-- Every integer-degree motivic group at the base field is canonically the
cohomology of its actual evaluated sheaf complex. The proof uses split smooth
Nisnevich covers and the K-projective section-representing complex. -/
def motivicBaseEvaluationComparison (p : ℤ) (q : ℕ) :
    motivicCohomology k p q (SmoothSite.base (Spec (.of k))) ≃+
      (motivicBaseComplex k q).homology p := by
  letI := Hypercohomology.projective_freeAbelianSheaf.{u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) (SmoothSite.base (Spec (.of k)))
    (fun φ ↦ SmoothSite.surjective_app_base_of_epi k φ)
  exact Hypercohomology.evaluationComparison
    (SmoothSite.nisnevichTopology (Spec (.of k))) (SmoothSite.base (Spec (.of k)))
    (motivicSheafComplex k q) p

end Motivic
