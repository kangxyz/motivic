/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.FiniteHypercohomology
public import Lean.Util.CollectAxioms

/-! # Consumers of genuine finite motivic cohomology and field coefficient exactness -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Motivic

universe w u

namespace MotivicTest.MotivicFiniteHypercohomology

variable (k : Type u) [Field k]

example (q n : ℕ) :
    motivicFiniteBaseComplex k q n ≅ finiteCoefficients (motivicBaseComplex k q) n :=
  motivicFiniteBaseComplexIso k q n

example (p : ℤ) (q n : ℕ) :
    (motivicBaseCoefficientShortComplex k p q n).ShortExact :=
  motivicBaseCoefficientShortComplex_shortExact k p q n

section ChosenDerivedCategory

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The group is definitionally the actual unbounded derived-Hom group. -/
example (p : ℤ) (q n : ℕ) (X : SmoothSite (Spec (.of k))) :
    motivicFiniteCohomology k p q n X =
      Hypercohomology.H.{w, u + 1, u, u + 1}
        (SmoothSite.nisnevichTopology (Spec (.of k)))
        (motivicFiniteSheafComplex k q n) p X := rfl

example (p : ℤ) (q n : ℕ) (X : SmoothSite (Spec (.of k))) :
    AddCommGroup (motivicFiniteCohomology k p q n X) := inferInstance

example (p : ℤ) (q n : ℕ) (X : SmoothSite (Spec (.of k))) :
    motivicFiniteCohomologyRestriction k p q n (𝟙 X) = 𝟙 _ :=
  (motivicFiniteCohomologyPresheaf k p q n).map_id (op X)

example (p : ℤ) (q n : ℕ) {X Y Z : SmoothSite (Spec (.of k))}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    motivicFiniteCohomologyRestriction k p q n (f ≫ g) =
      motivicFiniteCohomologyRestriction k p q n g ≫
        motivicFiniteCohomologyRestriction k p q n f :=
  (motivicFiniteCohomologyPresheaf k p q n).map_comp g.op f.op

example (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k))) ≃+
      (motivicFiniteBaseComplex k q n).homology p :=
  motivicFiniteBaseEvaluationComparison k p q n

/-- The derived field group is compared to the integral complex's actual coefficient cone. -/
example (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k))) ≃+
      (finiteCoefficients (motivicBaseComplex k q) n).homology p :=
  motivicFiniteBaseConeComparison k p q n

/-- This is the canonical cone reduction, through the proved base comparisons. -/
example (p : ℤ) (q n : ℕ)
    (x : motivicCohomology k p q (SmoothSite.base (Spec (.of k)))) :
    motivicFiniteBaseConeComparison k p q n (motivicBaseIntegralReduction k p q n x) =
      finiteCoefficients.integralHomology (motivicBaseComplex k q) n p
        (motivicBaseEvaluationComparison k p q x) :=
  motivicBaseIntegralReduction_comparison k p q n x

/-- This is the positive Bockstein from the signed cone, including its shift identification. -/
example (p : ℤ) (q n : ℕ)
    (x : motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k)))) :
    motivicBaseEvaluationComparison k (p + 1) q (motivicBaseBockstein k p q n x) =
      finiteCoefficients.bocksteinHomology (motivicBaseComplex k q) n p
        (motivicFiniteBaseConeComparison k p q n x) :=
  motivicBaseBockstein_comparison k p q n x

example (p : ℤ) (q n : ℕ) :
    Function.Exact (fun x : motivicCohomology k p q (SmoothSite.base (Spec (.of k))) =>
      n • x) (motivicBaseIntegralReduction k p q n) :=
  motivicBase_exact_mul_reduction k p q n

/-- A concrete composite level works without an invertibility hypothesis. -/
theorem composite_six_lifting (p : ℤ) (q : ℕ)
    (x : motivicFiniteCohomology k p q 6 (SmoothSite.base (Spec (.of k)))) :
    motivicBaseBockstein k p q 6 x = 0 ↔
      ∃ y : motivicCohomology k p q (SmoothSite.base (Spec (.of k))),
        motivicBaseIntegralReduction k p q 6 y = x :=
  motivicBase_exact_reduction_bockstein k p q 6 x

/-- Every six-torsion integral class comes from the positive Bockstein. -/
theorem composite_six_torsion (p : ℤ) (q : ℕ)
    (y : motivicCohomology k (p + 1) q (SmoothSite.base (Spec (.of k))))
    (hy : 6 • y = 0) :
    ∃ x : motivicFiniteCohomology k p q 6 (SmoothSite.base (Spec (.of k))),
      motivicBaseBockstein k p q 6 x = y :=
  (motivicBase_exact_bockstein_mul k p q 6 y).1 hy

example (p : ℤ) (q n : ℕ)
    (x : motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k)))) :
    n • motivicBaseBockstein k p q n x = 0 :=
  nsmul_motivicBaseBockstein k p q n x

/-- This is actual derived-group vanishing at level one, not just a sheaf homology statement. -/
theorem level_one_zero (p : ℤ) (q : ℕ)
    (x : motivicFiniteCohomology k p q 1 (SmoothSite.base (Spec (.of k)))) : x = 0 := by
  let := subsingleton_motivicFiniteCohomology_base_one k p q
  exact Subsingleton.elim x 0

end ChosenDerivedCategory

/-- A real consumer chooses the standard large derived localization. -/
def standardLargeFiniteFieldComparison (p : ℤ) (q n : ℕ) :=
  letI := HasDerivedCategory.standard
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})
  motivicFiniteBaseConeComparison k p q n

/-- Negative degree, weight two and composite level are admitted by the unbounded definition. -/
def negativeDegreeCompositeComparison := standardLargeFiniteFieldComparison k (-4) 2 6

open Lean in
run_cmd do
  for name in #[``motivicFiniteBaseComplex, ``motivicFiniteBaseComplexIso,
      ``motivicBaseCoefficientShortComplex, ``motivicBaseCoefficientShortComplex_shortExact,
      ``motivicFiniteCohomology, ``motivicFiniteCohomologyPresheaf,
      ``motivicFiniteCohomologyPresheaf_obj, ``motivicFiniteCohomologyRestriction,
      ``motivicFiniteBaseEvaluationComparison, ``motivicFiniteBaseConeComparison,
      ``motivicBaseIntegralReduction, ``motivicBaseBockstein,
      ``motivicBaseIntegralReduction_comparison, ``motivicBaseBockstein_comparison,
      ``motivicBase_exact_mul_reduction, ``motivicBase_exact_reduction_bockstein,
      ``motivicBase_exact_bockstein_mul, ``nsmul_motivicBaseBockstein,
      ``subsingleton_motivicFiniteCohomology_base_one, ``composite_six_lifting,
      ``composite_six_torsion, ``level_one_zero, ``standardLargeFiniteFieldComparison,
      ``negativeDegreeCompositeComparison] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Finite motivic field cohomology and Bockstein exactness use only standard foundations."

end MotivicTest.MotivicFiniteHypercohomology
