/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Coefficients.Finite.Complex
public import Motivic.Aglib.Algebra.Homology.CochainComplex.FiniteCoefficients.Exact
public import Mathlib.Algebra.Homology.ShortComplex.Ab

/-!
# Actual finite motivic hypercohomology and the base-field coefficient sequence

Finite motivic cohomology is the unbounded derived-Hom hypercohomology of the
actual finite motivic sheaf complex. It is a presheaf on the smooth Nisnevich
site. At the base field its canonical evaluation comparison identifies it
with the cohomology of the finite-coefficient cone on `motivicBaseComplex`.

The field reduction and positive Bockstein below are transported through these
proved comparisons. Their comparison formulas specify their canonical maps,
and exactness reuses the existing coefficient-cone exactness theorem. This
proves the field coefficient sequence for every natural level, including one
and composite levels, without an invertibility assumption. It asserts neither
an arbitrary-scheme long exact sequence nor a derived tensor identification.
These are structural theorems, not low-weight computations.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe w u

namespace Motivic
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.Sheaf

variable (k : Type u) [Field k]

/-- The literal complex of base-field sections of the finite motivic sheaf complex. -/
def motivicFiniteBaseComplex (q n : ℕ) : CochainComplex AddCommGrpCat.{u + 1} ℤ :=
  ((SmoothSite.nisnevichBaseEvaluation k).mapHomologicalComplex (.up ℤ)).obj
    (motivicFiniteSheafComplex k q n)

/-- Additive base evaluation commutes with the actual finite-coefficient mapping cone. -/
def motivicFiniteBaseComplexIso (q n : ℕ) :
    motivicFiniteBaseComplex k q n ≅ _root_.CochainComplex.finiteCoefficients (motivicBaseComplex k
        q) n := by
  let F := (SmoothSite.nisnevichBaseEvaluation k).mapHomologicalComplex (.up ℤ)
  have hmap : F.map (n • 𝟙 (motivicSheafComplex k q)) =
      n • 𝟙 (F.obj (motivicSheafComplex k q)) := by
    rw [Functor.map_nsmul]
    exact congrArg (fun f => n • f) (F.map_id (motivicSheafComplex k q))
  exact CochainComplex.mappingCone.mapHomologicalComplexIso
      (n • 𝟙 (motivicSheafComplex k q)) (SmoothSite.nisnevichBaseEvaluation k) ≪≫
    eqToIso (by change CochainComplex.mappingCone (F.map _) = _; rw [hmap]; rfl)

/-- The evaluated coefficient sequence with integral quotient and positive torsion map. -/
abbrev motivicBaseCoefficientShortComplex (p : ℤ) (q n : ℕ) :
    ShortComplex AddCommGrpCat.{u + 1} :=
  _root_.CochainComplex.finiteCoefficients.cohomologyShortComplex (motivicBaseComplex k q) n p

/-- The evaluated coefficient short complex is short exact, with no restriction on the level. -/
theorem motivicBaseCoefficientShortComplex_shortExact (p : ℤ) (q n : ℕ) :
    (motivicBaseCoefficientShortComplex k p q n).ShortExact :=
  _root_.CochainComplex.finiteCoefficients.cohomologyShortComplex_shortExact (motivicBaseComplex
      k q) n p

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Finite motivic cohomology is genuine unbounded derived-Hom hypercohomology. -/
abbrev motivicFiniteCohomology (p : ℤ) (q n : ℕ)
    (X : SmoothSite (Spec (.of k))) : Type w :=
  Hypercohomology.H.{w, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) (motivicFiniteSheafComplex k q n) p X

/-- Actual finite motivic groups form an additive presheaf in the smooth scheme. -/
def motivicFiniteCohomologyPresheaf (p : ℤ) (q n : ℕ) :
    (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  Hypercohomology.presheaf.{w, u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) (motivicFiniteSheafComplex k q n) p

@[simp]
theorem motivicFiniteCohomologyPresheaf_obj (p : ℤ) (q n : ℕ)
    (X : SmoothSite (Spec (.of k))) :
    (motivicFiniteCohomologyPresheaf k p q n).obj (op X) =
      AddCommGrpCat.of (motivicFiniteCohomology k p q n X) := rfl

/-- Restriction along an actual morphism of smooth schemes. -/
abbrev motivicFiniteCohomologyRestriction (p : ℤ) (q n : ℕ)
    {X Y : SmoothSite (Spec (.of k))} (f : X ⟶ Y) :
    AddCommGrpCat.of (motivicFiniteCohomology k p q n Y) ⟶
      AddCommGrpCat.of (motivicFiniteCohomology k p q n X) :=
  (motivicFiniteCohomologyPresheaf k p q n).map f.op

/-- Genuine derived finite motivic cohomology equals cohomology of its literal field sections. -/
def motivicFiniteBaseEvaluationComparison (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k))) ≃+
      (motivicFiniteBaseComplex k q n).homology p := by
  letI := Hypercohomology.projective_freeAbelianSheaf.{u + 1, u, u + 1}
    (SmoothSite.nisnevichTopology (Spec (.of k))) (SmoothSite.base (Spec (.of k)))
    (fun φ ↦ SmoothSite.surjective_app_base_of_epi k φ)
  exact Hypercohomology.evaluationComparison
    (SmoothSite.nisnevichTopology (Spec (.of k))) (SmoothSite.base (Spec (.of k)))
    (motivicFiniteSheafComplex k q n) p

/-- The actual derived finite group is identified with the coefficient cone of the integral
field complex. The second step is induced by the additive evaluation/cone isomorphism. -/
def motivicFiniteBaseConeComparison (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k))) ≃+
      (_root_.CochainComplex.finiteCoefficients (motivicBaseComplex k q) n).homology p :=
  (motivicFiniteBaseEvaluationComparison k p q n).trans <|
    (HomologicalComplex.homologyMapIso
      (motivicFiniteBaseComplexIso k q n) p).addCommGroupIsoToAddEquiv

/-- Field reduction defined using the proved comparison with the canonical integral cone map. -/
def motivicBaseIntegralReduction (p : ℤ) (q n : ℕ) :
    motivicCohomology k p q (SmoothSite.base (Spec (.of k))) →+
      motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k))) :=
  (motivicFiniteBaseConeComparison k p q n).symm.toAddMonoidHom.comp
    ((_root_.CochainComplex.finiteCoefficients.integralHomology (motivicBaseComplex k q) n
        p).hom.comp
      (motivicBaseEvaluationComparison k p q).toAddMonoidHom)

/-- The positive field Bockstein, transported from the canonical signed coefficient cone map. -/
def motivicBaseBockstein (p : ℤ) (q n : ℕ) :
    motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k))) →+
      motivicCohomology k (p + 1) q (SmoothSite.base (Spec (.of k))) :=
  (motivicBaseEvaluationComparison k (p + 1) q).symm.toAddMonoidHom.comp
    ((_root_.CochainComplex.finiteCoefficients.bocksteinHomology (motivicBaseComplex k q) n
        p).hom.comp
      (motivicFiniteBaseConeComparison k p q n).toAddMonoidHom)

/-- The reduction comparison fixes the exact integral-to-finite map. -/
@[simp]
theorem motivicBaseIntegralReduction_comparison (p : ℤ) (q n : ℕ)
    (x : motivicCohomology k p q (SmoothSite.base (Spec (.of k)))) :
    motivicFiniteBaseConeComparison k p q n (motivicBaseIntegralReduction k p q n x) =
      _root_.CochainComplex.finiteCoefficients.integralHomology (motivicBaseComplex k q) n p
        (motivicBaseEvaluationComparison k p q x) := by
  simp [motivicBaseIntegralReduction]

/-- The comparison fixes the sign: this is the existing positive cohomological Bockstein. -/
@[simp]
theorem motivicBaseBockstein_comparison (p : ℤ) (q n : ℕ)
    (x : motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k)))) :
    motivicBaseEvaluationComparison k (p + 1) q (motivicBaseBockstein k p q n x) =
      _root_.CochainComplex.finiteCoefficients.bocksteinHomology (motivicBaseComplex k q) n p
        (motivicFiniteBaseConeComparison k p q n x) := by
  simp [motivicBaseBockstein]

/-- Integral classes reduce to zero exactly when they are multiples of the level. -/
theorem motivicBase_exact_mul_reduction (p : ℤ) (q n : ℕ) :
    Function.Exact (fun x : motivicCohomology k p q (SmoothSite.base (Spec (.of k))) =>
      n • x) (motivicBaseIntegralReduction k p q n) := by
  have h := (ShortComplex.ab_exact_iff_function_exact _).1
    (_root_.CochainComplex.finiteCoefficients.exact_mul_integralHomology (motivicBaseComplex k
        q) n p)
  intro x
  constructor
  · intro hx
    have hx' : _root_.CochainComplex.finiteCoefficients.integralHomology (motivicBaseComplex k
        q) n p
        (motivicBaseEvaluationComparison k p q x) = 0 := by
      rw [← motivicBaseIntegralReduction_comparison, hx, map_zero]
    obtain ⟨y, hy⟩ := (h (motivicBaseEvaluationComparison k p q x)).1 hx'
    refine ⟨(motivicBaseEvaluationComparison k p q).symm y,
      (motivicBaseEvaluationComparison k p q).injective ?_⟩
    simpa using hy
  · rintro ⟨y, rfl⟩
    apply (motivicFiniteBaseConeComparison k p q n).injective
    rw [map_zero, motivicBaseIntegralReduction_comparison, map_nsmul]
    exact (h _).2 ⟨motivicBaseEvaluationComparison k p q y, rfl⟩

/-- A finite field class has zero positive Bockstein exactly when it lifts integrally. -/
theorem motivicBase_exact_reduction_bockstein (p : ℤ) (q n : ℕ) :
    Function.Exact (motivicBaseIntegralReduction k p q n) (motivicBaseBockstein k p q n) := by
  have h := (ShortComplex.ab_exact_iff_function_exact _).1
    (_root_.CochainComplex.finiteCoefficients.exact_integralHomology_bocksteinHomology
        (motivicBaseComplex k q) n p)
  intro x
  constructor
  · intro hx
    have hx' : _root_.CochainComplex.finiteCoefficients.bocksteinHomology (motivicBaseComplex k
        q) n p
        (motivicFiniteBaseConeComparison k p q n x) = 0 := by
      rw [← motivicBaseBockstein_comparison, hx, map_zero]
    obtain ⟨y, hy⟩ := (h (motivicFiniteBaseConeComparison k p q n x)).1 hx'
    refine ⟨(motivicBaseEvaluationComparison k p q).symm y,
      (motivicFiniteBaseConeComparison k p q n).injective ?_⟩
    simpa only [motivicBaseIntegralReduction_comparison, AddEquiv.apply_symm_apply] using hy
  · rintro ⟨y, rfl⟩
    apply (motivicBaseEvaluationComparison k (p + 1) q).injective
    rw [map_zero, motivicBaseBockstein_comparison, motivicBaseIntegralReduction_comparison]
    exact (h _).2 ⟨motivicBaseEvaluationComparison k p q y, rfl⟩

/-- The image of the positive field Bockstein is exactly the level torsion. -/
theorem motivicBase_exact_bockstein_mul (p : ℤ) (q n : ℕ) :
    Function.Exact (motivicBaseBockstein k p q n)
      (fun x : motivicCohomology k (p + 1) q (SmoothSite.base (Spec (.of k))) => n • x) := by
  have h := (ShortComplex.ab_exact_iff_function_exact _).1
    (_root_.CochainComplex.finiteCoefficients.exact_bocksteinHomology_mul (motivicBaseComplex k
        q) n p)
  intro x
  constructor
  · intro hx
    have hx' : (n • 𝟙 ((motivicBaseComplex k q).homology (p + 1)))
        (motivicBaseEvaluationComparison k (p + 1) q x) = 0 := by
      simpa using congrArg (motivicBaseEvaluationComparison k (p + 1) q) hx
    obtain ⟨y, hy⟩ := (h (motivicBaseEvaluationComparison k (p + 1) q x)).1 hx'
    refine ⟨(motivicFiniteBaseConeComparison k p q n).symm y,
      (motivicBaseEvaluationComparison k (p + 1) q).injective ?_⟩
    simpa only [motivicBaseBockstein_comparison, AddEquiv.apply_symm_apply] using hy
  · rintro ⟨y, rfl⟩
    apply (motivicBaseEvaluationComparison k (p + 1) q).injective
    rw [map_zero, map_nsmul, motivicBaseBockstein_comparison]
    exact (h _).2 ⟨motivicFiniteBaseConeComparison k p q n y, rfl⟩

/-- Every positive Bockstein class is annihilated by the coefficient level. -/
@[simp]
theorem nsmul_motivicBaseBockstein (p : ℤ) (q n : ℕ)
    (x : motivicFiniteCohomology k p q n (SmoothSite.base (Spec (.of k)))) :
    n • motivicBaseBockstein k p q n x = 0 :=
  (motivicBase_exact_bockstein_mul k p q n).apply_apply_eq_zero x

/-- The actual derived finite motivic group at the field vanishes at level one. -/
theorem subsingleton_motivicFiniteCohomology_base_one (p : ℤ) (q : ℕ) :
    Subsingleton (motivicFiniteCohomology k p q 1 (SmoothSite.base (Spec (.of k)))) := by
  let := AddCommGrpCat.subsingleton_of_isZero
    (_root_.CochainComplex.finiteCoefficients.isZero_homology_one (motivicBaseComplex k q) p)
  exact (motivicFiniteBaseConeComparison k p q 1).injective.subsingleton

end Motivic
