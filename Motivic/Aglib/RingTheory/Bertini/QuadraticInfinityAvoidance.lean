/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticInfinityCommonRelation
public import Motivic.Aglib.RingTheory.Bertini.ProjectiveEvaluationAvoidance

/-! # One same-family principal open has no field-valued quadratic infinity basepoints -/
@[expose] public noncomputable section
open _root_.MvPolynomial
universe u
namespace ProjectiveEvaluationIncidence

/-- The unchanged homogeneous forms vanish at this actual field-valued point. -/
def Vanishes (k A K : Type u) [CommRing k] [CommRing A] [CommRing K]
    [Algebra k K] [Algebra A K] {N : Type u} [Fintype N]
    (a : N → A) (n : ℕ) (c : Fin n × N → k) : Prop :=
  ∀ i, ∑ e, algebraMap k K (c (i, e)) * algebraMap A K (a e) = 0

end ProjectiveEvaluationIncidence

namespace QuadraticIncidence.InfinityChart
variable (k R : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  {σ : Type u} [Finite σ]

/-- There is no common zero of the same original forms on any full infinity chart. -/
def NoCommonInfinityZero (g : σ → R) (d : ℕ)
    (c : Fin (d + 1) × Exponent σ → k) : Prop :=
  ∀ (j : Exponent σ), monomialFunction k R g j ≠ 0 →
    let A := boundaryRing k R g j
    ∀ (K : Type u) [Field K] [Algebra k K] [Algebra A K]
      [IsScalarTower k A K],
      ¬ ProjectiveEvaluationIncidence.Vanishes k A K (boundaryCoordinate k R g j)
        (d + 1) c

/-- The relation excludes genuine field-valued common zeros, not merely an
abstract incidence component or a chosen rational point. -/
theorem noCommonInfinityZero_of_relation (g : σ → R) (d : ℕ)
    (f : MvPolynomial (Fin (d + 1) × Exponent σ) k)
    (hf : ∀ j : Exponent σ, monomialFunction k R g j ≠ 0 →
      ProjectiveEvaluationIncidence.parameterMap (boundaryRing k R g j) k
        (boundaryCoordinate k R g j) (d + 1) f = 0)
    (c : Fin (d + 1) × Exponent σ → k) (hc : eval c f ≠ 0) :
    NoCommonInfinityZero k R g d c := by
  intro j hj
  dsimp only
  intro K _ _ _ _
  exact ProjectiveEvaluationIncidence.not_vanish_of_relation k (boundaryRing k R g j) K
    (boundaryCoordinate k R g j) (d + 1) f (hf j hj) c hc

/-- The actual original quadratic infinity admits one nonempty ground principal
open consisting entirely of basepoint-free parameter tuples. -/
theorem exists_infinity_avoidance_polynomial (g : σ → R) (d : ℕ)
    (hd : Algebra.trdeg k R ≤ (d : Cardinal.{u}) + 1) :
    ∃ f : MvPolynomial (Fin (d + 1) × Exponent σ) k, f ≠ 0 ∧
      ∀ c, eval c f ≠ 0 → NoCommonInfinityZero k R g d c := by
  obtain ⟨f, hf, hz⟩ := exists_nonzero_common_infinity_relation k R g d hd
  exact ⟨f, hf, noCommonInfinityZero_of_relation k R g d f hz⟩

end QuadraticIncidence.InfinityChart
