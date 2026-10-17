/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoMixedNorm
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual fixed-coordinate norm symbols

Original signed cycles and full extension-field pushforward multiplicities are
retained. These statements do not assume a weight-two transfer map.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open WeightOnePointNorm WeightTwoSymbols WeightTwoMixedNorm

universe u

namespace MotivicTest.WeightTwoMixedNorm

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- The left mixed norm formula acts on an actual whole finite pushed point. -/
theorem actual_left (a : kˣ) (b : Eˣ) :
    cycleClass k (WeightOneFinitePointNorm.unitPointCorrespondence (k := k) b ≫
      (Cor.graphFunctor k).map (prependUnit k a)) =
        graphSymbol k a (Units.map (Algebra.norm k) b) :=
  finite_point_prepend k a b

/-- The corresponding right formula does not assume a primitive coordinate. -/
theorem actual_right (a : kˣ) (b : Eˣ) :
    cycleClass k (WeightOneFinitePointNorm.unitPointCorrespondence (k := k) b ≫
      (Cor.graphFunctor k).map (appendUnit k a)) =
        graphSymbol k (Units.map (Algebra.norm k) b) a :=
  finite_point_append k a b

/-- A base-field unit keeps the full extension degree, including for inseparable extensions. -/
theorem base_unit_degree (a b : kˣ) :
    cycleClass k (WeightOneFinitePointNorm.unitPointCorrespondence (k := k)
      (Units.map (algebraMap k E).toMonoidHom b) ≫
        (Cor.graphFunctor k).map (prependUnit k a)) =
          graphSymbol k a (b ^ Module.finrank k E) := by
  rw [cycle_prepend]
  have h : Units.map (Algebra.norm k) (Units.map (algebraMap k E).toMonoidHom b) =
      b ^ Module.finrank k E := by
    apply Units.ext
    exact Algebra.norm_algebraMap (b : k)
  rw [WeightOneFinitePointNorm.cycleNorm_unitPointCorrespondence]
  exact congrArg (graphSymbol k a) h

omit [Field E] [Algebra k E] [Module.Finite k E] in
/-- Signed multiplicities remain in the actual norm homomorphism. -/
theorem signed_cycles (a : kˣ) (β : point k ⟶ WeightOnePointNorm.target k) (n : ℤ) :
    cycleClass k ((n • β) ≫ (Cor.graphFunctor k).map (prependUnit k a)) =
      graphSymbol k a (cycleNorm k (n • β)).toMul :=
  cycle_prepend k a (n • β)

open Lean in
run_cmd do
  for name in #[``polynomial_postcompose, ``polynomial_prepend, ``polynomial_append,
      ``generator_prepend, ``generator_append, ``cycle_prepend, ``cycle_append,
      ``finite_point_prepend, ``finite_point_append,
      ``actual_left, ``actual_right, ``base_unit_degree, ``signed_cycles] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Mixed norm symbols use only standard Lean foundations."

end MotivicTest.WeightTwoMixedNorm
