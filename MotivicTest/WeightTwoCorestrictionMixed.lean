/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.CorestrictionMixed
public import Lean.Util.CollectAxioms

/-!
# Consumers of the literal mixed finite-point weight-two transfer

Both coordinate orders retain the whole finite point and the original
algebraic determinant norm. No separability or primitive-coordinate hypothesis
is available in these consumers.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open WeightTwoCorestriction WeightOnePointNorm

universe u

namespace MotivicTest.WeightTwoCorestrictionMixed

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

/-- The left coordinate is fixed over the original field before genuine finite pushforward. -/
theorem actual_mixed_left (a : kˣ) (b : Eˣ) :
    pointPushforward (k := k) ((Cor.graphFunctor E).map
      (WeightTwoSymbols.rationalPair E (Units.map (algebraMap k E).toMonoidHom a) b)) =
      WeightOneFinitePointNorm.unitPointCorrespondence (k := k) b ≫
        (Cor.graphFunctor k).map (WeightTwoSymbols.prependUnit k a) :=
  pointPushforward_rationalPair_prepend a b

/-- The right coordinate is fixed over the original field before genuine finite pushforward. -/
theorem actual_mixed_right (a : kˣ) (b : Eˣ) :
    pointPushforward (k := k) ((Cor.graphFunctor E).map
      (WeightTwoSymbols.rationalPair E b (Units.map (algebraMap k E).toMonoidHom a))) =
      WeightOneFinitePointNorm.unitPointCorrespondence (k := k) b ≫
        (Cor.graphFunctor k).map (WeightTwoSymbols.appendUnit k a) :=
  pointPushforward_rationalPair_append a b

/-- The finite pushforward class is the original norm symbol. -/
theorem actual_norm_symbol (a : kˣ) (b : Eˣ) :
    WeightTwoSymbols.cycleClass k (pointPushforward (k := k) ((Cor.graphFunctor E).map
      (WeightTwoSymbols.rationalPair E (Units.map (algebraMap k E).toMonoidHom a) b))) =
      WeightTwoSymbols.graphSymbol k a (Units.map (Algebra.norm k) b) :=
  cycleClass_pointPushforward_prepend a b

/-- The additive transfer on the original H22 has the left-fixed determinant norm formula. -/
theorem actual_corestriction_left (a : kˣ) (b : Eˣ) :
    corestriction (k := k) (WeightTwoSymbols.graphSymbol E
      (Units.map (algebraMap k E).toMonoidHom a) b) =
      WeightTwoSymbols.graphSymbol k a (Units.map (Algebra.norm k) b) :=
  corestriction_graphSymbol_prepend a b

/-- The same original H22 transfer has the right-fixed determinant norm formula. -/
theorem actual_corestriction_right (a : kˣ) (b : Eˣ) :
    corestriction (k := k) (WeightTwoSymbols.graphSymbol E b
      (Units.map (algebraMap k E).toMonoidHom a)) =
      WeightTwoSymbols.graphSymbol k (Units.map (Algebra.norm k) b) a :=
  corestriction_graphSymbol_append a b

open Lean in
run_cmd do
  for name in #[``toIntegralCycle_graph, ``ambientMap_snd, ``torusMap_coordinate,
      ``scalarPoint_zero_transport, ``toIntegralCycle_pointPushforward_graph,
      ``scalarPoint_prepend, ``scalarPoint_append,
      ``pointPushforward_rationalPair_prepend, ``pointPushforward_rationalPair_append,
      ``cycleClass_pointPushforward_prepend, ``cycleClass_pointPushforward_append,
      ``actual_mixed_left, ``actual_mixed_right, ``actual_norm_symbol,
      ``corestriction_graphSymbol_prepend, ``corestriction_graphSymbol_append,
      ``actual_corestriction_left, ``actual_corestriction_right] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Literal mixed weight-two transfers use only standard foundations."

end MotivicTest.WeightTwoCorestrictionMixed
