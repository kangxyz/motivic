/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalCoordinateInsertion
public import Aglib.KTheory.MilnorK.LowDegree
public import Aglib.KTheory.MilnorK.CompatibilityK2
public import Motivic.Cohomology.Motivic.WeightOneEquivalence
public import Motivic.Cohomology.Motivic.WeightTwoMilnorSymbol

/-!
# The all-weight Milnor symbol in actual diagonal motivic cohomology

The genuine rational graph classes satisfy the standard all-degree Milnor
relations by actual finite interpolation and fixed-coordinate insertion of the
proved Steinberg class. Their universal quotient lift is the forward map to
the original derived group. Its weight-one and weight-two values retain the
already established maps. No injectivity or surjectivity is asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe w u

namespace Motivic.DiagonalMilnorSymbol

open DiagonalTopDegree DiagonalCycleSymbols

variable (k : Type u) [Field k] [CharZero k]

/-- Actual rational graph classes satisfy precisely the standard all-weight symbol relations. -/
theorem graphSymbol_isSymbolMap (q : ℕ) : MilnorK.IsSymbolMap (graphSymbol k q) where
  map_mul := graphSymbol_mul k q
  steinberg a i j hij hab :=
    DiagonalCoordinateInsertion.graphSymbol_steinberg k q a i j (by
      intro h
      have hv := congrArg Fin.val h
      omega) hab

/-- The standard all-weight Milnor presentation maps to the original raw homology. -/
def rawSymbol (q : ℕ) : MilnorK.K k q →+ (motivicRawBaseComplex k q).homology q :=
  (MilnorK.lift (graphSymbol k q) (graphSymbol_isSymbolMap k q)).toAddMonoidHom

/-- Every Milnor generator is sent to its actual rational graph class. -/
@[simp] theorem rawSymbol_symbol (q : ℕ) (a : Fin q → kˣ) :
    rawSymbol k q (MilnorK.symbol a) = graphSymbol k q a :=
  MilnorK.lift_symbol (graphSymbol k q) (graphSymbol_isSymbolMap k q) a

omit [CharZero k] in
/-- The one-entry graph is the already constructed actual weight-one class. -/
theorem graphSymbol_one_weight (a : Fin 1 → kˣ) :
    graphSymbol k 1 a = WeightOneHomologyNorm.graphUnitClass k (a 0) := by
  have h : rationalTuple k 1 a = WeightOnePointNorm.rationalPoint k (a 0) := by
    apply SmoothSite.torusPower_hom_ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [rationalTuple, WeightOnePointNorm.rationalPoint,
      SmoothSite.torusPowerLift_coordinate]
  unfold graphSymbol
  rw [h]
  rfl

/-- In weight one, the original homology norm is the standard Milnor-to-units equivalence. -/
theorem rawSymbol_one_comparison (x : MilnorK.K k 1) :
    WeightOneHomologyNorm.homologyNorm k (rawSymbol k 1 x) = MilnorK.oneEquiv k x := by
  have h : (WeightOneHomologyNorm.homologyNorm k).comp (rawSymbol k 1) =
      (MilnorK.oneEquiv k).toAddMonoidHom := by
    apply MilnorK.addHom_ext
    intro a
    change WeightOneHomologyNorm.homologyNorm k (rawSymbol k 1 (MilnorK.symbol a)) = _
    rw [rawSymbol_symbol, graphSymbol_one_weight, WeightOneHomologyNorm.homologyNorm_graphUnitClass]
    exact (MilnorK.oneEquiv_symbol k a).symm
  exact DFunLike.congr_fun h x

omit [CharZero k] in
/-- The two-entry graph is exactly the already constructed original weight-two symbol. -/
theorem graphSymbol_two_weight (a : Fin 2 → kˣ) :
    graphSymbol k 2 a = WeightTwoSymbols.graphSymbol k (a 0) (a 1) := by
  have h : rationalTuple k 2 a = WeightTwoSymbols.rationalPair k (a 0) (a 1) := by
    apply SmoothSite.torusPower_hom_ext
    intro i
    fin_cases i <;>
      simp only [rationalTuple, WeightTwoSymbols.rationalPair,
        SmoothSite.torusPowerLift_coordinate] <;> rfl
  unfold graphSymbol
  rw [h]
  rfl

/-- The general symbol agrees with the existing K₂ map through the proved standard comparison. -/
theorem rawSymbol_two_comparison (x : MilnorK.K k 2) :
    rawSymbol k 2 x =
      WeightTwoMilnorSymbol.rawMilnorSymbol k (MilnorK.twoEquiv k x) := by
  have h : rawSymbol k 2 = (WeightTwoMilnorSymbol.rawMilnorSymbol k).comp
      (MilnorK.twoEquiv k).toAddMonoidHom := by
    apply MilnorK.addHom_ext
    intro a
    change rawSymbol k 2 (MilnorK.symbol a) =
      WeightTwoMilnorSymbol.rawMilnorSymbol k (MilnorK.twoEquiv k (MilnorK.symbol a))
    rw [rawSymbol_symbol, graphSymbol_two_weight, MilnorK.twoEquiv_symbol,
      WeightTwoMilnorSymbol.rawMilnorSymbol_symbol]
  exact DFunLike.congr_fun h x

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The forward all-weight symbol map to the originally defined derived diagonal group. -/
def motivicSymbol (q : ℕ) : MilnorK.K k q →+
    motivicCohomology k q q (SmoothSite.base (Spec (.of k))) :=
  (motivicRawBaseEvaluationComparison k q q).symm.toAddMonoidHom.comp (rawSymbol k q)

/-- The original field evaluation comparison retains the actual raw symbol map. -/
theorem motivicSymbol_comparison (q : ℕ) (x : MilnorK.K k q) :
    motivicRawBaseEvaluationComparison k q q (motivicSymbol k q x) = rawSymbol k q x :=
  (motivicRawBaseEvaluationComparison k q q).apply_symm_apply _

/-- A standard Milnor symbol maps to the derived class of its original rational tuple. -/
@[simp] theorem motivicSymbol_symbol (q : ℕ) (a : Fin q → kˣ) :
    motivicSymbol k q (MilnorK.symbol a) =
      (motivicRawBaseEvaluationComparison k q q).symm (graphSymbol k q a) := by
  change (motivicRawBaseEvaluationComparison k q q).symm (rawSymbol k q (MilnorK.symbol a)) = _
  rw [rawSymbol_symbol]

/-- In degree two, the all-weight map preserves the original derived Milnor symbol exactly. -/
theorem motivicSymbol_two_comparison (x : MilnorK.K k 2) :
    motivicSymbol k 2 x =
      WeightTwoMilnorSymbol.motivicMilnorSymbol k (MilnorK.twoEquiv k x) := by
  apply (motivicRawBaseEvaluationComparison k 2 2).injective
  exact (motivicSymbol_comparison k 2 x).trans ((rawSymbol_two_comparison k x).trans
    (WeightTwoMilnorSymbol.motivicMilnorSymbol_comparison k (MilnorK.twoEquiv k x)).symm)

end Motivic.DiagonalMilnorSymbol
