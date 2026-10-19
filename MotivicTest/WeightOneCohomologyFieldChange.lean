/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.CohomologyFieldChange
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Consumers of the original weight-one equivalences under field change

The squares use the actual cohomology maps and the literal map of field units.
The inverse formula tests the original graph convention. Composite and
characteristic-dividing levels are included without an invertibility premise.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open Motivic.WeightOneHomologyNorm Motivic.WeightOneEquivalence
open Motivic.WeightOneFiniteCoefficients Motivic.WeightOneCohomologyFieldChange

universe w u

namespace MotivicTest.WeightOneCohomologyFieldChange

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)

/-- The original raw graph class maps to the graph of the ordinary image unit. -/
theorem raw_graph (a : kˣ) :
    HomologicalComplex.homologyMap (motivicRawBaseComplexMap φ 1) 1 (graphUnitClass k a) =
      graphUnitClass L (Units.map φ.toMonoidHom a) :=
  graphUnitClass_fieldChange φ a

/-- The quotient map is the ordinary induced map on actual unit cosets. -/
theorem quotient_unit (n : ℕ) (a : kˣ) :
    unitsModuloPowersFieldChange φ n (QuotientGroup.mk a) =
      (QuotientGroup.mk (Units.map φ.toMonoidHom a) : unitsModuloPowers L n) :=
  unitsModuloPowersFieldChange_mk φ n a

variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of L))) AddCommGrpCat.{u + 1})]

/-- The square is equality of the original integral homomorphisms. -/
theorem integral_square :
    (weightOneEquiv L).toAddMonoidHom.comp (motivicCohomologyFieldChange φ 1 1) =
      (Units.map φ.toMonoidHom).toAdditive.comp (weightOneEquiv k).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  exact weightOneEquiv_fieldChange φ x

/-- The original integral graph inverse retains the unit, without any sign or inverse twist. -/
theorem integral_graph (a : kˣ) :
    motivicCohomologyFieldChange φ 1 1
      ((motivicRawBaseEvaluationComparison k 1 1).symm (graphUnitClass k a)) =
    (motivicRawBaseEvaluationComparison L 1 1).symm
      (graphUnitClass L (Units.map φ.toMonoidHom a)) := by
  simpa only [weightOneEquiv_symm_apply, toMul_ofMul] using
    weightOneEquiv_symm_fieldChange φ a

/-- The square is equality of the actual finite homomorphisms, at any natural level. -/
theorem finite_square (n : ℕ) :
    (weightOneFiniteEquiv L n).toAddMonoidHom.comp (motivicFiniteCohomologyFieldChange φ 1 1 n) =
      (unitsModuloPowersFieldChange φ n).toAdditive.comp
        (weightOneFiniteEquiv k n).toAddMonoidHom := by
  apply AddMonoidHom.ext
  intro x
  exact weightOneFiniteEquiv_fieldChange φ n x

/-- The actual reduction square sends the original norm to its ordinary image coset. -/
theorem finite_reduction (n : ℕ)
    (x : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k)))) :
    weightOneFiniteEquiv L n
      (motivicFiniteCohomologyFieldChange φ 1 1 n (motivicBaseIntegralReduction k 1 1 n x)) =
        Additive.ofMul (QuotientGroup.mk
          (Units.map φ.toMonoidHom (motivicNorm k x).toMul) : unitsModuloPowers L n) := by
  rw [motivicCohomologyFieldChange_integralReduction,
    weightOneFiniteEquiv_integralReduction, motivicNorm_fieldChange]
  rfl

/-- Every unit representative of a finite class retains the literal inverse formula. -/
theorem finite_inverse (n : ℕ) (a : kˣ) :
    motivicFiniteCohomologyFieldChange φ 1 1 n
      ((weightOneFiniteEquiv k n).symm
        (Additive.ofMul (QuotientGroup.mk a : unitsModuloPowers k n))) =
      (weightOneFiniteEquiv L n).symm
        (Additive.ofMul (QuotientGroup.mk (Units.map φ.toMonoidHom a) :
          unitsModuloPowers L n)) :=
  weightOneFiniteEquiv_symm_mk_fieldChange φ n a

/-- Level one uses the original quotient equivalence. -/
theorem level_one
    (x : motivicFiniteCohomology k 1 1 1 (SmoothSite.base (Spec (.of k)))) :
    weightOneFiniteEquiv L 1 (motivicFiniteCohomologyFieldChange φ 1 1 1 x) =
      (unitsModuloPowersFieldChange φ 1).toAdditive (weightOneFiniteEquiv k 1 x) :=
  weightOneFiniteEquiv_fieldChange φ 1 x

/-- A concrete composite level uses exactly the same quotient map. -/
theorem level_twelve
    (x : motivicFiniteCohomology k 1 1 12 (SmoothSite.base (Spec (.of k)))) :
    weightOneFiniteEquiv L 12 (motivicFiniteCohomologyFieldChange φ 1 1 12 x) =
      (unitsModuloPowersFieldChange φ 12).toAdditive (weightOneFiniteEquiv k 12 x) :=
  weightOneFiniteEquiv_fieldChange φ 12 x

section CharacteristicTwo

variable {E : Type} [Field E] (ψ : ZMod 2 →+* E)
variable [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of (ZMod 2)))) AddCommGrpCat.{1})]
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{1})]

/-- The same exact square includes the characteristic-dividing composite coefficient six. -/
theorem characteristic_dividing
    (x : motivicFiniteCohomology (ZMod 2) 1 1 6 (SmoothSite.base (Spec (.of (ZMod 2))))) :
    weightOneFiniteEquiv E 6 (motivicFiniteCohomologyFieldChange ψ 1 1 6 x) =
      (unitsModuloPowersFieldChange ψ 6).toAdditive (weightOneFiniteEquiv (ZMod 2) 6 x) :=
  weightOneFiniteEquiv_fieldChange ψ 6 x

end CharacteristicTwo

/-- Identity-field change is literally the identity on the original integral group. -/
theorem integral_identity :
    motivicCohomologyFieldChange (RingHom.id k) 1 1 = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  exact integral_fieldChange_id x

/-- Identity-field change is literally the identity on every original finite group. -/
theorem finite_identity (n : ℕ) :
    motivicFiniteCohomologyFieldChange (RingHom.id k) 1 1 n = AddMonoidHom.id _ := by
  apply AddMonoidHom.ext
  intro x
  exact finite_fieldChange_id n x

variable {M : Type u} [Field M] (ψ : L →+* M)
  [HasDerivedCategory.{w}
    (Sheaf (SmoothSite.nisnevichTopology (Spec (.of M))) AddCommGrpCat.{u + 1})]

/-- Computed integral weight one has the literal composition law on the actual groups. -/
theorem integral_composition :
    (motivicCohomologyFieldChange ψ 1 1).comp (motivicCohomologyFieldChange φ 1 1) =
      motivicCohomologyFieldChange (ψ.comp φ) 1 1 := by
  apply AddMonoidHom.ext
  intro x
  exact integral_fieldChange_comp φ ψ x

/-- Computed finite weight one has the literal composition law at every level. -/
theorem finite_composition (n : ℕ) :
    (motivicFiniteCohomologyFieldChange ψ 1 1 n).comp
      (motivicFiniteCohomologyFieldChange φ 1 1 n) =
        motivicFiniteCohomologyFieldChange (ψ.comp φ) 1 1 n := by
  apply AddMonoidHom.ext
  intro x
  exact finite_fieldChange_comp φ ψ n x

open Lean in
run_cmd do
  for name in #[
      `Motivic.WeightOneCohomologyFieldChange.zeroProductIso_fieldChange_hom,
      `Motivic.WeightOneCohomologyFieldChange.zeroProductIso_fieldChange_inv,
      `Motivic.WeightOneCohomologyFieldChange.degreeZeroNorm_fieldChange,
      `Motivic.WeightOneCohomologyFieldChange.rawDegreeZeroNorm_fieldChange,
      `Motivic.WeightOneCohomologyFieldChange.rawClass_fieldChange,
      `Motivic.WeightOneCohomologyFieldChange.homologyNorm_fieldChange,
      `Motivic.WeightOneCohomologyFieldChange.graphUnitClass_fieldChange,
      `Motivic.WeightOneCohomologyFieldChange.powerSubgroup_le_comap,
      `Motivic.WeightOneCohomologyFieldChange.unitsModuloPowersFieldChange,
      `Motivic.WeightOneCohomologyFieldChange.unitsModuloPowersFieldChange_mk,
      `Motivic.WeightOneCohomologyFieldChange.motivicNorm_fieldChange,
      `Motivic.WeightOneCohomologyFieldChange.weightOneEquiv_fieldChange,
      `Motivic.WeightOneCohomologyFieldChange.weightOneEquiv_symm_fieldChange,
      `Motivic.WeightOneCohomologyFieldChange.unitReduction_fieldChange,
      `Motivic.WeightOneCohomologyFieldChange.weightOneFiniteEquiv_fieldChange,
      `Motivic.WeightOneCohomologyFieldChange.weightOneFiniteEquiv_symm_mk_fieldChange,
      `Motivic.WeightOneCohomologyFieldChange.integral_fieldChange_id,
      `Motivic.WeightOneCohomologyFieldChange.finite_fieldChange_id,
      `Motivic.WeightOneCohomologyFieldChange.integral_fieldChange_comp,
      `Motivic.WeightOneCohomologyFieldChange.finite_fieldChange_comp,
      `MotivicTest.WeightOneCohomologyFieldChange.integral_identity,
      `MotivicTest.WeightOneCohomologyFieldChange.finite_identity,
      `MotivicTest.WeightOneCohomologyFieldChange.integral_composition,
      `MotivicTest.WeightOneCohomologyFieldChange.finite_composition,
      `MotivicTest.WeightOneCohomologyFieldChange.integral_square,
      `MotivicTest.WeightOneCohomologyFieldChange.integral_graph,
      `MotivicTest.WeightOneCohomologyFieldChange.finite_square,
      `MotivicTest.WeightOneCohomologyFieldChange.finite_reduction,
      `MotivicTest.WeightOneCohomologyFieldChange.finite_inverse,
      `MotivicTest.WeightOneCohomologyFieldChange.level_one,
      `MotivicTest.WeightOneCohomologyFieldChange.level_twelve,
      `MotivicTest.WeightOneCohomologyFieldChange.characteristic_dividing] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[`propext, `Classical.choice, `Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual weight-one field-change squares use only standard Lean foundations."

end MotivicTest.WeightOneCohomologyFieldChange
