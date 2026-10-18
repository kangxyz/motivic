/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.DiagonalMilnorEquivalence
public import Lean.Util.CollectAxioms

/-! Both directions of comparison with the original derived diagonal group, in every weight. -/
@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Motivic
open PresheafWithTransfers DiagonalMilnorSymbol DiagonalMilnorBoundaryDescent
universe w u
namespace MotivicTest.DiagonalMilnorEquivalence
variable (k : Type u) [Field k] [CharZero k] (q : ℕ)

/-- The original finite field, in every degree, satisfies the actual norm/transfer square. -/
theorem actual_finite_norm_square {E : Type u} [Field E] [CharZero E]
    [Algebra k E] [Module.Finite k E] (x : MilnorK.K E q) :
    rawSymbol k q (MilnorK.finiteExtensionNorm k E q x) =
      DiagonalCorestriction.corestriction (k := k) q (rawSymbol E q x) :=
  DiagonalPolynomialNormComparisonAll.rawSymbol_finiteExtensionNorm q x

/-- An original raw class is recovered, not merely a forward symbol. -/
theorem actual_raw_opposite_inverse (x : (motivicRawBaseComplex k q).homology q) :
    rawSymbol k q (rawNorm k q x) = x :=
  Motivic.DiagonalMilnorEquivalence.rawSymbol_rawNorm k q x

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- An arbitrary original derived diagonal class is recovered by the same two maps. -/
theorem actual_derived_opposite_inverse
    (x : motivicCohomology k q q (SmoothSite.base (Spec (.of k)))) :
    motivicSymbol k q (motivicNorm k q x) = x :=
  Motivic.DiagonalMilnorEquivalence.motivicSymbol_motivicNorm k q x

/-- The equivalence retains the literal original Hnn codomain
and the existing symbol as its forward map. -/
theorem actual_derived_forward_map (x : MilnorK.K k q) :
    Motivic.DiagonalMilnorEquivalence.motivicEquiv k q x = motivicSymbol k q x := rfl

/-- Weight zero is included without a positive-weight premise. -/
theorem actual_weight_zero_inverse
    (x : motivicCohomology k 0 0 (SmoothSite.base (Spec (.of k)))) :
    motivicSymbol k 0 (motivicNorm k 0 x) = x :=
  Motivic.DiagonalMilnorEquivalence.motivicSymbol_motivicNorm k 0 x

open Lean in
run_cmd do
  for name in #[``actual_finite_norm_square, ``actual_raw_opposite_inverse,
      ``actual_derived_opposite_inverse, ``actual_derived_forward_map, ``actual_weight_zero_inverse,
      ``Motivic.DiagonalMilnorEquivalence.rawEquiv,
      ``Motivic.DiagonalMilnorEquivalence.motivicEquiv,
      ``DiagonalPolynomialNormComparisonAll.rawSymbol_polynomialNorm] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Original all-weight raw and derived Milnor equivalence: standard foundations only."

end MotivicTest.DiagonalMilnorEquivalence
