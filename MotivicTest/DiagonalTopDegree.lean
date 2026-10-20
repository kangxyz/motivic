/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.TopDegree
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual all-weight diagonal zero-cycle quotient

The consumers retain the literal identity-axis quotient, test odd and even
shift signs, and identify cosets with classes in the original derived group.
The audit rejects every nonstandard axiom in the implementation and consumers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic Motivic.DiagonalTopDegree

universe w u

namespace MotivicTest.DiagonalTopDegree

variable (k : Type u) [Field k]

/-- The quotient kernel is the full actual singular boundary image. -/
theorem actual_zero_iff_boundary (q : ℕ) (x : chains k q 0) :
    singularClass k q x = 0 ↔ ∃ y : chains k q 1, boundary k q y = x :=
  singularClass_eq_zero_iff k q x

/-- Odd weight retains the negative shifted differential. -/
theorem actual_odd_sign :
    (motivicRawBaseComplex k 3).d 2 3 =
      -((previousTermIso k 3).hom ≫ AddCommGrpCat.ofHom (boundary k 3) ≫
        (topTermIso k 3).inv) := by
  have h := raw_d_top k 3
  change (motivicRawBaseComplex k 3).d 2 3 = (-1 : ℤ) • _ at h
  simpa only [neg_one_zsmul] using h

/-- Even weight retains the positive shifted differential. -/
theorem actual_even_sign :
    (motivicRawBaseComplex k 2).d 1 2 =
      (previousTermIso k 2).hom ≫ AddCommGrpCat.ofHom (boundary k 2) ≫
        (topTermIso k 2).inv := by
  have h := raw_d_top k 2
  change (motivicRawBaseComplex k 2).d 1 2 = (1 : ℤ) • _ at h
  simpa only [one_zsmul] using h

/-- Weight zero uses the original degree minus one differential into degree zero. -/
theorem actual_zero_weight_sign :
    (motivicRawBaseComplex k 0).d (-1) 0 =
      (previousTermIso k 0).hom ≫ AddCommGrpCat.ofHom (boundary k 0) ≫
        (topTermIso k 0).inv := by
  have h := raw_d_top k 0
  change (motivicRawBaseComplex k 0).d (-1) 0 = (1 : ℤ) • _ at h
  simpa only [one_zsmul] using h

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Every weight uses the existing motivic cohomology, not a replacement group. -/
def actualDerivedEquivalence (q : ℕ) :
    (chains k q 0 ⧸ (boundary k q).range) ≃+
      motivicCohomology k q q (SmoothSite.base (Spec (.of k))) :=
  quotientToMotivicEquiv k q

/-- The comparison preserves the original representative exactly. -/
theorem actual_derived_coset (q : ℕ) (x : chains k q 0) :
    motivicRawBaseEvaluationComparison k q q
      (actualDerivedEquivalence k q (QuotientAddGroup.mk x)) = singularClass k q x :=
  quotientToMotivicEquiv_mk k q x

open Lean in
run_cmd do
  for name in #[``point, ``chains, ``boundary, ``boundary_eq_endpoints, ``zeroHomology,
      ``raw_outgoing_d_zero, ``rawClass, ``differential_rawClass, ``rawClass_surjective,
      ``rawClass_eq_zero_iff, ``raw_d, ``topTermIso, ``previousTermIso, ``raw_d_top,
      ``singularClass, ``singularClass_eq_zero_iff, ``singularClass_boundary,
      ``singularClass_surjective, ``singularClass_ker, ``quotientToRawEquiv,
      ``quotientToRawEquiv_mk, ``quotientToMotivicEquiv, ``quotientToMotivicEquiv_mk,
      ``actual_zero_iff_boundary, ``actual_odd_sign, ``actual_even_sign,
      ``actual_zero_weight_sign, ``actualDerivedEquivalence, ``actual_derived_coset] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual all-weight diagonal zero-cycle quotient uses only standard foundations."

end MotivicTest.DiagonalTopDegree
