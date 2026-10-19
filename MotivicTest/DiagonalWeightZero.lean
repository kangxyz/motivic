/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.WeightZero
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual integral weight-zero field cohomology

These use actual geometric correspondence coefficients and the original
signed singular boundary and derived cohomology. The final audit rejects all
nonstandard assumptions in the implementations and consumers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open Motivic.DiagonalTopDegree Motivic.DiagonalWeightZero

universe w u

namespace MotivicTest.DiagonalWeightZero

variable (k : Type u) [Field k]

/-- The actual structural graph has coefficient exactly one. -/
theorem actual_graph_degree_one :
    correspondenceEquiv k (simplexSource k 0)
      ((Cor.graphFunctor k).map (toBase k (simplexSource k 0))) = 1 :=
  correspondenceEquiv_graph k _

/-- Signed negative multiplicity retains the literal negative integer coefficient. -/
theorem actual_negative_graph_degree :
    correspondenceEquiv k (simplexSource k 0)
      ((-3 : ℤ) • (Cor.graphFunctor k).map (toBase k (simplexSource k 0))) = -3 := by
  rw [map_zsmul, correspondenceEquiv_graph, zsmul_eq_mul, mul_one, Int.cast_id]

/-- The genuine endpoint boundary, not an imposed relation, is zero. -/
theorem actual_boundary_zero (x : chains k 0 1) : boundary k 0 x = 0 := by
  rw [boundary_eq_zero]
  rfl

/-- A zero-cycle vanishes in the original raw homology exactly when it is zero. -/
theorem actual_raw_class_zero_iff (x : chains k 0 0) :
    singularClass k 0 x = 0 ↔ x = 0 := by
  rw [singularClass_eq_zero_iff]
  simp only [boundary_eq_zero, AddMonoidHom.zero_apply, exists_const, eq_comm]

/-- The literal quotient evaluates every original zero-cycle correctly. -/
theorem actual_quotient_degree (x : chains k 0 0) :
    quotientEquiv k (QuotientAddGroup.mk x) = chainEquiv k 0 x :=
  quotientEquiv_mk k x

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- Every field, without characteristic restrictions, has the original `H^{0,0}=ℤ`. -/
def actual_derived_equivalence :
    motivicCohomology k 0 0 (SmoothSite.base (Spec (.of k))) ≃+ ℤ := motivicEquiv k

/-- The original all-degree Milnor presentation computes the original derived group. -/
def actual_milnor_equivalence : MilnorK.K k 0 ≃+
    motivicCohomology k 0 0 (SmoothSite.base (Spec (.of k))) := milnorEquiv k

/-- The zeroth Milnor symbol has the canonical integer normalization. -/
theorem actual_empty_symbol_degree (a : MilnorK.SymbolTuple k 0) :
    motivicEquiv k (milnorEquiv k (MilnorK.symbol a)) = 1 := by
  rw [milnorEquiv_symbol, motivicEquiv_graphClass]

/-- The canonical empty symbol is the actual structural graph class. -/
theorem actual_empty_symbol_graph (a : MilnorK.SymbolTuple k 0) :
    milnorEquiv k (MilnorK.symbol a) = graphClass k := milnorEquiv_symbol k a

/-- The inverse sends a negative integer to the literal negative graph multiple. -/
theorem actual_derived_negative_generator :
    (motivicEquiv k).symm (-3) = (-3 : ℤ) • graphClass k :=
  motivicEquiv_symm_apply k (-3)

/-- The all-weight forward map is the canonical degree-zero equivalence. -/
theorem actual_forward_symbol_zero [CharZero k] (x : MilnorK.K k 0) :
    DiagonalMilnorSymbol.motivicSymbol k 0 x = milnorEquiv k x :=
  motivicSymbol_zero k x

open Lean in
run_cmd do
  for name in #[``toBase, ``baseGenerator, ``eq_baseGenerator, ``graph_toBase,
      ``correspondenceEquiv, ``correspondenceEquiv_graph, ``correspondenceEquiv_graph_comp,
      ``sectionsCorrespondenceEquiv, ``sectionsCorrespondenceEquiv_transfer,
      ``sectionsEquiv, ``sectionsEquiv_transfer, ``simplexSource, ``simplexSource_integral,
      ``chainEquiv, ``chainEquiv_face, ``boundary_eq_zero, ``boundary_range_eq_bot,
      ``quotientEquiv, ``quotientEquiv_mk, ``sectionsCorrespondenceEquiv_reduced,
      ``graphChain, ``chainEquiv_graphChain, ``graphClass, ``motivicEquiv_graphClass,
      ``motivicEquiv_symm_apply, ``milnorEquiv_symbol, ``motivicEquiv,
      ``motivicEquiv_class, ``milnorEquiv, ``graphSymbol_zero, ``motivicSymbol_zero,
      ``actual_graph_degree_one, ``actual_negative_graph_degree, ``actual_boundary_zero,
      ``actual_raw_class_zero_iff, ``actual_quotient_degree, ``actual_derived_equivalence,
      ``actual_milnor_equivalence, ``actual_empty_symbol_degree, ``actual_empty_symbol_graph,
      ``actual_derived_negative_generator, ``actual_forward_symbol_zero] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual weight-zero integral field computation uses only standard foundations."

end MotivicTest.DiagonalWeightZero
