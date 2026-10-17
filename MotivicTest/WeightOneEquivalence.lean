/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightOneEquivalence
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Consumers of the actual weight-one motivic equivalence

The equivalence is tested on the original derived motivic group and its actual
raw complex, over an arbitrary field. The rejecting axiom audit includes the
full geometric interpolation and point-presentation dependency chains.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Motivic
open Motivic.WeightOneHomologyNorm Motivic.WeightOneEquivalence

universe w u

namespace MotivicTest.WeightOneEquivalence

variable (k : Type u) [Field k]

/-- Every original raw homology class is represented by an actual signed point cycle. -/
theorem actual_cycle_representatives : Function.Surjective (cycleClass k) :=
  cycleClass_surjective k

/-- The identity is killed by the original reduced-torus quotient. -/
theorem original_identity_relation : graphUnitClass k 1 = 0 := graphUnitClass_one k

/-- The unit law is proved from actual quadratic interpolation. -/
theorem original_multiplication_relation (a b : kˣ) :
    graphUnitClass k (a * b) = graphUnitClass k a + graphUnitClass k b :=
  graphUnitClass_mul k a b

/-- Inseparable closed points are covered by the same actual generator theorem. -/
theorem arbitrary_point_norm (Z : WeightOnePointNorm.Generator k) :
    cycleClass k Z.cycle = graphUnitClass k (WeightOnePointNorm.generatorNorm Z) :=
  cycleClass_generator k Z

/-- The norm's kernel on the actual raw homology vanishes. -/
theorem actual_homology_kernel (x : (motivicRawBaseComplex k 1).homology 1)
    (hx : homologyNorm k x = 0) : x = 0 := by
  apply homologyNorm_injective k
  simpa only [map_zero] using hx

/-- The homology inverse retains the original graph, with no sign or inverse twist. -/
theorem inverse_graph (a : kˣ) :
    (homologyEquiv k).symm (Additive.ofMul a) = graphUnitClass k a :=
  homologyEquiv_symm_apply k (Additive.ofMul a)

/-- Coincident roots in characteristic two still satisfy the graph law. -/
example (a : (ZMod 2)ˣ) :
    graphUnitClass (ZMod 2) (a * a) =
      graphUnitClass (ZMod 2) a + graphUnitClass (ZMod 2) a :=
  graphUnitClass_mul (ZMod 2) a a

/-- Positive-characteristic actual homology has the proved norm equivalence. -/
example : (motivicRawBaseComplex (ZMod 2) 1).homology 1 ≃+ Additive (ZMod 2)ˣ :=
  homologyEquiv (ZMod 2)

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The requested equivalence uses the originally defined derived motivic group. -/
def actual_weight_one_equivalence :
    motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k))) ≃+ Additive kˣ :=
  weightOneEquiv k

/-- Its forward map is precisely the actual derived norm. -/
theorem actual_derived_norm_formula
    (x : motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k)))) :
    actual_weight_one_equivalence k x = motivicNorm k x := weightOneEquiv_apply k x

/-- The original derived norm is bijective without any extra hypotheses. -/
theorem actual_derived_norm_bijective : Function.Bijective (motivicNorm k) :=
  ⟨motivicNorm_injective k, motivicNorm_surjective k⟩

/-- The original derived inverse transports the actual unit graph. -/
theorem actual_derived_inverse_graph (a : kˣ) :
    (actual_weight_one_equivalence k).symm (Additive.ofMul a) =
      (motivicRawBaseEvaluationComparison k 1 1).symm (graphUnitClass k a) :=
  weightOneEquiv_symm_apply k (Additive.ofMul a)

open Lean in
run_cmd do
  for name in #[``rawClass_surjective, ``differential_rawClass, ``rawClass_boundary,
      ``singularClass, ``singularClass_boundary, ``cycleClass, ``cycleClass_graph,
      ``cycleClass_surjective, ``homologyNorm_cycleClass, ``rationalPoint_one,
      ``graphUnitClass_one, ``singularClass_quotient, ``singularClass_face_quotient,
      ``cycleClass_endpoints, ``cycleClass_polynomial_target, ``cycleClass_polynomial,
      ``graphUnitClass_mul, ``graphUnitHom, ``cycleClass_generator,
      ``graphUnitHom_comp_cycleNorm, ``graphUnitHom_homologyNorm, ``homologyNorm_injective,
      ``homologyEquiv, ``homologyEquiv_apply, ``homologyEquiv_symm_apply,
      ``motivicNorm_injective, ``weightOneEquiv, ``weightOneEquiv_apply,
      ``weightOneEquiv_symm_apply, ``actual_cycle_representatives,
      ``original_identity_relation, ``original_multiplication_relation,
      ``arbitrary_point_norm, ``actual_homology_kernel, ``inverse_graph,
      ``actual_weight_one_equivalence, ``actual_derived_norm_formula,
      ``actual_derived_norm_bijective, ``actual_derived_inverse_graph] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual weight-one motivic equivalence uses only standard Lean foundations."

end MotivicTest.WeightOneEquivalence
