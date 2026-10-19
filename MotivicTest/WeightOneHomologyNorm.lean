/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.HomologyNorm
public import Mathlib.Algebra.Field.ZMod
public import Lean.Util.CollectAxioms

/-!
# Actual weight-one homology norm consumers

These use the canonical raw complex and genuinely defined derived group over
an arbitrary field. No injectivity or weight-one equivalence is presumed.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory AlgebraicGeometry Motivic
open Motivic.WeightOneHomologyNorm

universe w u

namespace MotivicTest.WeightOneHomologyNorm

variable (k : Type u) [Field k]

/-- Every actual raw class has exactly its original point norm. -/
theorem class_formula (x : (motivicRawBaseComplex k 1).X 1) :
    homologyNorm k (rawClass k x) = WeightOneBoundaryNorm.rawDegreeZeroNorm k x :=
  homologyNorm_rawClass k x

/-- Arbitrary integer multiples retain the norm's additive law. -/
theorem signed_graph_formula (a : kˣ) (n : ℤ) :
    homologyNorm k (n • graphUnitClass k a) = n • Additive.ofMul a := by
  rw [map_zsmul, homologyNorm_graphUnitClass]

/-- Graph classes prove surjectivity on the actual homology object. -/
theorem arbitrary_field_surjective : Function.Surjective (homologyNorm k) :=
  homologyNorm_surjective k

/-- Positive characteristic is included in the actual construction. -/
example : Function.Surjective (homologyNorm (ZMod 2)) :=
  homologyNorm_surjective (ZMod 2)

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]

/-- The norm acts on the original derived motivic group, not a replacement definition. -/
def actualDerivedNorm :
    motivicCohomology k 1 1 (SmoothSite.base (Spec (.of k))) →+ Additive kˣ :=
  motivicNorm k

/-- Actual derived cohomology maps surjectively to the original units. -/
theorem actualDerivedNorm_surjective : Function.Surjective (actualDerivedNorm k) :=
  motivicNorm_surjective k

open Lean in
run_cmd do
  for name in #[``liftedRawNorm, ``liftedRawNorm_boundary, ``homologyNormHom,
      ``homologyNorm, ``homologyNorm_class, ``isZero_raw_X_two, ``raw_outgoing_d_zero,
      ``rawClass, ``homologyNorm_rawClass, ``graphUnitClass, ``homologyNorm_graphUnitClass,
      ``homologyNorm_surjective, ``motivicNorm, ``motivicNorm_surjective,
      ``class_formula, ``signed_graph_formula, ``arbitrary_field_surjective,
      ``actualDerivedNorm, ``actualDerivedNorm_surjective] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual weight-one homology and derived norms use only standard foundations."

end MotivicTest.WeightOneHomologyNorm
