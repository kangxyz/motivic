/-
Copyright (c) 2026 Motivic Cohomology contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.ConstantRetainedTarget

/-! The smooth quasi-affine retained curve maps to the original overlap. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.AffineLineEtaleCompactification
universe u
example (k : Type u) [Field k] {Y S : Scheme.{u}} [IsAffine S]
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    (U : (Spec (.of (Polynomial k))).Opens) (q : S ⟶ Spec (.of k)) :
    (constantRetainedTarget k p U q).IsQuasiAffine ∧
      SmoothOfRelativeDimension 1 (pullback.fst q (retainedProjection k p U)) :=
  ⟨constantRetainedTarget_quasiAffine k p U q, constantRetainedTarget_smooth k p U q⟩
#print axioms constantRetainedTarget_quasiAffine
#print axioms range_constantRetainedInclusion_complement
