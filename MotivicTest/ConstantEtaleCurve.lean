/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Constant.EtaleCurve

/-! Actual compactification, smooth retained curve, and original Cartier graph. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.AffineLineEtaleCompactification
universe u
example (k : Type u) [Field k] {Y S : Scheme.{u}} [IsAffine S]
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    (q : S ⟶ Spec (.of k)) :
    IsProper (pullback.fst q (projection k p)) ∧
    IsOpenImmersion (constantInclusion k p q) ∧
    (constantCurve k p q).IsQuasiAffine ∧
    SmoothOfRelativeDimension 1 (pullback.fst q (curveProjection k p)) :=
  ⟨inferInstance, inferInstance, constantCurve_quasiAffine k p q, constantCurve_smooth k p q⟩
example (k : Type u) [Field k] {Y S : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    (r : S ⟶ Y) := actualGraph_idealModule_isLocallyRankOne k p r
#print axioms actualGraph_idealModule_isLocallyRankOne
#print axioms constantCurve_quasiAffine
