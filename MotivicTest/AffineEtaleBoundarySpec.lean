/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.AffineEtaleBoundarySpec

/-! The original affine-line base and full finite boundary are retained. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
example (k : Type u) [Field k] {Z Y : Scheme.{u}}
    (p : Y ⟶ Spec (.of (Polynomial k))) [Etale p] [QuasiCompact p] [IsSeparated p]
    (z : Z ⟶ Spec (.of (Polynomial k))) (s : Z ⟶ Y)
    (hs : IsPullback s (𝟙 Z) p z) (q : Z ⟶ Spec (.of k)) [IsFinite q] :=
  Scheme.exists_noetherian_spec_etale_boundary_refinement p z s hs q
#print axioms AlgebraicGeometry.Scheme.exists_noetherian_spec_etale_boundary_refinement
