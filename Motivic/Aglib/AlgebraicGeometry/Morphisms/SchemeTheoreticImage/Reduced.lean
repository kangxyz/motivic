/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Reduced scheme-theoretic images

The scheme-theoretic image of a quasi-compact map from a reduced scheme is
reduced. On every target affine open, the coordinate ring of the image is a
quotient by the kernel of restriction; it injects into the reduced ring of
sections over the source. The proof uses those actual affine charts.

This supplies the reducedness prerequisite for componentwise graph cycles.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}}

/-- A quasi-compact scheme-theoretic image of a reduced scheme is reduced. -/
theorem isReduced_schemeImage (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] :
    IsReduced f.image := by
  have hR : ∀ U : Y.affineOpens, _root_.IsReduced (f.ker.subschemeCover.X U) := fun U => by
    change _root_.IsReduced (Γ(Y, U) ⧸ f.ker.ideal U)
    rw [f.ker_apply U]
    exact isReduced_of_injective (RingHom.kerLift (f.app U.1).hom)
      (RingHom.kerLift_injective (f.app U.1).hom)
  have hS : ∀ U : Y.affineOpens,
      AlgebraicGeometry.IsReduced (f.ker.subschemeCover.openCover.X U) := fun U => by
    change AlgebraicGeometry.IsReduced (Spec (f.ker.subschemeCover.X U))
    have := hR U
    infer_instance
  exact @IsReduced.of_openCover f.image f.ker.subschemeCover.openCover hS

end AlgebraicGeometry.Scheme.Hom
