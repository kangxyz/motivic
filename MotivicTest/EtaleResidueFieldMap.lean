/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Fibers.ResidueFieldMap

/-! # Direct tests for the actual residue-field morphism of an étale map -/

public section

open CategoryTheory AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Etale f] (x : X)

example : IsOpenImmersion (f.asFiberHom x) := inferInstance

example : Etale (Spec.map (f.residueFieldMap x)) := inferInstance

example : IsSeparated (Spec.map (f.residueFieldMap x)) := inferInstance

example : QuasiCompact (Spec.map (f.residueFieldMap x)) := inferInstance
