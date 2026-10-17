/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Noetherian sources of finite-type morphisms

A quasi-compact locally finite-type morphism with Noetherian target has a
Noetherian source. This assembles the actual local ring and compactness results,
so downstream cycle constructions need not assume Noetherianity separately for
finite-type schemes over a field or finite covers of such schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

variable {X Y : Scheme.{u}}

/-- Finite-type schemes over a Noetherian base are Noetherian. -/
theorem isNoetherian_of_finiteType (f : X ⟶ Y) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsNoetherian Y] : IsNoetherian X where
  toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian f
  toCompactSpace := QuasiCompact.compactSpace_of_compactSpace f

end Motivic
