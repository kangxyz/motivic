/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.SchemeTheoreticImage.Reduced
public import Mathlib.AlgebraicGeometry.IdealSheaf.IrreducibleComponent

/-!
# Integral components of reduced Noetherian schemes

Mathlib's scheme structure on an irreducible component is the scheme-theoretic
image of the open complement of all the other components. For a reduced
Noetherian scheme this image is reduced, hence integral. No irreducibility
assumption is made on the original scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom

variable (X : Scheme.{u}) (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
  [IsNoetherian X] [IsReduced X]

/-- The actual component scheme of a reduced Noetherian scheme is reduced. -/
instance isReduced_irreducibleComponent : IsReduced (X.irreducibleComponent Z hZ) := by
  unfold Scheme.irreducibleComponent
  rw [Scheme.irreducibleComponentIdeal_def]
  exact isReduced_schemeImage (X.irreducibleComponentOpen Z).ι

/-- Each irreducible component of a reduced Noetherian scheme is integral. -/
instance isIntegral_irreducibleComponent : IsIntegral (X.irreducibleComponent Z hZ) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

omit [IsReduced X] in
/-- The component inclusion has precisely the specified topological image. -/
theorem range_irreducibleComponentι : Set.range (X.irreducibleComponentι Z hZ) = Z := by
  change Set.range (X.irreducibleComponentIdeal Z hZ).subschemeι = Z
  rw [Scheme.IdealSheafData.range_subschemeι]
  rfl

end AlgebraicGeometry.Scheme
