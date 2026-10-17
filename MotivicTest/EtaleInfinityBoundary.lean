/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Normalization.EtaleInfinityBoundary

/-! The actual full boundary is finite, rather than a supplied finite subset. -/
@[expose] public noncomputable section
set_option linter.hashCommand false
open CategoryTheory AlgebraicGeometry TopologicalSpace
attribute [local instance] specializationOrder
universe u

example (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X] [CompactSpace X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] [QuasiCompact f] [IsSeparated f]
    (hcurve : ∀ x : X, x ≠ genericPoint X → Order.coheight x = 1)
    {S : Scheme.{u}} (p : X ⟶ S) [IsProper p] :
    IsFinite (Scheme.EtaleCompactification.infinityInclusion X f ≫
      (Scheme.EtaleCompactification.genericMap X f).fromNormalization ≫ p) :=
  Scheme.EtaleCompactification.finite_infinity_projection X f hcurve p

#print axioms AlgebraicGeometry.Scheme.EtaleCompactification.generic_fibre_mem_inclusion
#print axioms AlgebraicGeometry.Scheme.EtaleCompactification.infinity_avoids_generic
#print axioms AlgebraicGeometry.Scheme.EtaleCompactification.finite_infinity_projection
