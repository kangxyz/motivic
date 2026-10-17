/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ComponentIdentityUnits
public import Motivic.AlgebraicGeometry.Correspondences.IncidenceTorAssociativity
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The category of actual finite correspondences

The objects of `Cor k` are smooth separated finite-type schemes over an arbitrary
field, wrapped separately from the existing smooth-site category. Its morphisms
are the actual signed finite-correspondence cycles, its identities are the full
componentwise diagonal cycles, and its composition is the incidence Tor pairing.
The established componentwise unit laws and all-signed associativity theorem
supply the category laws. The existing additive groups and biadditivity supply
the preadditive structure. No connectedness or integrality condition is imposed.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic

/-- Smooth separated finite-type objects over `k`, with finite correspondences
as morphisms rather than the morphisms of the smooth site. -/
structure Cor (k : Type u) [Field k] : Type (u + 1) where
  /-- The underlying smooth-site object. -/
  toSmoothSite : SmoothSite (Spec (.of k))

namespace Cor

variable (k : Type u) [Field k]

/-- The category whose composition is the actual incidence Tor pairing. -/
instance category : Category.{u} (Cor k) where
  Hom X Y := FiniteCorrespondence X.toSmoothSite.hom Y.toSmoothSite.hom
  id X := componentIdentityCycle (X := X.toSmoothSite.left) X.toSmoothSite.hom
  comp {X Y Z} α β := FiniteCorrespondence.incidenceTorPairing k
    (X := X.toSmoothSite) (Y := Y.toSmoothSite) (Z := Z.toSmoothSite) α β
  id_comp {X Y} α := FiniteCorrespondence.incidenceTorPairing_componentIdentity_left k
    (X := X.toSmoothSite) (Y := Y.toSmoothSite) α
  comp_id {X Y} α := FiniteCorrespondence.incidenceTorPairing_componentIdentity_right k
    (X := X.toSmoothSite) (Y := Y.toSmoothSite) α
  assoc {X Y Z W} α β γ := FiniteCorrespondence.incidenceTorPairing_assoc k
    (X := X.toSmoothSite) (Y := Y.toSmoothSite) (Z := Z.toSmoothSite)
    (W := W.toSmoothSite) α β γ

/-- Addition of actual signed cycles makes the correspondence category preadditive. -/
instance preadditive : Preadditive (Cor k) where
  homGroup X Y := inferInstanceAs
    (AddCommGroup (FiniteCorrespondence X.toSmoothSite.hom Y.toSmoothSite.hom))
  add_comp X Y Z α α' β := FiniteCorrespondence.incidenceTorPairing_add_left k
    (X := X.toSmoothSite) (Y := Y.toSmoothSite) (Z := Z.toSmoothSite) α α' β
  comp_add X Y Z α β β' := FiniteCorrespondence.incidenceTorPairing_add_right k
    (X := X.toSmoothSite) (Y := Y.toSmoothSite) (Z := Z.toSmoothSite) α β β'

end Cor

end Motivic
