/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.AffineIncidenceComparison
public import Motivic.Algebra.Homology.TorComparison.Balanced

/-!
# Actual intersection Tor at a specified common point

Both scalar actions are the literal pointed stalk maps at the same ambient
point. Reanchoring uses equality transport only; commuting open neighborhoods
use the existing actual stalk Tor comparison. The factor swap is the proved
balanced Tor isomorphism, not an implicit convention change.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.Intersection

variable {D T P : Scheme.{u}} (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T)
  (p : P) (hi : p = i d) (hj : p = j t)

/-- Actual categorical Tor with both original scalar actions based at the
specified common ambient point; the coefficient remains the first argument. -/
abbrev pointedStalkTor (n : ℕ) : ModuleCat (P.presheaf.stalk p) :=
  ((Tor (ModuleCat (P.presheaf.stalk p)) n).obj
    ((ModuleCat.restrictScalars (StalkTransport.pointedMap j t p hj).hom).obj
      (ModuleCat.of (T.presheaf.stalk t) (T.presheaf.stalk t)))).obj
    ((ModuleCat.restrictScalars (StalkTransport.pointedMap i d p hi).hom).obj
      (ModuleCat.of (D.presheaf.stalk d) (D.presheaf.stalk d)))

/-- Reanchoring the same two actions at the first support image changes no length. -/
theorem pointedStalkTor_length (n : ℕ) :
    Module.length (P.presheaf.stalk p) (pointedStalkTor i d j t p hi hj n) =
      Module.length (ambientStalk i d)
        (((Tor (ModuleCat (ambientStalk i d)) n).obj
          (coefficientStalkModule i d j t (hi.symm.trans hj))).obj (sourceStalkModule i d)) := by
  subst p
  unfold pointedStalkTor
  rw [StalkTransport.pointedMap_image]
  rfl

/-- Swapping the original factors uses the genuine all-degree Tor balance isomorphism. -/
theorem pointedStalkTor_balance_length (n : ℕ) :
    Module.length (P.presheaf.stalk p) (pointedStalkTor i d j t p hi hj n) =
      Module.length (P.presheaf.stalk p) (pointedStalkTor j t i d p hj hi n) :=
  (TorComparison.torBalanceIso _ _ n).toLinearEquiv.length_eq

/-- Commuting actual open neighborhoods transport both specified-point scalar
maps. Scheme isomorphisms are included, and no scalar square is assumed separately. -/
theorem pointedStalkTor_neighborhood_length
    {D' T' P' : Scheme.{u}}
    (i' : D' ⟶ P') (d' : D') (j' : T' ⟶ P') (t' : T')
    (p' : P') (hi' : p' = i' d') (hj' : p' = j' t')
    (uD : D' ⟶ D) (uT : T' ⟶ T) (uP : P' ⟶ P)
    (hD : uD ≫ i = i' ≫ uP) (hT : uT ≫ j = j' ≫ uP)
    (hd : d = uD d') (ht : t = uT t')
    [IsOpenImmersion uD] [IsOpenImmersion uT] [IsOpenImmersion uP] (n : ℕ) :
    Module.length (P.presheaf.stalk p) (pointedStalkTor i d j t p hi hj n) =
      Module.length (P'.presheaf.stalk p')
        (pointedStalkTor i' d' j' t' p' hi' hj' n) := by
  rw [pointedStalkTor_length, pointedStalkTor_length]
  exact neighborhoodStalkTor_length i d j t (hi.symm.trans hj)
    i' d' j' t' (hi'.symm.trans hj') uD uT uP hD hT hd ht n

end Motivic.Intersection
