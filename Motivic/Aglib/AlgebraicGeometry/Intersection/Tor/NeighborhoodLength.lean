/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.StalkTorTransport
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientLength

/-!
# Tor length under neighborhood restriction
-/

@[expose] public noncomputable section


set_option backward.isDefEq.respectTransparency true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Intersection

/-- Actual intersection Tor length is preserved by commuting open neighborhoods,
using the constructed actual stalk equivalence and its surjectivity. -/
theorem neighborhoodStalkTor_length
    {D T P D' T' P' : Scheme.{u}}
    (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T) (hp : i d = j t)
    (i' : D' ⟶ P') (d' : D') (j' : T' ⟶ P') (t' : T') (hp' : i' d' = j' t')
    (uD : D' ⟶ D) (uT : T' ⟶ T) (uP : P' ⟶ P)
    (hi : uD ≫ i = i' ≫ uP) (hj : uT ≫ j = j' ≫ uP)
    (hd : d = uD d') (ht : t = uT t')
    [IsOpenImmersion uD] [IsOpenImmersion uT] [IsOpenImmersion uP] (n : ℕ) :
    Module.length (ambientStalk i d)
      (((Tor (ModuleCat (ambientStalk i d)) n).obj
        (coefficientStalkModule i d j t hp)).obj (sourceStalkModule i d)) =
    Module.length (ambientStalk i' d')
      (((Tor (ModuleCat (ambientStalk i' d')) n).obj
        (coefficientStalkModule i' d' j' t' hp')).obj (sourceStalkModule i' d')) := by
  let e := neighborhoodStalkTorIso i d j t hp i' d' j' t' hp' uD uT uP hi hj hd ht n
  exact e.toLinearEquiv.length_eq.trans
    (_root_.ModuleCat.length_restrictScalars_of_surjective
      (neighborhoodAmbientStalkEquiv i d i' d' uD uP hi hd).toRingHom
      (neighborhoodAmbientStalkEquiv i d i' d' uD uP hi hd).surjective _)

end AlgebraicGeometry.Scheme.Intersection
