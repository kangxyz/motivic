/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.StalkModules
public import Motivic.RingTheory.RegularSequence.FlatKernel

/-!
# Literal coefficient scalars and pointed stalk transport

Weak regularity for the actual coefficient stalk module is equivalent to weak
regularity of the literal image list in its ring. Pointed stalk maps compose
with their canonical point identifications, so a commuting diagram of scheme
maps gives the exact scalar compatibility needed to transport that same list.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.Intersection

/-- Coefficient regularity is regularity of the identical list's images under
its actual scalar map, with no change of equations. -/
theorem coefficientStalkModule_isWeaklyRegular_iff
    {D T P : Scheme.{u}} (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T)
    (hp : i d = j t) (s : List (ambientStalk i d)) :
    IsWeaklyRegular (coefficientStalkModule i d j t hp) s ↔
      IsWeaklyRegular (T.presheaf.stalk t)
        (s.map (coefficientStalkMap i d j t hp).hom) := by
  let := (coefficientStalkMap i d j t hp).hom.toAlgebra
  exact (isWeaklyRegular_map_algebraMap_iff (T.presheaf.stalk t)
    (T.presheaf.stalk t) s).symm

end Motivic.Intersection

namespace Motivic.StalkTransport

variable {X Y Z : Scheme.{u}}

/-- The actual stalk map based at a specified equal target point. -/
def pointedMap (f : X ⟶ Y) (x : X) (y : Y) (h : y = f x) :
    Y.presheaf.stalk y ⟶ X.presheaf.stalk x :=
  (Y.presheaf.stalkCongr (.of_eq h)).hom ≫ f.stalkMap x

set_option backward.isDefEq.respectTransparency false in
/-- Actual pointed stalk maps compose, including their equality transports. -/
theorem pointedMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (y : Y) (z : Z)
    (hy : y = f x) (hz : z = g y) :
    pointedMap g y z hz ≫ pointedMap f x y hy =
      pointedMap (f ≫ g) x z (hz.trans (congrArg g hy)) := by
  subst y
  subst z
  simp only [pointedMap, TopCat.Presheaf.stalkCongr_hom]
  change (Z.presheaf.stalkSpecializes (specializes_refl (g (f x))) ≫
      g.stalkMap (f x)) ≫ Y.presheaf.stalkSpecializes (specializes_refl (f x)) ≫
      f.stalkMap x =
    Z.presheaf.stalkSpecializes (specializes_refl (g (f x))) ≫ (f ≫ g).stalkMap x
  simp [Scheme.Hom.stalkMap_comp]

/-- A commuting triangle determines exactly the same pointed scalar map. -/
theorem pointedMap_congr (f g : X ⟶ Y) (hfg : f = g) (x : X) (y : Y)
    (hf : y = f x) (hg : y = g x) :
    pointedMap f x y hf = pointedMap g x y hg := by
  subst g
  rfl

/-- Pointed stalk transport through a scheme isomorphism is a ring isomorphism. -/
instance pointedMap_isIso (f : X ⟶ Y) [IsIso f] (x : X) (y : Y) (h : y = f x) :
    IsIso (pointedMap f x y h) := by
  unfold pointedMap
  infer_instance

/-- An actual isomorphic stalk transport preserves the literal regular image list. -/
theorem isWeaklyRegular_map_pointedMap (f : X ⟶ Y) [IsIso f]
    (x : X) (y : Y) (h : y = f x) {s : List (Y.presheaf.stalk y)}
    (hs : IsWeaklyRegular (Y.presheaf.stalk y) s) :
    IsWeaklyRegular (X.presheaf.stalk x) (s.map (pointedMap f x y h).hom) :=
  RegularSequence.isWeaklyRegular_map_of_flat (pointedMap f x y h).hom
    (RingHom.Flat.of_bijective
      (asIso (pointedMap f x y h)).commRingCatIsoToRingEquiv.bijective) hs

end Motivic.StalkTransport
