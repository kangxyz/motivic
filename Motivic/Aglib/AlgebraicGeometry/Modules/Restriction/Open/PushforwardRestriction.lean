/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Actual open pushforward and restriction

For a Cartesian square of open immersions, restriction of the actual open
pushforward is the pushforward of the actual restriction. The isomorphism is
constructed from restriction-adjunction maps. Its invertibility follows from
the literal equality of the underlying image/preimage opens, with the full
structure-sheaf module action retained.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Gluing.TwoOpenCover

open Scheme.Modules

variable {T U V X : Scheme.{u}} {a : T ⟶ U} {b : T ⟶ V} {f : U ⟶ X} {g : V ⟶ X}
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion f] [IsOpenImmersion g]
  (sq : IsPullback a b f g)

include sq in
omit [IsOpenImmersion g] in
/-- Restricting an open pushforward to the overlap loses no sections on the
other open, because the defining square is actually Cartesian. -/
theorem overlap_open_eq (W : U.Opens) :
    g ⁻¹ᵁ f ''ᵁ (a ''ᵁ a ⁻¹ᵁ W) = g ⁻¹ᵁ f ''ᵁ W := by
  rw [← IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq,
    ← IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq,
    a.preimage_image_eq]

include sq in
omit [IsOpenImmersion g] in
set_option backward.isDefEq.respectTransparency false in
/-- The actual restriction unit is invertible on an open pushforward after
restriction to the other open. This is proved on all actual section maps. -/
theorem isIso_overlap_unit (M : V.Modules) :
    IsIso ((restrictAdjunction a).unit.app ((restrictFunctor f).obj ((pushforward g).obj M))) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [restrictAdjunction_unit_app_app, restrict_map, pushforward_obj_presheaf_map]
  have hi : IsIso ((TopologicalSpace.Opens.map g.base).map
      (f.opensFunctor.map (homOfLE (a.image_preimage_le W)))) :=
    (PartialOrder.isIso_iff_eq _).mpr (overlap_open_eq sq W)
  infer_instance

include sq in
omit [IsOpenImmersion b] [IsOpenImmersion f] in
set_option backward.isDefEq.respectTransparency false in
/-- The first open's restriction unit becomes an isomorphism after actual
pushforward and restriction to the other member of the Cartesian square. -/
theorem isIso_restrict_pushforward_unit (M : U.Modules) :
    IsIso ((restrictFunctor g).map
      ((pushforward f).map ((restrictAdjunction a).unit.app M))) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  change IsIso (((restrictAdjunction a).unit.app M).app (f ⁻¹ᵁ g ''ᵁ W))
  rw [restrictAdjunction_unit_app_app]
  have he : a ''ᵁ a ⁻¹ᵁ (f ⁻¹ᵁ g ''ᵁ W) = f ⁻¹ᵁ g ''ᵁ W := by
    rw [← IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback sq.flip,
      a.preimage_image_eq]
  have hi : IsIso (homOfLE (a.image_preimage_le (f ⁻¹ᵁ g ''ᵁ W))) :=
    (PartialOrder.isIso_iff_eq _).mpr he
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The actual open-square base-change isomorphism, built from the
restriction unit, restriction-composition maps and the actual open counit. -/
def pushforwardRestrictIso (M : V.Modules) :
    (restrictFunctor f).obj ((pushforward g).obj M) ≅
      (pushforward a).obj ((restrictFunctor b).obj M) := by
  letI : IsIso ((restrictAdjunction a).unit.app
    ((restrictFunctor f).obj ((pushforward g).obj M))) := isIso_overlap_unit sq M
  exact asIso ((restrictAdjunction a).unit.app
      ((restrictFunctor f).obj ((pushforward g).obj M))) ≪≫
    (pushforward a).mapIso
      ((restrictFunctorComp a f).symm.app _ ≪≫
        (restrictFunctorCongr sq.w).app _ ≪≫
        (restrictFunctorComp b g).app _ ≪≫
        (restrictFunctor b).mapIso ((restrictFunctorAdjCounitIso g).app M))

end AlgebraicGeometry.Scheme.Modules.Gluing.TwoOpenCover
