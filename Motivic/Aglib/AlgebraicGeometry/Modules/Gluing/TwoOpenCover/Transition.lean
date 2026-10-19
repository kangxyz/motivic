/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Gluing.TwoOpenCover.Basic

/-!
# The actual transition of a glued module sheaf

The two constructed local isomorphisms realize the original supplied transition
on the actual Cartesian overlap, with all restriction-composition comparisons.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Gluing.TwoOpenCover

open Scheme.Modules

variable {T U V X : Scheme.{u}} {a : T ⟶ U} {b : T ⟶ V} {f : U ⟶ X} {g : V ⟶ X}
  [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion f] [IsOpenImmersion g]
  (sq : IsPullback a b f g) (M : U.Modules) (N : V.Modules)
  (e : (restrictFunctor a).obj M ≅ (restrictFunctor b).obj N)

set_option backward.isDefEq.respectTransparency false in
/-- The open restriction counit is the actual comparison used by the local inverse. -/
theorem restrictionCounitIso_hom :
    ((restrictFunctorAdjCounitIso f).app M).hom = (restrictAdjunction f).counit.app M := rfl

/-- The actual comparison between the two composite restrictions to the overlap. -/
def overlapRestrictionIso : restrictFunctor f ⋙ restrictFunctor a ≅
    restrictFunctor g ⋙ restrictFunctor b :=
  (restrictFunctorComp a f).symm ≪≫ restrictFunctorCongr sq.w ≪≫ restrictFunctorComp b g

set_option backward.isDefEq.respectTransparency false in
/-- The constructed local comparison is the actual overlap adjunction mate. -/
theorem overlapComparison_hom_eq_mate :
    (overlapComparison sq M N e).hom =
      (restrictAdjunction a).homEquiv _ _
        ((overlapRestrictionIso sq).hom.app ((pushforward g).obj N) ≫
          (restrictFunctor b).map ((restrictAdjunction g).counit.app N) ≫ e.inv) := by
  simp only [overlapComparison, pushforwardRestrictIso, overlapRestrictionIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom,
    NatTrans.comp_app, Adjunction.homEquiv_unit,
    Functor.map_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The local comparison realizes exactly the supplied inverse transition. -/
theorem overlapComparison_mate :
    (restrictFunctor a).map (overlapComparison sq M N e).hom ≫
        (restrictAdjunction a).counit.app ((restrictFunctor a).obj M) =
      (overlapRestrictionIso sq).hom.app ((pushforward g).obj N) ≫
        (restrictFunctor b).map ((restrictAdjunction g).counit.app N) ≫ e.inv := by
  rw [overlapComparison_hom_eq_mate]
  exact ((restrictAdjunction a).homEquiv _ _).symm_apply_apply _

set_option backward.isDefEq.respectTransparency false in
/-- Restricting the pullback compatibility gives its actual first-open adjunction mate. -/
theorem glued_local_condition :
    (gluedRestrictLeftIso sq M N e).hom ≫ (restrictAdjunction a).unit.app M =
      (restrictFunctor f).map (gluedSnd sq M N e) ≫ (overlapComparison sq M N e).hom := by
  have hc := congrArg (fun φ => (restrictFunctor f).map φ ≫
    (restrictAdjunction f).counit.app (overlapModule (a := a) M)) (glued_condition sq M N e)
  simp only [Functor.map_comp, Category.assoc] at hc
  have hr : (restrictFunctor f).map (rightOverlapMap sq M N e) ≫
      (restrictAdjunction f).counit.app (overlapModule (a := a) M) =
        (overlapComparison sq M N e).hom :=
    ((restrictAdjunction f).homEquiv _ _).symm_apply_apply _
  rw [hr] at hc
  change (restrictFunctor f).map (gluedFst sq M N e) ≫
      ((restrictFunctor f).map ((pushforward f).map ((restrictAdjunction a).unit.app M)) ≫
        (restrictAdjunction f).counit.app (overlapModule (a := a) M)) = _ at hc
  have hn := (restrictAdjunction f).counit.naturality ((restrictAdjunction a).unit.app M)
  change (restrictFunctor f).map ((pushforward f).map ((restrictAdjunction a).unit.app M)) ≫
      (restrictAdjunction f).counit.app (overlapModule (a := a) M) =
    (restrictAdjunction f).counit.app M ≫ (restrictAdjunction a).unit.app M at hn
  rw [hn] at hc
  simpa only [gluedRestrictLeftIso, Iso.trans_hom, asIso_hom,
    restrictionCounitIso_hom, Category.assoc] using hc

set_option backward.isDefEq.respectTransparency false in
/-- The two actual local restriction isomorphisms realize the supplied transition,
with the original composition and square-congruence maps on the overlap. -/
theorem glued_transition :
    (restrictFunctor a).map (gluedRestrictLeftIso sq M N e).hom ≫ e.hom =
      (overlapRestrictionIso sq).hom.app (glued sq M N e) ≫
        (restrictFunctor b).map (gluedRestrictRightIso sq M N e).hom := by
  have hc := congrArg (fun φ => (restrictFunctor a).map φ ≫
    (restrictAdjunction a).counit.app ((restrictFunctor a).obj M))
      (glued_local_condition sq M N e)
  simp only [Functor.map_comp, Category.assoc] at hc
  rw [(restrictAdjunction a).left_triangle_components,
    Category.comp_id, overlapComparison_mate] at hc
  have hn := (overlapRestrictionIso sq).hom.naturality (gluedSnd sq M N e)
  change (restrictFunctor a).map ((restrictFunctor f).map (gluedSnd sq M N e)) ≫
      (overlapRestrictionIso sq).hom.app ((pushforward g).obj N) =
    (overlapRestrictionIso sq).hom.app (glued sq M N e) ≫
      (restrictFunctor b).map ((restrictFunctor g).map (gluedSnd sq M N e)) at hn
  rw [← Category.assoc, hn, Category.assoc] at hc
  apply (cancel_mono e.inv).mp
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    gluedRestrictRightIso, Iso.trans_hom, asIso_hom, Functor.map_comp,
    restrictionCounitIso_hom] using hc

end AlgebraicGeometry.Scheme.Modules.Gluing.TwoOpenCover
