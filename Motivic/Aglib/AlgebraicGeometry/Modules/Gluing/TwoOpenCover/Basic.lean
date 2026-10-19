/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Restriction.Open.PushforwardRestriction
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.Algebra.Category.Grp.Limits

/-!
# Two-open gluing of actual structure-sheaf modules

An isomorphism of the two restricted modules on their actual Cartesian
overlap gives a genuine module sheaf, constructed as a pullback of open
pushforwards. Both actual restriction projections are isomorphisms. The
constructor takes legitimate local descent data, not a presumed global
coefficient sheaf or its desired comparison.
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

/-- The overlap module pushed into the first open. -/
abbrev overlapModule := (pushforward a).obj ((restrictFunctor a).obj M)

/-- The genuine first open restriction unit, pushed into the ambient scheme. -/
def leftOverlapMap :
    (pushforward f).obj M ⟶ (pushforward f).obj (overlapModule (a := a) M) :=
  (pushforward f).map ((restrictAdjunction a).unit.app M)

/-- The second module on the first open, identified with the specified
first overlap module by actual open base change and the transition. -/
def overlapComparison :
    (restrictFunctor f).obj ((pushforward g).obj N) ≅ overlapModule (a := a) M :=
  pushforwardRestrictIso sq N ≪≫ (pushforward a).mapIso e.symm

/-- The second overlap map is the adjunct of the constructed local comparison. -/
def rightOverlapMap :
    (pushforward g).obj N ⟶ (pushforward f).obj (overlapModule (a := a) M) :=
  (restrictAdjunction f).homEquiv _ _ (overlapComparison sq M N e).hom

/-- A genuine module sheaf obtained as the compatible pullback of the two
actual open pushforwards. -/
def glued : X.Modules :=
  CategoryTheory.Limits.pullback
    (leftOverlapMap (a := a) (f := f) M) (rightOverlapMap sq M N e)

/-- The actual first compatible projection. -/
def gluedFst : glued sq M N e ⟶ (pushforward f).obj M := pullback.fst _ _

/-- The actual second compatible projection. -/
def gluedSnd : glued sq M N e ⟶ (pushforward g).obj N := pullback.snd _ _

/-- Both actual projections satisfy the prescribed overlap compatibility. -/
@[reassoc] theorem glued_condition :
    gluedFst sq M N e ≫ leftOverlapMap (a := a) (f := f) M =
      gluedSnd sq M N e ≫ rightOverlapMap sq M N e := pullback.condition

set_option backward.isDefEq.respectTransparency false in
/-- Open restriction preserves actual finite limits of module sheaves. -/
instance restrict_preservesFiniteLimits : PreservesFiniteLimits (restrictFunctor f) := by
  let : ReflectsFiniteLimits (toPresheaf U) :=
    reflectsFiniteLimits_of_reflectsIsomorphisms (toPresheaf U)
  have : PreservesFiniteLimits (restrictFunctor f ⋙ toPresheaf U) := by
    change PreservesFiniteLimits (toPresheaf X ⋙
      (Functor.whiskeringLeft _ _ _).obj f.opensFunctor.op)
    have : PreservesFiniteLimits (toPresheaf X) := inferInstance
    have : PreservesFiniteLimits
        ((Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj f.opensFunctor.op) :=
      inferInstance
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves (restrictFunctor f) (toPresheaf U)

set_option backward.isDefEq.respectTransparency false in
/-- The second overlap map becomes an isomorphism on the first open by the
actual restriction adjunction, not by a local-isomorphism hypothesis. -/
theorem isIso_restrict_rightOverlapMap :
    IsIso ((restrictFunctor f).map (rightOverlapMap sq M N e)) := by
  have he : (restrictFunctor f).map (rightOverlapMap sq M N e) ≫
      (restrictAdjunction f).counit.app (overlapModule (a := a) M) =
        (overlapComparison sq M N e).hom := by
    exact ((restrictAdjunction f).homEquiv _ _).symm_apply_apply _
  have : IsIso ((restrictFunctor f).map (rightOverlapMap sq M N e) ≫
      (restrictAdjunction f).counit.app (overlapModule (a := a) M)) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((restrictAdjunction f).counit.app (overlapModule (a := a) M))

include sq in
omit [IsOpenImmersion b] [IsOpenImmersion f] in
set_option backward.isDefEq.respectTransparency false in
/-- The first overlap map becomes an isomorphism on the second open by its
literal section restriction maps. -/
theorem isIso_restrict_leftOverlapMap :
    IsIso ((restrictFunctor g).map (leftOverlapMap (a := a) (f := f) M)) :=
  isIso_restrict_pushforward_unit sq M

set_option backward.isDefEq.respectTransparency false in
/-- The actual first projection is invertible after restricting to its open. -/
theorem isIso_restrict_gluedFst :
    IsIso ((restrictFunctor f).map (gluedFst sq M N e)) := by
  have := isIso_restrict_rightOverlapMap sq M N e
  exact ((IsPullback.of_hasPullback (leftOverlapMap (a := a) (f := f) M)
    (rightOverlapMap sq M N e)).map (restrictFunctor f)).isIso_fst_of_isIso

set_option backward.isDefEq.respectTransparency false in
/-- The actual second projection is invertible after restricting to its open. -/
theorem isIso_restrict_gluedSnd :
    IsIso ((restrictFunctor g).map (gluedSnd sq M N e)) := by
  have := isIso_restrict_leftOverlapMap sq M
  exact ((IsPullback.of_hasPullback (leftOverlapMap (a := a) (f := f) M)
    (rightOverlapMap sq M N e)).map (restrictFunctor g)).isIso_snd_of_isIso

/-- The constructed module sheaf restricts to the actual first local module. -/
def gluedRestrictLeftIso : (restrictFunctor f).obj (glued sq M N e) ≅ M := by
  letI := isIso_restrict_gluedFst sq M N e
  exact asIso ((restrictFunctor f).map (gluedFst sq M N e)) ≪≫
    (restrictFunctorAdjCounitIso f).app M

/-- The constructed module sheaf restricts to the actual second local module. -/
def gluedRestrictRightIso : (restrictFunctor g).obj (glued sq M N e) ≅ N := by
  letI := isIso_restrict_gluedSnd sq M N e
  exact asIso ((restrictFunctor g).map (gluedSnd sq M N e)) ≪≫
    (restrictFunctorAdjCounitIso g).app N

/-- Refining the first open retains the actual local module through the
original composite open immersion. -/
def gluedRestrictLeftRefinementIso {W : Scheme.{u}} (h : W ⟶ U) [IsOpenImmersion h] :
    (restrictFunctor (h ≫ f)).obj (glued sq M N e) ≅ (restrictFunctor h).obj M :=
  (restrictFunctorComp h f).app _ ≪≫
    (restrictFunctor h).mapIso (gluedRestrictLeftIso sq M N e)

/-- Refining the second open retains its literal restriction as well. -/
def gluedRestrictRightRefinementIso {W : Scheme.{u}} (h : W ⟶ V) [IsOpenImmersion h] :
    (restrictFunctor (h ≫ g)).obj (glued sq M N e) ≅ (restrictFunctor h).obj N :=
  (restrictFunctorComp h g).app _ ≪≫
    (restrictFunctor h).mapIso (gluedRestrictRightIso sq M N e)

/-- Every actually compatible pair of ambient maps has a canonical map to
the constructed module sheaf. -/
def gluedLift (L : X.Modules) (l : L ⟶ (pushforward f).obj M)
    (r : L ⟶ (pushforward g).obj N)
    (h : l ≫ leftOverlapMap (a := a) (f := f) M = r ≫ rightOverlapMap sq M N e) :
    L ⟶ glued sq M N e := pullback.lift l r h

/-- The first projection of the universal compatible map is the original map. -/
@[reassoc (attr := simp)] theorem gluedLift_fst (L : X.Modules)
    (l : L ⟶ (pushforward f).obj M) (r : L ⟶ (pushforward g).obj N)
    (h : l ≫ leftOverlapMap (a := a) (f := f) M = r ≫ rightOverlapMap sq M N e) :
    gluedLift sq M N e L l r h ≫ gluedFst sq M N e = l := pullback.lift_fst _ _ _

/-- The second projection of the universal compatible map is the original map. -/
@[reassoc (attr := simp)] theorem gluedLift_snd (L : X.Modules)
    (l : L ⟶ (pushforward f).obj M) (r : L ⟶ (pushforward g).obj N)
    (h : l ≫ leftOverlapMap (a := a) (f := f) M = r ≫ rightOverlapMap sq M N e) :
    gluedLift sq M N e L l r h ≫ gluedSnd sq M N e = r := pullback.lift_snd _ _ _

/-- Maps into the constructed module sheaf are determined by their actual
local pushforward projections. -/
theorem glued_hom_ext {L : X.Modules} {l r : L ⟶ glued sq M N e}
    (h₁ : l ≫ gluedFst sq M N e = r ≫ gluedFst sq M N e)
    (h₂ : l ≫ gluedSnd sq M N e = r ≫ gluedSnd sq M N e) : l = r :=
  pullback.hom_ext h₁ h₂

end AlgebraicGeometry.Scheme.Modules.Gluing.TwoOpenCover
