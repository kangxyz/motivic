/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.OpenPushforwardRestriction
public import Motivic.AlgebraicGeometry.Modules.AffineQuasicoherentComplex

/-!
# Actual finite pushforward and whole open-chart restriction

Pushforward along arbitrary vertical morphisms commutes naturally with a
Cartesian open restriction. The actual restriction unit is invertible by the
accepted whole-preimage section argument; composition and the target-open
counit construct the comparison. Its finite-affine specialization uses the
entire inverse image and genuine coordinate morphism, then presents any given
termwise-QC complex and its original pushforward stalks in those coordinates.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FinitePushforwardRestriction

open Scheme.Modules

variable {T X U Y : Scheme.{u}} {a : T ⟶ X} {b : T ⟶ U} {f : X ⟶ Y} {g : U ⟶ Y}
  [IsOpenImmersion a] [IsOpenImmersion g] (sq : IsPullback a b f g)

/-- Actual open base change for arbitrary vertical maps, natural in every
original module sheaf. Only the horizontal maps are open immersions. -/
def openBaseChangeIso :
    pushforward f ⋙ restrictFunctor g ≅ restrictFunctor a ⋙ pushforward b := by
  let F := pushforward f ⋙ restrictFunctor g
  let α := Functor.whiskerRight (restrictAdjunction a).unit F
  have (M : X.Modules) : IsIso (α.app M) :=
    OpenModuleGluing.isIso_restrict_pushforward_unit sq M
  have : IsIso α := NatIso.isIso_of_isIso_app α
  exact (Functor.leftUnitor F).symm ≪≫ asIso α ≪≫
    Functor.associator (restrictFunctor a) (pushforward a) F ≪≫
    Functor.isoWhiskerLeft (restrictFunctor a)
      ((Functor.associator (pushforward a) (pushforward f) (restrictFunctor g)).symm ≪≫
        Functor.isoWhiskerRight (pushforwardComp a f) (restrictFunctor g) ≪≫
        Functor.isoWhiskerRight (pushforwardCongr sq.w) (restrictFunctor g) ≪≫
        Functor.isoWhiskerRight (pushforwardComp b g).symm (restrictFunctor g) ≪≫
        Functor.associator (pushforward b) (pushforward g) (restrictFunctor g) ≪≫
        Functor.isoWhiskerLeft (pushforward b) (restrictFunctorAdjCounitIso g) ≪≫
        Functor.rightUnitor (pushforward b))

/-- Every original sheaf-module morphism satisfies the actual base-change square. -/
@[reassoc] theorem openBaseChangeIso_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (pushforward f ⋙ restrictFunctor g).map φ ≫ (openBaseChangeIso sq).hom.app N =
      (openBaseChangeIso sq).hom.app M ≫ (restrictFunctor a ⋙ pushforward b).map φ :=
  (openBaseChangeIso sq).hom.naturality φ

/-- Open base change preserves arbitrary original complexes and their differentials. -/
def openBaseChangeComplexIso {ι : Type*} (c : ComplexShape ι) :
    (pushforward f ⋙ restrictFunctor g).mapHomologicalComplex c ≅
      (restrictFunctor a ⋙ pushforward b).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (openBaseChangeIso sq) c

/-- Every degree is the actual natural module-sheaf comparison. -/
theorem openBaseChangeComplexIso_hom_f {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex X.Modules c) (n : ι) :
    ((openBaseChangeComplexIso sq c).app K).hom.f n =
      (openBaseChangeIso sq).hom.app (K.X n) := rfl

/-- The actual original differential square for finite-vertical open base change. -/
theorem openBaseChangeComplexIso_hom_comm {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex X.Modules c) (n m : ι) :
    (((pushforward f ⋙ restrictFunctor g).mapHomologicalComplex c).obj K).d n m ≫
        ((openBaseChangeComplexIso sq c).app K).hom.f m =
      ((openBaseChangeComplexIso sq c).app K).hom.f n ≫
        (((restrictFunctor a ⋙ pushforward b).mapHomologicalComplex c).obj K).d n m :=
  (((openBaseChangeComplexIso sq c).app K).hom.comm n m).symm

open FiniteAffineChart AffineQuasicoherent ModuleStalk

variable (f : X ⟶ Y) [IsFinite f] {V : Y.Opens} (hV : IsAffineOpen V)

/-- The actual whole affine coordinate chart square is genuinely Cartesian. -/
theorem wholeChartIsPullback :
    IsPullback (sourceChart f hV) (coordinateMap f) f hV.fromSpec :=
  (IsOpenImmersion.isPullback (coordinateMap f) (sourceChart f hV) hV.fromSpec f
    (chart_square f hV).symm (by simp [sourceChart])).flip

/-- The actual original finite pushforward restricts to the pushforward of the
whole source chart, with the literal coordinate morphism. -/
def wholeChartPushforwardIso :
    pushforward f ⋙ restrictFunctor hV.fromSpec ≅
      restrictFunctor (sourceChart f hV) ⋙ pushforward (coordinateMap f) :=
  openBaseChangeIso (wholeChartIsPullback f hV)

/-- The whole finite affine comparison retains the original complex. -/
def wholeChartPushforwardComplexIso {ι : Type*} (c : ComplexShape ι) :
    (pushforward f ⋙ restrictFunctor hV.fromSpec).mapHomologicalComplex c ≅
      (restrictFunctor (sourceChart f hV) ⋙
        pushforward (coordinateMap f)).mapHomologicalComplex c :=
  NatIso.mapHomologicalComplex (wholeChartPushforwardIso f hV) c

/-- The constructed coordinate complex of a given QC sheaf complex gives its
actual original finite pushforward on the entire target affine chart. -/
def wholeChartCoordinatePushforwardIso {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex X.Modules c) [∀ n, (K.X n).IsQuasicoherent] :
    ((tilde.functor Γ(X, f ⁻¹ᵁ V) ⋙
        pushforward (coordinateMap f)).mapHomologicalComplex c).obj
        (wholeChartCoordinateComplex c f hV K) ≅
      ((pushforward f ⋙ restrictFunctor hV.fromSpec).mapHomologicalComplex c).obj K :=
  ((pushforward (coordinateMap f)).mapHomologicalComplex c).mapIso
      (wholeChartTildeIso c f hV K) ≪≫
    ((wholeChartPushforwardComplexIso f hV c).app K).symm

/-- The actual target stalk of the global finite pushforward is recovered
from the constructed whole-chart coordinate complex with its canonical action. -/
def wholeChartPushforwardStalkIso {ι : Type*} (c : ComplexShape ι)
    (K : HomologicalComplex X.Modules c) [∀ n, (K.X n).IsQuasicoherent]
    (p : Spec Γ(Y, V)) :
    ((tilde.functor Γ(X, f ⁻¹ᵁ V) ⋙ pushforward (coordinateMap f) ⋙
        functor p).mapHomologicalComplex c).obj (wholeChartCoordinateComplex c f hV K) ≅
      ((pushforward f ⋙ functor (hV.fromSpec p) ⋙ ModuleCat.restrictScalars
        (inv (hV.fromSpec.stalkMap p)).hom).mapHomologicalComplex c).obj K :=
  ((functor p).mapHomologicalComplex c).mapIso
      (wholeChartCoordinatePushforwardIso f hV c K) ≪≫
    (openRestrictionComplexIso hV.fromSpec p c).app
      ((pushforward f).mapHomologicalComplex c |>.obj K)

end Motivic.FinitePushforwardRestriction
