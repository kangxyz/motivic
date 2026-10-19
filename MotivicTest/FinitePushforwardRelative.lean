/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Finite.RelativeKoszul
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Diagonal.IntermediateLists

/-!
# Actual relative-QC finite-pushforward consumers

A module or complex on the entire inverse image is genuinely pushed to the
ambient source. The open adjunction counit proves precisely the required
relative QC, without a global QC assertion. The tests retain the original
source fiber, original differentials, actual image-product map and middle list.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.FinitePushforwardRelative
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent

open Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler
open _root_.HomologicalComplex.ModuleLengthEuler

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U) (p : Spec Γ(Y, U))

/-- A genuine module on the whole inverse image is pushed to the original ambient source. -/
abbrev ambientModule (E : (f ⁻¹ᵁ U).toScheme.Modules) := (pushforward (f ⁻¹ᵁ U).ι).obj E

/-- The actual open adjunction counit proves the required relative quasi-coherence. -/
instance ambientModule_relativeQuasicoherent (E : (f ⁻¹ᵁ U).toScheme.Modules)
    [E.IsQuasicoherent] :
    ((restrictFunctor (f ⁻¹ᵁ U).ι).obj (ambientModule f E)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (f ⁻¹ᵁ U).toScheme.ringCatSheaf).prop_of_iso
    ((restrictFunctorAdjCounitIso (f ⁻¹ᵁ U).ι).app E).symm
      (inferInstanceAs E.IsQuasicoherent)

/-- The genuine whole-open QC proof transfers through the original affine restriction. -/
theorem actualAffineRestriction (E : (f ⁻¹ᵁ U).toScheme.Modules) [E.IsQuasicoherent] :
    ((restrictFunctor (FiniteAffineChart.sourceChart f hU)).obj
      (ambientModule f E)).IsQuasicoherent :=
  RelativeAffine.sourceChart_quasicoherent f hU (ambientModule f E)

/-- The actual whole coefficient is finite from all original source-stalk witnesses,
with the relative QC witness constructed from the genuine open counit. -/
theorem relativeWholeFinite (E : (f ⁻¹ᵁ U).toScheme.Modules) [E.IsQuasicoherent]
    (hE : ∀ x : {x : X // f x = hU.fromSpec p},
      Module.Finite (X.presheaf.stalk x.1) (originalSourceStalkModule (ambientModule f E) x.1)) :
    letI : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
    Module.Finite (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p)
      (originalWholeLocalizedModule f hU p (ambientModule f E)) :=
  RelativeFiniteEuler.originalWholeModule_finite f hU p (ambientModule f E) hE

/-- An empty original fiber kills the actual whole localized module with no finite-rank premise. -/
theorem emptyFiberWholeZero (E : (f ⁻¹ᵁ U).toScheme.Modules) [E.IsQuasicoherent]
    [IsEmpty {x : X // f x = hU.fromSpec p}] :
    Subsingleton (originalWholeLocalizedModule f hU p (ambientModule f E)) :=
  RelativeFiniteEuler.originalWholeModule_subsingleton f hU p (ambientModule f E)
    (fun x => isEmptyElim x)

/-- Whole localized boundedness uses pointwise bounds and the actual relative-QC construction. -/
theorem relativeWholeBound (E : ℕ → (f ⁻¹ᵁ U).toScheme.Modules)
    [∀ n, (E n).IsQuasicoherent]
    (hE : ∀ x : {x : X // f x = hU.fromSpec p}, ∃ b : ℕ, ∀ n, b ≤ n →
      Subsingleton (originalSourceStalkModule (ambientModule f (E n)) x.1)) :
    ∃ b : ℕ, ∀ n, b ≤ n →
      Subsingleton (originalWholeLocalizedModule f hU p (ambientModule f (E n))) :=
  RelativeFiniteEuler.originalWholeFamily_exists_bound f hU p
    (fun n => ambientModule f (E n)) hE

/-- Actual pushforward maps every term and differential of a whole-open complex. -/
abbrev ambientComplex (E : ChainComplex (f ⁻¹ᵁ U).toScheme.Modules ℕ) :=
  ((pushforward (f ⁻¹ᵁ U).ι).mapHomologicalComplex (ComplexShape.down ℕ)).obj E

/-- The termwise open counits prove exactly the relative QC needed by the complex adapter. -/
instance ambientComplex_relativeQuasicoherent
    (E : ChainComplex (f ⁻¹ᵁ U).toScheme.Modules ℕ) [∀ n, (E.X n).IsQuasicoherent]
    (n : ℕ) :
    ((restrictFunctor (f ⁻¹ᵁ U).ι).obj ((ambientComplex f E).X n)).IsQuasicoherent :=
  ambientModule_relativeQuasicoherent f (E.X n)

/-- The actual counit/open-stalk comparison preserves every original differential. -/
theorem relativeOriginalDifferential
    (E : ChainComplex (f ⁻¹ᵁ U).toScheme.Modules ℕ) [∀ n, (E.X n).IsQuasicoherent]
    (q : Spec Γ(X, f ⁻¹ᵁ U)) (n m : ℕ) :
    let K := ambientComplex f E
    let C := ((tilde.functor Γ(X, f ⁻¹ᵁ U) ⋙ Stalk.functor q).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj
        (Affine.wholeChartCoordinateComplex (ComplexShape.down ℕ) f hU K)
    let D := (Functor.mapHomologicalComplex
      (Stalk.functor (FiniteAffineChart.sourceChart f hU q) ⋙
        ModuleCat.restrictScalars (inv ((FiniteAffineChart.sourceChart f hU).stalkMap q)).hom)
      (ComplexShape.down ℕ)).obj K
    let e := RelativeAffine.wholeChartStalkIso f hU (ComplexShape.down ℕ) K q
    e.hom.f n ≫ D.d n m = C.d n m ≫ e.hom.f m :=
  (RelativeAffine.wholeChartStalkIso f hU (ComplexShape.down ℕ)
    (ambientComplex f E) q).hom.comm n m

/-- The same actual list, whole fiber and literal scheme residue weights work from relative QC. -/
theorem relativeOriginalProjection
    [IsNoetherianRing (Y.presheaf.stalk (hU.fromSpec p))]
    (E : ChainComplex (f ⁻¹ᵁ U).toScheme.Modules ℕ) [∀ n, (E.X n).IsQuasicoherent]
    (s : List (Y.presheaf.stalk (hU.fromSpec p)))
    (hE : FiniteHomology (originalWholeKoszulTotal f hU p (ambientComplex f E) s)) :
    chainEuler (originalPushforwardKoszul f hU p (ambientComplex f E) s)
      (RelativeFiniteEuler.originalPushforwardKoszul_finiteHomology f hU p _ s hE) =
    ∑ᶠ x : {x : X // f x = hU.fromSpec p}, (f.residueDegree x.1 : ℤ) *
      chainEuler (originalFiberKoszul f hU p (ambientComplex f E) s x)
        (RelativeFiniteEuler.originalFiberKoszul_finiteHomology f hU p _ s hE x) :=
  RelativeFiniteEuler.originalFinitePushforwardKoszulEuler f hU p _ s hE

section Correspondence

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated h]
  {V : (F.leftIntermediateImageProduct G H).Opens} (hV : IsAffineOpen V)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
  (K : ChainComplex (F.leftIntermediateSupportProduct G H).Modules ℕ)
  [∀ n, ((restrictFunctor ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V).ι).obj
    (K.X n)).IsQuasicoherent]
  [IsNoetherianRing ((F.leftIntermediateImageProduct G H).presheaf.stalk (hV.fromSpec p))]

/-- The genuine image-product projection accepts QC only on its whole inverse image,
with the original remaining middle list acting through the actual middle-pair stalk map. -/
theorem actualRelativeRemainingProjection
    (s : List ((CategoryTheory.Limits.pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (hV.fromSpec p))))
    (hK : FiniteHomology (originalWholeKoszulTotal (F.leftIntermediateImageMap G H) hV p K
      (s.map ((F.leftImageMiddlePair G H).stalkMap (hV.fromSpec p)).hom))) :
    let t := s.map ((F.leftImageMiddlePair G H).stalkMap (hV.fromSpec p)).hom
    chainEuler (originalPushforwardKoszul (F.leftIntermediateImageMap G H) hV p K t)
      (RelativeFiniteEuler.originalPushforwardKoszul_finiteHomology _ hV p K t hK) =
    ∑ᶠ x : {x : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H x = hV.fromSpec p},
      ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
        chainEuler (originalFiberKoszul (F.leftIntermediateImageMap G H) hV p K t x)
          (RelativeFiniteEuler.originalFiberKoszul_finiteHomology _ hV p K t hK x) :=
  RelativeFiniteEuler.originalFinitePushforwardKoszulEuler _ hV p K _ hK

end Correspondence

end Motivic.MotivicTest.FinitePushforwardRelative
