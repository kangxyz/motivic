/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Finite.OpenRestriction
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Finite.Euler

/-!
# Euler lengths of genuine global finite pushforward stalks

A given termwise-quasi-coherent complex is represented on the whole affine
inverse image. Its original global pushforward and source stalk complexes
retain their canonical structure-stalk actions. Finite homology is required
only after localization to the whole finite algebra at the target point.
The actual first-stage correspondence coefficient must still be constructed
before this reusable theorem can be applied to it.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler
open _root_.AlgebraicGeometry.Scheme.Hom

open _root_.AlgebraicGeometry.Scheme.Hom.FiniteAffineChart
open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine
open _root_.AlgebraicGeometry.Scheme.Modules.Stalk
open _root_.HomologicalComplex.ModuleLengthEuler

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U) (p : Spec Γ(Y, U))

/-- The coordinate algebra is the actual finite-map homomorphism on sections. -/
local instance coordinateAlgebra : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

include hU in
/-- The whole affine inverse-image coordinate algebra is finite. -/
theorem coordinateFinite : Module.Finite Γ(Y, U) Γ(X, f ⁻¹ᵁ U) := by
  exact f.finite_app U hU

/-- The original coordinate complex on the entire affine inverse image. -/
abbrev originalCoordinateComplex (K : ChainComplex X.Modules ℕ) :=
  wholeChartCoordinateComplex (ComplexShape.down ℕ) f hU K

/-- Localization is at the whole finite algebra, before choosing any source point. -/
abbrev originalWholeLocalizedComplex (K : ChainComplex X.Modules ℕ) :=
  FiniteFiber.wholeCoefficientComplex Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p
    (originalCoordinateComplex f hU K)

/-- The actual original source structure-stalk complex. -/
abbrev originalSourceStalkComplex (K : ChainComplex X.Modules ℕ) (x : X) :=
  ((functor x).mapHomologicalComplex (ComplexShape.down ℕ)).obj K

/-- The actual original global finite pushforward structure-stalk complex. -/
abbrev originalPushforwardStalkComplex (K : ChainComplex X.Modules ℕ) :=
  ((Scheme.Modules.pushforward f ⋙
    functor (hU.fromSpec p)).mapHomologicalComplex (ComplexShape.down ℕ)).obj K

/-- The actual original target stalk is the localization of its chart ring. -/
def targetStalkLocalizationIso :
    Y.presheaf.stalk (hU.fromSpec p) ≅ CommRingCat.of (Localization.AtPrime p.asIdeal) :=
  asIso (hU.fromSpec.stalkMap p) ≪≫ Spec.stalkIso Γ(Y, U) p

private theorem homologyLength_restrict_equiv {R T : Type u} [CommRing R] [CommRing T]
    (e : R ≃+* T) (K : ChainComplex (ModuleCat.{u} T) ℕ) (n : ℕ) :
    Module.length R
        ((((ModuleCat.restrictScalars e.toRingHom).mapHomologicalComplex _).obj K).homology n) =
      Module.length T (K.homology n) :=
  ((K.sc n).mapHomologyIso (ModuleCat.restrictScalars e.toRingHom)).toLinearEquiv.length_eq.trans
    (_root_.ModuleCat.length_restrictScalars_of_surjective e.toRingHom e.surjective _)

variable (K : ChainComplex X.Modules ℕ) [∀ n, (K.X n).IsQuasicoherent]

/-- The chart's actual pushforward homology length equals the original global
pushforward stalk length, through the canonical open-chart scalar map. -/
theorem pushforward_homology_length (n : ℕ) :
    Module.length ((Spec Γ(Y, U)).presheaf.stalk p)
        ((FiniteFiber.actualPushforwardStalkComplex Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p
          (originalCoordinateComplex f hU K)).homology n) =
      Module.length (Y.presheaf.stalk (hU.fromSpec p))
        ((originalPushforwardStalkComplex f hU p K).homology n) :=
  ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (FiniteRestriction.wholeChartPushforwardStalkIso
      f hU _ K p)).toLinearEquiv.length_eq.trans
    (homologyLength_restrict_equiv
      (asIso (hU.fromSpec.stalkMap p)).symm.commRingCatIsoToRingEquiv
      (originalPushforwardStalkComplex f hU p K) n)

/-- Every chart source homology length equals the original source stalk length
through the actual open-chart structure-stalk map. -/
theorem source_homology_length (q : Spec Γ(X, f ⁻¹ᵁ U)) (n : ℕ) :
    Module.length ((Spec Γ(X, f ⁻¹ᵁ U)).presheaf.stalk q)
        ((FiniteFiber.actualSourceStalkComplex Γ(X, f ⁻¹ᵁ U) q
          (originalCoordinateComplex f hU K)).homology n) =
      Module.length (X.presheaf.stalk (sourceChart f hU q))
        ((originalSourceStalkComplex K (sourceChart f hU q)).homology n) :=
  ((HomologicalComplex.homologyFunctor _ _ n).mapIso
    (wholeChartStalkIso _ f hU K q)).toLinearEquiv.length_eq.trans
    (homologyLength_restrict_equiv
      (asIso ((sourceChart f hU).stalkMap q)).symm.commRingCatIsoToRingEquiv
      (originalSourceStalkComplex K (sourceChart f hU q)) n)

private theorem finiteHomology_of_length_eq {R T : Type u} [CommRing R] [CommRing T]
    {K : ChainComplex (ModuleCat.{u} R) ℕ} {L : ChainComplex (ModuleCat.{u} T) ℕ}
    (hK : FiniteHomology K)
    (h : ∀ n, Module.length R (K.homology n) = Module.length T (L.homology n)) :
    FiniteHomology L where
  finite_length n := by rw [← h n]; exact hK.finite_length n
  finite_support := by simpa only [show (fun n => Module.length R (K.homology n)) =
    (fun n => Module.length T (L.homology n)) from funext h] using hK.finite_support

private theorem homologyEuler_eq_of_length_eq {R T : Type u} [CommRing R] [CommRing T]
    {K : ChainComplex (ModuleCat.{u} R) ℕ} {L : ChainComplex (ModuleCat.{u} T) ℕ}
    (h : ∀ n, Module.length R (K.homology n) = Module.length T (L.homology n))
    (sign : ℕ → ℤ) (hK : FiniteHomology K) (hL : FiniteHomology L) :
    homologyEuler K sign hK = homologyEuler L sign hL := by
  unfold homologyEuler signedLengthSum
  apply finsum_congr
  intro n
  simp only [integerLength, h n]

variable [IsNoetherianRing (Y.presheaf.stalk (hU.fromSpec p))]

include hU in
/-- Noetherianity of the actual target stalk supplies the affine-local hypothesis. -/
theorem coordinateLocal_noetherian : IsNoetherianRing (Localization.AtPrime p.asIdeal) :=
  isNoetherianRing_of_ringEquiv (Y.presheaf.stalk (hU.fromSpec p))
    (targetStalkLocalizationIso hU p).commRingCatIsoToRingEquiv

/-- Whole local finite homology implies finite homology of the original global
pushforward stalk, without any separate finite-length term premise. -/
theorem originalPushforward_finiteHomology
    (hK : FiniteHomology (originalWholeLocalizedComplex f hU p K)) :
    FiniteHomology (originalPushforwardStalkComplex f hU p K) := by
  have := coordinateFinite f hU
  have := coordinateLocal_noetherian hU p
  exact finiteHomology_of_length_eq
    (FiniteFiber.actualPushforwardStalk_finiteHomology Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p
      (originalCoordinateComplex f hU K) hK)
    (pushforward_homology_length f hU p K)

/-- Whole local finite homology implies finite original source homology at every
coordinate source point over p. -/
theorem originalChartSource_finiteHomology
    (hK : FiniteHomology (originalWholeLocalizedComplex f hU p K))
    (q : {q : Spec Γ(X, f ⁻¹ᵁ U) // coordinateMap f q = p}) :
    FiniteHomology (originalSourceStalkComplex K (sourceChart f hU q.1)) := by
  have := coordinateFinite f hU
  have := coordinateLocal_noetherian hU p
  exact finiteHomology_of_length_eq
    (FiniteFiber.actualFiberStalk_finiteHomology Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p
      (originalCoordinateComplex f hU K) hK q)
    (source_homology_length f hU K q.1)

/-- Every original source point above the target has finite stalk homology,
derived using the whole-fiber equivalence and no separate source finiteness premise. -/
theorem originalFiber_finiteHomology
    (hK : FiniteHomology (originalWholeLocalizedComplex f hU p K))
    (x : {x : X // f x = hU.fromSpec p}) :
    FiniteHomology (originalSourceStalkComplex K x.1) := by
  have hx : sourceChart f hU ((fiberEquiv f hU p).symm x).1 = x.1 :=
    congrArg Subtype.val ((fiberEquiv f hU p).apply_symm_apply x)
  have h := originalChartSource_finiteHomology f hU p K hK ((fiberEquiv f hU p).symm x)
  exact (congrArg (fun z : X => FiniteHomology (originalSourceStalkComplex K z)) hx).mp h

/-- The original global finite-pushforward Euler identity over the entire actual
source fiber, with literal scheme residue degrees. Only homology over the whole
localized coordinate algebra is assumed finite. -/
theorem originalFinitePushforwardEuler (sign : ℕ → ℤ)
    (hK : FiniteHomology (originalWholeLocalizedComplex f hU p K)) :
    homologyEuler (originalPushforwardStalkComplex f hU p K) sign
        (originalPushforward_finiteHomology f hU p K hK) =
      ∑ᶠ x : {x : X // f x = hU.fromSpec p}, (f.residueDegree x.1 : ℤ) *
        homologyEuler (originalSourceStalkComplex K x.1) sign
          (originalFiber_finiteHomology f hU p K hK x) := by
  have := coordinateFinite f hU
  have := coordinateLocal_noetherian hU p
  let L := originalCoordinateComplex f hU K
  have hL := FiniteFiber.actualPushforwardStalk_finiteHomology
    Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p L hK
  have hq := FiniteFiber.actualFiberStalk_finiteHomology
    Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p L hK
  calc
    _ = homologyEuler
        (FiniteFiber.actualPushforwardStalkComplex Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p L) sign hL :=
      (homologyEuler_eq_of_length_eq (pushforward_homology_length f hU p K) sign _ _).symm
    _ = ∑ᶠ q : {q : Spec Γ(X, f ⁻¹ᵁ U) // coordinateMap f q = p},
        ((coordinateMap f).residueDegree q.1 : ℤ) *
        homologyEuler (FiniteFiber.actualSourceStalkComplex Γ(X, f ⁻¹ᵁ U) q.1 L)
          sign (hq q) :=
      FiniteFiber.actualFinitePushforwardEuler Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p L sign hK
    _ = ∑ᶠ q : {q : Spec Γ(X, f ⁻¹ᵁ U) // coordinateMap f q = p},
        (f.residueDegree (fiberEquiv f hU p q).1 : ℤ) *
        homologyEuler (originalSourceStalkComplex K (fiberEquiv f hU p q).1) sign
          (originalFiber_finiteHomology f hU p K hK (fiberEquiv f hU p q)) := by
      apply finsum_congr
      intro q
      rw [residueDegree_eq f hU q.1]
      congr 1
      exact homologyEuler_eq_of_length_eq (source_homology_length f hU K q.1) sign _ _
    _ = _ := finsum_comp_equiv (fiberEquiv f hU p)
      (f := fun x => (f.residueDegree x.1 : ℤ) *
        homologyEuler (originalSourceStalkComplex K x.1) sign
          (originalFiber_finiteHomology f hU p K hK x))

/-- The alternating specialization for the original global finite pushforward. -/
theorem originalFinitePushforwardChainEuler
    (hK : FiniteHomology (originalWholeLocalizedComplex f hU p K)) :
    chainEuler (originalPushforwardStalkComplex f hU p K)
        (originalPushforward_finiteHomology f hU p K hK) =
      ∑ᶠ x : {x : X // f x = hU.fromSpec p}, (f.residueDegree x.1 : ℤ) *
        chainEuler (originalSourceStalkComplex K x.1)
          (originalFiber_finiteHomology f hU p K hK x) :=
  originalFinitePushforwardEuler f hU p K (fun n => (-1) ^ n) hK

end AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler
