/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChangeQuotient
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Canonical flat Tor base change with its actual quotient action -/

@[expose] public section

noncomputable section

open CategoryTheory
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison

universe u

namespace Motivic.MotivicTest.TorFlatBaseChangeQuotient

/-- Actual base change along every localization descends to the image support quotient. -/
def localizationQuotientIso {R : Type u} [CommRing R] (p : Submonoid R)
    (J K : Ideal R) (n : ℕ) :=
  flatBaseChangeTorQuotientIso (algebraMap R (Localization p))
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization p) p)) J K n

/-- The quotient-linear localized comparison has exactly the old canonical function. -/
theorem localizationQuotientIso_hom_apply {R : Type u} [CommRing R] (p : Submonoid R)
    (J K : Ideal R) (n : ℕ)
    (x : (ModuleCat.extendScalars (algebraMap R (Localization p))).obj
      (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj
        (ModuleCat.of R (R ⧸ J)))) :
    (localizationQuotientIso p J K n).hom x =
      (flatBaseChangeTorIso (algebraMap R (Localization p))
        (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization p) p))
        (ModuleCat.of R (R ⧸ K)) (ModuleCat.of R (R ⧸ J)) n).hom x := rfl

/-- Localization at three keeps the full nonradical input ideal (4) in this actual
quotient-linear base-change comparison, including degree one. -/
def integerFourLocalization :=
  localizationQuotientIso (Submonoid.powers (3 : ℤ))
    (Ideal.span ({4} : Set ℤ)) (Ideal.span ({4} : Set ℤ)) 1

end Motivic.MotivicTest.TorFlatBaseChangeQuotient
