/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.LiteralQuotientTorCoherence
public import MotivicTest.TorComparisonFlatBaseChangeComposition

/-!
# Literal quotient Tor coherence on a nonradical higher-Tor example

Both localization maps, all image ideals and the nonzero degree-one Tor are
actual objects. Target coefficients are literal quotients by image ideals.
-/

@[expose] public section

open CategoryTheory

namespace Motivic.MotivicTest.LiteralQuotientTorCoherence

open TorComparisonFlatBaseChangeComposition
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison

/-- The nonradical higher-Tor example obeys the literal-quotient composition equation. -/
theorem higherTorComposition :
    let f := algebraMap ℤ (first (3 : ℤ))
    let g := algebraMap (first (3 : ℤ)) (second (3 : ℤ) 5)
    let I := TorQuotientFiniteness.fourIdeal
    ∃ (hf : f.Flat) (hg : g.Flat),
      ((ModuleCat.extendScalarsComp f g).hom.app
          (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ (ℤ ⧸ I))).obj
            (ModuleCat.of ℤ (ℤ ⧸ I))) ≫
        (ModuleCat.extendScalars g).map (flatBaseChangeLiteralTorIso f hf I I 1).hom ≫
        (flatBaseChangeLiteralTorIso g hg (I.map f) (I.map f) 1).hom ≫
        (mappedQuotientsTorCompIso f g I I 1).hom =
      (flatBaseChangeLiteralTorIso (g.comp f) (hf.comp hg) I I 1).hom) ∧
      ¬ Limits.IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ (ℤ ⧸ I))).obj
        (ModuleCat.of ℤ (ℤ ⧸ I))) := by
  dsimp only
  refine ⟨RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (first (3 : ℤ)) (.powers (3 : ℤ))),
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (second (3 : ℤ) 5)
        (.powers (algebraMap ℤ (first (3 : ℤ)) 5))), ?_,
    TorQuotientFiniteness.higherTor_nonzero⟩
  exact flatBaseChangeLiteralTorIso_hom_comp _ _ _ _ _ _ _

/-- Identity base change returns the actual original nonradical quotient Tor. -/
theorem higherTorIdentity :
    let I := TorQuotientFiniteness.fourIdeal
    (flatBaseChangeLiteralTorIso (RingHom.id ℤ) (RingHom.Flat.id ℤ) I I 1).hom ≫
      (mappedQuotientsTorIdIso I I 1).hom =
    (ModuleCat.extendScalarsId ℤ).hom.app
      (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ (ℤ ⧸ I))).obj
        (ModuleCat.of ℤ (ℤ ⧸ I))) :=
  flatBaseChangeLiteralTorIso_hom_id _ _ _

end Motivic.MotivicTest.LiteralQuotientTorCoherence
