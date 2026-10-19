/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.TorSupportRestrictionCoherence
public import MotivicTest.TorComparisonFlatBaseChangeComposition

/-!
# Canonical supported Tor restrictions under successive principal localizations

The modules, support quotients, localization maps and higher-Tor nonvanishing
are actual objects and proved properties, with no abstract cocycle assumption.
-/

@[expose] public section

open CategoryTheory

namespace Motivic.MotivicTest.TorSupportRestrictionCoherence

open TorComparisonFlatBaseChangeComposition
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison

/-- Actual supported degree-one Tor obeys two successive principal restrictions. -/
theorem higherTorSupportComposition :
    let f := algebraMap ℤ (first (3 : ℤ))
    let g := algebraMap (first (3 : ℤ)) (second (3 : ℤ) 5)
    let I := TorQuotientFiniteness.fourIdeal
    ∃ (hf : f.Flat) (hg : g.Flat),
      ((ModuleCat.extendScalarsComp (supportQuotientMapSup f I I)
          (supportQuotientMapSup g (I.map f) (I.map f))).hom.app (torSupportModule I I 1) ≫
        (ModuleCat.extendScalars (supportQuotientMapSup g (I.map f) (I.map f))).map
          (torSupportBaseChangeIso f hf I I 1).hom ≫
        (torSupportBaseChangeIso g hg (I.map f) (I.map f) 1).hom ≫
        (torSupportCompositeTargetIso f g I I 1).hom =
      (torSupportDirectCompositeIso f g hf hg I I 1).hom) ∧
      ¬ Limits.IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ (ℤ ⧸ I))).obj
        (ModuleCat.of ℤ (ℤ ⧸ I))) := by
  dsimp only
  refine ⟨RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (first (3 : ℤ)) (.powers (3 : ℤ))),
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (second (3 : ℤ) 5)
        (.powers (algebraMap ℤ (first (3 : ℤ)) 5))), ?_,
    TorQuotientFiniteness.higherTor_nonzero⟩
  exact torSupportBaseChangeIso_hom_comp _ _ _ _ _ _ _

/-- The canonical supported degree-one restriction also obeys the genuine unit law. -/
theorem higherTorSupportIdentity :
    let I := TorQuotientFiniteness.fourIdeal
    (torSupportBaseChangeIso (RingHom.id ℤ) (RingHom.Flat.id ℤ) I I 1).hom ≫
      (torSupportIdentityTargetIso I I 1).hom = (torSupportUnitIso I I 1).hom :=
  torSupportBaseChangeIso_hom_id _ _ _

/-- The comparison's direct target is the literal supported Tor along the actual ring associator. -/
noncomputable def higherTorSupportDirectTarget :
    let f := algebraMap ℤ (first (3 : ℤ))
    let g := algebraMap (first (3 : ℤ)) (second (3 : ℤ) 5)
    let I := TorQuotientFiniteness.fourIdeal
    torSupportCompositeTarget f g I I 1 ≅
      (ModuleCat.restrictScalars (torSupportCompositeRingIso f g I I).toRingHom).obj
        (torSupportModule (I.map (g.comp f)) (I.map (g.comp f)) 1) :=
  torSupportCompositeTargetRestrictIso _ _ _ _ _

end Motivic.MotivicTest.TorSupportRestrictionCoherence
