/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.TorSupportRestrictionTransport
public import MotivicTest.TorSupportRestrictionCoherence

/-!
# Direct supported Tor comparison under genuine source transport

The nonradical integer quotient in degree one tests the exact existing direct
supported Tor transition, under successive principal localizations and actual
support-ring source and target transport.
-/

@[expose] public section

open CategoryTheory

namespace Motivic.MotivicTest.TorSupportRestrictionTransport

open TorComparisonFlatBaseChangeComposition
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison

/-- Two actual higher-Tor restrictions agree with the existing direct supported transition. -/
theorem higherTorDirectComposition :
    let f := algebraMap ℤ (first (3 : ℤ))
    let g := algebraMap (first (3 : ℤ)) (second (3 : ℤ) 5)
    let I := TorQuotientFiniteness.fourIdeal
    ∃ (hf : f.Flat) (hg : g.Flat),
      ((ModuleCat.extendScalarsComp (supportQuotientMapSup f I I)
          (supportQuotientMapSup g (I.map f) (I.map f))).hom.app (torSupportModule I I 1) ≫
        (ModuleCat.extendScalars (supportQuotientMapSup g (I.map f) (I.map f))).map
          (torSupportBaseChangeIso f hf I I 1).hom ≫
        (torSupportBaseChangeIso g hg (I.map f) (I.map f) 1).hom ≫
        (torSupportCompositeTargetIso f g I I 1).hom ≫
        (torSupportCompositeTargetRestrictIso f g I I 1).hom =
      (torSupportCompositeSourceIso f g I I 1).hom ≫
        (ModuleCat.restrictScalars (torSupportCompositeRingIso f g I I).toRingHom).map
          (torSupportBaseChangeIso (g.comp f) (hf.comp hg) I I 1).hom) ∧
      ¬ Limits.IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ (ℤ ⧸ I))).obj
        (ModuleCat.of ℤ (ℤ ⧸ I))) := by
  dsimp only
  refine ⟨RingHom.flat_algebraMap_iff.mpr
    (IsLocalization.flat (first (3 : ℤ)) (.powers (3 : ℤ))),
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (second (3 : ℤ) 5)
        (.powers (algebraMap ℤ (first (3 : ℤ)) 5))), ?_,
    TorQuotientFiniteness.higherTor_nonzero⟩
  exact torSupportBaseChangeIso_hom_comp_transport _ _ _ _ _ _ _

/-- The existing supported identity transition agrees with the literal quotient scalar unitor. -/
theorem higherTorDirectIdentity :
    let I := TorQuotientFiniteness.fourIdeal
    (torSupportBaseChangeIso (RingHom.id ℤ) (RingHom.Flat.id ℤ) I I 1).hom ≫
      (torSupportIdentityTargetIso I I 1).hom ≫
      (torSupportIdentityTargetRestrictIso I I 1).hom =
    (torSupportIdentitySourceIso I I 1).hom ≫
      (ModuleCat.restrictScalars (torSupportIdentityRingIso I I).toRingHom).map
        ((ModuleCat.extendScalarsId (ℤ ⧸ (I ⊔ I))).hom.app (torSupportModule I I 1)) :=
  torSupportBaseChangeIso_hom_id_transport _ _ _

end Motivic.MotivicTest.TorSupportRestrictionTransport
