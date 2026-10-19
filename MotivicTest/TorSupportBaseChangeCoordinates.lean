/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.TorSupportBaseChangeCoordinates
public import MotivicTest.TorSupportBaseChange

/-! # Coordinates of actual nonzero higher-Tor support restriction -/

@[expose] public section

noncomputable section

open CategoryTheory
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison
open scoped TensorProduct ChangeOfRings

namespace Motivic.MotivicTest.TorSupportBaseChangeCoordinates

open TorQuotientFiniteness TorSupportBaseChange

/-- The actual principal-localization ring map used by the higher-Tor consumer. -/
def threeMap : ℤ →+* Localization (Submonoid.powers (3 : ℤ)) := algebraMap _ _

/-- Flatness belongs to the ambient localization map. -/
theorem threeMap_flat : threeMap.Flat :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat _ (Submonoid.powers (3 : ℤ)))

/-- The actual degree-one support transition keeps canonical coordinates after map_sup transport. -/
theorem higherTorRestriction_hom_tmul
    (s : Localization (Submonoid.powers (3 : ℤ))) (m : torSupportModule fourIdeal fourIdeal 1) :
    (torSupportBaseChangeIso threeMap threeMap_flat fourIdeal fourIdeal 1).hom
      (Ideal.Quotient.mk (fourIdeal.map threeMap ⊔ fourIdeal.map threeMap) s
        ⊗ₜ[ℤ ⧸ (fourIdeal ⊔ fourIdeal),supportQuotientMapSup threeMap fourIdeal fourIdeal] m) =
      (extendedQuotientsTorIso threeMap fourIdeal fourIdeal 1).hom
        ((flatBaseChangeTorIso threeMap threeMap_flat (ModuleCat.of ℤ Q)
          (ModuleCat.of ℤ Q) 1).hom (s ⊗ₜ[ℤ,threeMap] m)) :=
  torSupportBaseChangeIso_hom_tmul threeMap threeMap_flat fourIdeal fourIdeal 1 s m

/-- The ideal in the coordinate formula is nonradical. -/
theorem coordinateIdeal_not_radical : ¬ fourIdeal.IsRadical := fourIdeal_not_radical

/-- The actual original degree-one Tor in the coordinate formula is nonzero. -/
theorem coordinateSource_nonzero :
    ¬ Limits.IsZero (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ Q)).obj
      (ModuleCat.of ℤ Q)) := higherTor_nonzero

end Motivic.MotivicTest.TorSupportBaseChangeCoordinates
