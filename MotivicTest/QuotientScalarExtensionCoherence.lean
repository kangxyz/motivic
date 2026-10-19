/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.QuotientScalarExtensionCoherence
public import MotivicTest.TorComparisonFlatBaseChangeComposition

/-!
# Quotient-scalar associator on actual nonzero higher Tor

The source is actual degree-one Tor of the nonradical integer quotient by four.
Both quotient ring maps arise from successive principal localizations, with no
assumed scalar square or annihilation premise.
-/

@[expose] public section

open CategoryTheory

namespace Motivic.MotivicTest.QuotientScalarExtensionCoherence

open TorComparisonFlatBaseChangeComposition
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison

/-- Successive quotient scalar extension is coherent on the genuine supported higher Tor. -/
theorem higherTorAssociator :
    let f := algebraMap ℤ (first (3 : ℤ))
    let g := algebraMap (first (3 : ℤ)) (second (3 : ℤ) 5)
    let I := TorQuotientFiniteness.fourIdeal ⊔ TorQuotientFiniteness.fourIdeal
    let M := (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ TorQuotientFiniteness.Q)).obj
      (ModuleCat.of ℤ TorQuotientFiniteness.Q))
    let hM := quotient_support_le_annihilator TorQuotientFiniteness.fourIdeal
      TorQuotientFiniteness.fourIdeal 1
    let q := supportQuotientMap f I
    let p := supportQuotientMap g (I.map f)
    let hq := Ideal.quotientMap_comp_mk (f := f) (I := I.map f) (J := I) Ideal.le_comap_map
    let hp := Ideal.quotientMap_comp_mk (f := g) (I := (I.map f).map g)
      (J := I.map f) Ideal.le_comap_map
    let hN := quotientScalarExtension_support_of_map f I (I.map f) rfl M hM
    let hP := quotientScalarExtension_support_of_map g (I.map f) ((I.map f).map g) rfl
      ((ModuleCat.extendScalars f).obj M) hN
    let hD := quotientScalarExtension_support_of_map (g.comp f) I ((I.map f).map g)
      (quotientImage_comp f g I (I.map f) ((I.map f).map g) rfl rfl) M hM
    ((ModuleCat.extendScalarsComp q p).hom.app (quotientModule I M hM) ≫
        (ModuleCat.extendScalars p).map
          (quotientScalarExtensionIsoOfMap f I (I.map f) rfl q hq M hM).hom ≫
        (quotientScalarExtensionIsoOfMap g (I.map f) ((I.map f).map g) rfl p hp
          ((ModuleCat.extendScalars f).obj M) hN).hom =
      (quotientScalarExtensionIsoOfMap (g.comp f) I ((I.map f).map g)
        (quotientImage_comp f g I (I.map f) ((I.map f).map g) rfl rfl) (p.comp q)
        (quotientScalarSquare_comp f g I (I.map f) ((I.map f).map g) q p hq hp) M hM).hom ≫
      quotientLinearMap ((I.map f).map g) hD hP
        ((ModuleCat.extendScalarsComp f g).hom.app M)) ∧ ¬ Limits.IsZero M := by
  dsimp only
  exact ⟨quotientScalarExtensionIsoOfMap_hom_comp _ _ _ _ _ rfl rfl _ _ _ _ _ _,
    TorQuotientFiniteness.higherTor_nonzero⟩

/-- The same actual nonzero higher Tor tests the quotient-scalar unitor. -/
theorem higherTorUnitor :
    let I := TorQuotientFiniteness.fourIdeal ⊔ TorQuotientFiniteness.fourIdeal
    let M := (((Tor (ModuleCat ℤ) 1).obj (ModuleCat.of ℤ TorQuotientFiniteness.Q)).obj
      (ModuleCat.of ℤ TorQuotientFiniteness.Q))
    let hM := quotient_support_le_annihilator TorQuotientFiniteness.fourIdeal
      TorQuotientFiniteness.fourIdeal 1
    (quotientScalarExtensionIsoOfMap (RingHom.id ℤ) I I (Ideal.map_id I)
      (RingHom.id (ℤ ⧸ I)) rfl M hM).hom ≫
      quotientLinearMap I
        (quotientScalarExtension_support_of_map (RingHom.id ℤ) I I (Ideal.map_id I) M hM)
        hM ((ModuleCat.extendScalarsId ℤ).hom.app M) =
      (ModuleCat.extendScalarsId (ℤ ⧸ I)).hom.app (quotientModule I M hM) :=
  quotientScalarExtensionIsoOfMap_hom_id _ _ _

end Motivic.MotivicTest.QuotientScalarExtensionCoherence
