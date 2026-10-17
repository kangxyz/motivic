/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Modules.TildeOpenBaseChangeCocycle
public import MotivicTest.TildeOpenBaseChangeIdentity

/-! # Successive principal-open tilde restriction on actual nonzero supported higher Tor -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace Motivic.MotivicTest.TildeOpenBaseChangeComposition

open Motivic.TildeOpenBaseChange Motivic.TorComparison TorQuotientFiniteness

local instance {A B C : CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C)
    [IsOpenImmersion (Spec.map φ)] [IsOpenImmersion (Spec.map ψ)] :
    IsOpenImmersion (Spec.map (φ ≫ ψ)) := by
  rw [Spec.map_comp]
  infer_instance

/-- Two actual principal localizations obey the canonical sheaf-level composition square. -/
theorem principal_comp (A : CommRingCat.{u}) (r : A) (s : Localization.Away r)
    (M : ModuleCat.{u} A) :
    let B := CommRingCat.of (Localization.Away r)
    let φ : A ⟶ B := CommRingCat.ofHom (algebraMap A (Localization.Away r))
    let ψ : B ⟶ CommRingCat.of (Localization.Away s) :=
      CommRingCat.ofHom (algebraMap (Localization.Away r) (Localization.Away s))
    (compositionRestrictionIso φ ψ).hom.app (tilde M) ≫
      (restrictFunctor (Spec.map ψ)).map ((restrictionIso φ).hom.app M) ≫
      (restrictionIso ψ).hom.app ((ModuleCat.extendScalars φ.hom).obj M) =
    (restrictionIso (φ ≫ ψ)).hom.app M ≫
      tilde.map ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M) := by
  dsimp only
  exact restrictionIso_hom_comp_app _ _ M

/-- The actual supported higher-Tor comparison obeys the principal-open composition square. -/
theorem higherTor_principal_comp :
    let A := CommRingCat.of (ℤ ⧸ (fourIdeal ⊔ fourIdeal))
    let B := CommRingCat.of (Localization.Away (3 : A))
    let φ : A ⟶ B := CommRingCat.ofHom (algebraMap A B)
    let ψ : B ⟶ CommRingCat.of (Localization.Away (3 : B)) :=
      CommRingCat.ofHom (algebraMap B (Localization.Away (3 : B)))
    let M := torSupportModule fourIdeal fourIdeal 1
    (compositionRestrictionIso φ ψ).hom.app (tilde M) ≫
      (restrictFunctor (Spec.map ψ)).map ((restrictionIso φ).hom.app M) ≫
      (restrictionIso ψ).hom.app ((ModuleCat.extendScalars φ.hom).obj M) =
    (restrictionIso (φ ≫ ψ)).hom.app M ≫
      tilde.map ((ModuleCat.extendScalarsComp φ.hom ψ.hom).hom.app M) :=
  principal_comp _ 3 3 _

/-- The actual module used in the canonical cocycle is nonzero higher Tor. -/
theorem higherTorSource_nonzero : ¬ Limits.IsZero (torSupportModule fourIdeal fourIdeal 1) :=
  TildeOpenBaseChange.higherTorSupport_nonzero

/-- No radical replacement is made in the support of the cocycle consumer. -/
theorem higherTorIdeal_not_radical : ¬ fourIdeal.IsRadical := fourIdeal_not_radical

end Motivic.MotivicTest.TildeOpenBaseChangeComposition
