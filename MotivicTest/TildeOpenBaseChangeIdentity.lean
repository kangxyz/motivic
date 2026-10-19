/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeBaseChange.Identity
public import MotivicTest.TildeOpenBaseChange

/-! # Canonical tilde/open unit on actual nonzero supported higher Tor -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace Motivic.MotivicTest.TildeOpenBaseChangeIdentity

open _root_.AlgebraicGeometry.Scheme.Modules.QuasiCoherent.Affine.TildeBaseChange
open _root_.ComplexShape
open _root_.HomologicalComplex
open _root_.HomologicalComplex₂
open _root_.ModuleCat.TorComparison
open TorQuotientFiniteness

/-- The actual supported higher-Tor sheaf comparison obeys the genuine geometric/scalar unit law. -/
theorem higherTor_unit :
    let A := CommRingCat.of (ℤ ⧸ (fourIdeal ⊔ fourIdeal))
    let M := torSupportModule fourIdeal fourIdeal 1
    (restrictionIso (𝟙 A)).hom.app M ≫
        tilde.map ((ModuleCat.extendScalarsId A).hom.app M) =
      (identityRestrictionIso A).hom.app (tilde M) :=
  restrictionIso_hom_id _ _

/-- The actual source module in the sheaf-level unitor is nonzero. -/
theorem higherTorSource_nonzero : ¬ Limits.IsZero (torSupportModule fourIdeal fourIdeal 1) :=
  TildeOpenBaseChange.higherTorSupport_nonzero

/-- The original support ideal in the unit consumer is nonradical. -/
theorem higherTorIdeal_not_radical : ¬ fourIdeal.IsRadical := fourIdeal_not_radical

end Motivic.MotivicTest.TildeOpenBaseChangeIdentity
