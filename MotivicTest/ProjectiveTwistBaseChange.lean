/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.TwistBaseChangeIsomorphism

/-! # Actual integral twisting-sheaf coefficient-change consumers -/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (ι : Type u)

example (n : ℤ) :
    (Scheme.Modules.pullback (ProjectiveSpace.map f ι)).obj (twistingSheaf R ι n) ≅
      twistingSheaf S ι n := twistingBaseChangeIso f ι n

example (n : ℤ) : (twistingBaseChangeIso f ι n).hom = twistingBaseChangeMap f ι n := rfl

open Lean in
run_cmd do
  for name in #[``AlgebraicGeometry.ProjectiveSpace.twistingBaseChangeIso,
      ``AlgebraicGeometry.ProjectiveSpace.twistingBaseChangeMap_isIso] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual twisting-sheaf base change uses only standard foundations."
