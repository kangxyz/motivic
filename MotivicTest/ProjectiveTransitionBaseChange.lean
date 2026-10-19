/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.Twisting.TransitionBaseChange

/-! # Native section-valued transition base-change consumers -/

open AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace

universe u

variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) (ι : Type u)

example (i j : ι) :
    ProjectiveSpace.map f ι ⁻¹ᵁ (coordinateOpen R ι i ⊓ coordinateOpen R ι j) =
      coordinateOpen S ι i ⊓ coordinateOpen S ι j := by
  rw [Scheme.Hom.preimage_inf, map_preimage_coordinateOpen, map_preimage_coordinateOpen]

example (i j : ι) (d : ℤ) :
    Units.map ((ProjectiveSpace.map f ι).app
        (coordinateOpen R ι i ⊓ coordinateOpen R ι j)).hom.toMonoidHom
        (coordinateTransitionOn R ι i j inf_le_left inf_le_right ^ (-d)) =
      coordinateTransitionOn S ι i j
        (le_coordinateOpen_of_le_preimage f ι i le_rfl inf_le_left)
        (le_coordinateOpen_of_le_preimage f ι j le_rfl inf_le_right) ^ (-d) :=
  coordinateTransitionOn_zpow_map_app f ι i j inf_le_left inf_le_right (-d)

open Lean in
run_cmd do
  for name in #[``AlgebraicGeometry.ProjectiveSpace.coordinateTransitionOn_map_appLE,
      ``AlgebraicGeometry.ProjectiveSpace.coordinateTransitionOn_map_app,
      ``AlgebraicGeometry.ProjectiveSpace.coordinateTransitionOn_zpow_map_app] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Projective transition base change uses only standard foundations."
