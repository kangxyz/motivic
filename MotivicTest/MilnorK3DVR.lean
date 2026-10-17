/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.KTheory.MilnorK3.DVR
public import Lean.Util.CollectAxioms

/-! # Actual DVR consumers of the degree-three Milnor residue -/

@[expose] public noncomputable section

namespace MotivicTest.MilnorK3DVR

open Motivic.KTheory.MilnorK2 Motivic.KTheory.MilnorK3

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The target is the Milnor K₂ of the actual residue field, not supplied residue data. -/
def actualResidue : K3 K →ₗ[ℤ] K2 (IsLocalRing.ResidueField R) :=
  Motivic.KTheory.MilnorK3.DVR.residue R K

/-- Every actual irreducible computes the same full homomorphism. -/
theorem every_uniformizer {π : R} (hπ : Irreducible π) :
    actualResidue (R := R) (K := K) =
      Motivic.KTheory.MilnorK3.DVR.residueWithUniformizer (K := K) hπ :=
  Motivic.KTheory.MilnorK3.DVR.residue_eq hπ

/-- The literal ring residue map determines the normalized symbol. -/
theorem original_residue_normalization {π : R} (hπ : Irreducible π) (u v : Rˣ) :
    actualResidue (R := R) (K := K)
      (symbol3 (Motivic.KTheory.MilnorK2.DVR.uniformizer (K := K) hπ)
        (Motivic.KTheory.MilnorK2.DVR.fieldUnits R K u)
        (Motivic.KTheory.MilnorK2.DVR.fieldUnits R K v)) =
      symbol (Units.map (IsLocalRing.residue R).toMonoidHom u)
        (Units.map (IsLocalRing.residue R).toMonoidHom v) :=
  Motivic.KTheory.MilnorK3.DVR.residue_uniformizer_ring_units hπ u v

open Lean in
run_cmd do
  for name in #[``Motivic.KTheory.MilnorK3.DVR.residueWithUniformizer,
      ``Motivic.KTheory.MilnorK3.DVR.residueWithUniformizer_independent,
      ``Motivic.KTheory.MilnorK3.DVR.residue,
      ``Motivic.KTheory.MilnorK3.DVR.residue_eq,
      ``Motivic.KTheory.MilnorK3.DVR.residue_ring_units,
      ``Motivic.KTheory.MilnorK3.DVR.residue_uniformizer_ring_units,
      ``actualResidue, ``every_uniformizer, ``original_residue_normalization] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual DVR Milnor K3 residue uses only standard Lean logical foundations."

end MotivicTest.MilnorK3DVR
