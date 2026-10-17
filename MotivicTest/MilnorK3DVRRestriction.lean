/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.KTheory.MilnorK3.DVRRestriction
public import Lean.Util.CollectAxioms

/-! # Consumers of actual unramified DVR restriction -/

@[expose] public noncomputable section

namespace MotivicTest.MilnorK3DVRRestriction

open Motivic.KTheory.MilnorK2 Motivic.KTheory.MilnorK3

variable {R S K L : Type*}
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra S L] [IsFractionRing S L]
  (j : R →+* S) [IsLocalHom j] (F : K →+* L)
  (hF : ∀ r : R, F (algebraMap R K r) = algebraMap S L (j r))

include hF

omit [IsLocalHom j] in
/-- Integer-order compatibility is a conclusion from structural ring maps. -/
theorem original_order_is_preserved {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (a : Kˣ) :
    Motivic.KTheory.MilnorK2.DVR.value S L
        (Additive.ofMul (Units.map F.toMonoidHom a)) =
      Motivic.KTheory.MilnorK2.DVR.value R K (Additive.ofMul a) :=
  Motivic.KTheory.MilnorK3.DVR.value_map j F hF hπ hjπ (Additive.ofMul a)

/-- Every original K₃ quotient class satisfies the actual residue square. -/
theorem original_residue_commutes {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (x : K3 K) :
    Motivic.KTheory.MilnorK2.map (IsLocalRing.ResidueField.map j)
        (Motivic.KTheory.MilnorK3.DVR.residue R K x) =
      Motivic.KTheory.MilnorK3.DVR.residue S L (Motivic.KTheory.MilnorK3.map F x) :=
  LinearMap.congr_fun
    (Motivic.KTheory.MilnorK3.DVR.residue_restrict j F hF hπ hjπ) x

/-- The target angular component is obtained using the actual residue-field map. -/
theorem original_unit_reduction_commutes {π : R} (hπ : Irreducible π)
    (hjπ : Irreducible (j π)) (a : Kˣ) :
    Motivic.KTheory.MilnorK2.DVR.unitResidue (K := L) hjπ (Units.map F.toMonoidHom a) =
      Units.map (IsLocalRing.ResidueField.map j).toMonoidHom
        (Motivic.KTheory.MilnorK2.DVR.unitResidue (K := K) hπ a) :=
  Motivic.KTheory.MilnorK3.DVR.unitResidue_map j F hF hπ hjπ a

open Lean in
run_cmd do
  for name in #[``Motivic.KTheory.MilnorK3.DVR.residueFieldMap,
      ``Motivic.KTheory.MilnorK3.DVR.residueFieldMap_residue,
      ``Motivic.KTheory.MilnorK3.DVR.fieldUnits_map,
      ``Motivic.KTheory.MilnorK3.DVR.uniformizer_map,
      ``Motivic.KTheory.MilnorK3.DVR.mapped_normalizedLift_spec,
      ``Motivic.KTheory.MilnorK3.DVR.value_map,
      ``Motivic.KTheory.MilnorK3.DVR.normalizedLift_map,
      ``Motivic.KTheory.MilnorK3.DVR.unitResidue_map,
      ``Motivic.KTheory.MilnorK3.DVR.unitPart_map,
      ``Motivic.KTheory.MilnorK3.DVR.residue_restrict,
      ``original_order_is_preserved, ``original_residue_commutes,
      ``original_unit_reduction_commutes] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual unramified DVR restriction uses only standard Lean logical foundations."

end MotivicTest.MilnorK3DVRRestriction
