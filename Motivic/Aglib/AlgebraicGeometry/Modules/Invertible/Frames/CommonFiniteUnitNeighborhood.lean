/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.CommonFiniteNeighborhood
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.UnitOpen

/-! # A common neighborhood for the same frames and chosen functionals

The whole inverse boundary, not merely the marked component, is used to retain
both original source functionals. The canonical unit opens choose no new
sections. No freeness of sections over the resulting affine open is asserted.


Intended upstream module:
`Aglib.AlgebraicGeometry.Modules.Invertible.Frames.CommonFiniteUnitNeighborhood`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.PairUnitNeighborhood`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme

/-- Refine the fixed frame domains inside the unit loci of all six SAME
functionals, retaining the entire original closed boundary and its full inverse. -/
theorem exists_principal_common_unit_frame_neighborhood
    {Y X Z : Scheme.{u}} [IsAffine X]
    (p : Y ⟶ X) [IsFinite p] (z : Z ⟶ X) [IsClosedImmersion z]
    (U : Y.Opens) (V : X.Opens)
    (hsource : p ⁻¹' Set.range z ⊆ U) (htarget : Set.range z ⊆ V)
    (LB MB NB : LineBundle Y) (LA MA : LineBundle X)
    (aB : LB.val ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (bB : MB.val ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (nB dB : NB.val ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (aA : LA.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    (bA : MA.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso ((Modules.pullback (pullback.fst p z)).map aB)]
    [IsIso ((Modules.pullback (pullback.fst p z)).map bB)]
    [IsIso ((Modules.pullback (pullback.fst p z)).map nB)]
    [IsIso ((Modules.pullback (pullback.fst p z)).map dB)]
    [IsIso ((Modules.pullback z).map aA)]
    [IsIso ((Modules.pullback z).map bA)] :
    ∃ r : Γ(X, ⊤),
      IsAffineOpen (X.basicOpen r) ∧ IsAffineOpen (p ⁻¹ᵁ X.basicOpen r) ∧
      X.basicOpen r ≤ V ∧ p ⁻¹ᵁ X.basicOpen r ≤ U ∧
      X.basicOpen r ≤ zeroSupportUnitOpen LA aA ∧
      X.basicOpen r ≤ zeroSupportUnitOpen MA bA ∧
      p ⁻¹ᵁ X.basicOpen r ≤ zeroSupportUnitOpen LB aB ∧
      p ⁻¹ᵁ X.basicOpen r ≤ zeroSupportUnitOpen MB bB ∧
      p ⁻¹ᵁ X.basicOpen r ≤ zeroSupportUnitOpen NB nB ∧
      p ⁻¹ᵁ X.basicOpen r ≤ zeroSupportUnitOpen NB dB ∧
      ∃ t : Z ⟶ (X.basicOpen r).toScheme, t ≫ (X.basicOpen r).ι = z := by
  have haB : p ⁻¹' Set.range z ⊆ zeroSupportUnitOpen LB aB := by
    rw [← Scheme.Pullback.range_fst]
    exact range_subset_zeroSupportUnitOpen_of_pullback_isIso LB aB (pullback.fst p z)
  have hbB : p ⁻¹' Set.range z ⊆ zeroSupportUnitOpen MB bB := by
    rw [← Scheme.Pullback.range_fst]
    exact range_subset_zeroSupportUnitOpen_of_pullback_isIso MB bB (pullback.fst p z)
  have hnB : p ⁻¹' Set.range z ⊆ zeroSupportUnitOpen NB nB := by
    rw [← Scheme.Pullback.range_fst]
    exact range_subset_zeroSupportUnitOpen_of_pullback_isIso NB nB (pullback.fst p z)
  have hdB : p ⁻¹' Set.range z ⊆ zeroSupportUnitOpen NB dB := by
    rw [← Scheme.Pullback.range_fst]
    exact range_subset_zeroSupportUnitOpen_of_pullback_isIso NB dB (pullback.fst p z)
  have haA := range_subset_zeroSupportUnitOpen_of_pullback_isIso LA aA z
  have hbA := range_subset_zeroSupportUnitOpen_of_pullback_isIso MA bA z
  obtain ⟨r, hr, hrp, hrA, hrB, t, ht⟩ :=
    exists_principal_common_frame_neighborhood p z
      (U ⊓ (zeroSupportUnitOpen LB aB ⊓ zeroSupportUnitOpen MB bB) ⊓
        (zeroSupportUnitOpen NB nB ⊓ zeroSupportUnitOpen NB dB))
      (V ⊓ zeroSupportUnitOpen LA aA ⊓ zeroSupportUnitOpen MA bA)
      (fun _ hx => ⟨⟨hsource hx, ⟨haB hx, hbB hx⟩⟩, ⟨hnB hx, hdB hx⟩⟩)
      (fun _ hx => ⟨⟨htarget hx, haA hx⟩, hbA hx⟩)
  exact ⟨r, hr, hrp, fun _ hx => (hrA hx).1.1,
    (fun _ hx => (hrB hx).1.1), (fun _ hx => (hrA hx).1.2),
    (fun _ hx => (hrA hx).2), (fun _ hx => (hrB hx).1.2.1),
    (fun _ hx => (hrB hx).1.2.2), (fun _ hx => (hrB hx).2.1),
    (fun _ hx => (hrB hx).2.2), t, ht⟩

end AlgebraicGeometry.Scheme
