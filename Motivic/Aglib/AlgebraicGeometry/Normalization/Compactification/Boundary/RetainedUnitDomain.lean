/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.ZeroLocus.UnitOpenPullback
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # Actual full inverse boundary lies in the original functional unit domain

Range containment is used only to factor through an open unit domain. This does
not replace the full scheme factors needed for boundary values or norm equations.


Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.RetainedUnitDomain`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme

variable {C X Y U Z D I : Scheme.{u}}
  (f : C ⟶ X) (j : Y ⟶ C) (d : D ⟶ C)
  (hd : Set.range d = (Set.range j)ᶜ)
  (z : Z ⟶ X) (s : Z ⟶ Y) (H : IsPullback s (𝟙 Z) (j ≫ f) z)
  (i : I ⟶ X) (p : Y ⟶ U) (k : U ⟶ X)
  (hp : p ≫ k = j ≫ f) (hi : Disjoint (Set.range k) (Set.range i))

include hd H hp hi in
/-- The original retained triangle and marked pullback cover the full inverse
boundary by the old complement and the original marked section. -/
theorem preimage_fullBoundary_subset_retainedBoundary :
    f ⁻¹' (Set.range i ∪ Set.range z) ⊆ Set.range d ∪ Set.range (s ≫ j) := by
  intro x hx
  by_cases hj : x ∈ Set.range j
  · obtain ⟨y, rfl⟩ := hj
    rcases hx with hx | hx
    · exfalso
      exact Set.disjoint_left.mp hi ⟨p y, congrArg (fun l => l y) hp⟩ hx
    · obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb, _⟩ := exists_preimage_of_isPullback H y a ha.symm
      exact Or.inr ⟨b, congrArg (fun t => j t) hb⟩
  · exact Or.inl (hd.symm ▸ hj)

include hd H hp hi in
/-- Boundary units of the original functional extend to every map whose range
lies in the full inverse boundary. The open factorization retains nilpotents. -/
theorem isIso_pullbackUnitMap_of_fullBoundary_range
    (L : LineBundle C) (φ : L.val ⟶ SheafOfModules.unit C.ringCatSheaf)
    [IsIso ((Modules.pullback d).map φ)]
    [IsIso ((Modules.pullback (s ≫ j)).map φ)]
    {W : Scheme.{u}} (w : W ⟶ C)
    (hw : Set.range w ⊆ f ⁻¹' (Set.range i ∪ Set.range z)) :
    IsIso (pullbackUnitMap w φ) := by
  apply isIso_pullbackUnitMap_of_range_subset_unitOpen L φ w
  intro x hx
  rcases preimage_fullBoundary_subset_retainedBoundary f j d hd z s H i p k hp hi
      (hw hx) with hx | hx
  · exact range_subset_zeroSupportUnitOpen_of_pullback_isIso L φ d hx
  · exact range_subset_zeroSupportUnitOpen_of_pullback_isIso L φ (s ≫ j) hx

end AlgebraicGeometry.Scheme
