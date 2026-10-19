/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.CommonFiniteUnitNeighborhood

/-! # One full-boundary neighborhood for two original functional pairs

Only the original source numerator and denominator and target numerator and
denominator are retained. In the graph application the target denominator must
first be proved a boundary unit on the actual disjoint parameter. The generic
marked graph pole is not assumed invertible. The given chart domains remain
unchanged as upper bounds, so existing free-chart restriction applies.


Intended upstream module: `Aglib.AlgebraicGeometry.Modules.Invertible.Frames.PairUnitNeighborhood`.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme

/-- The entire finite inverse image lies in both original source unit domains;
the target lies in both original target unit domains and its prior chart. -/
theorem exists_principal_pair_unit_neighborhood
    {Y X Z : Scheme.{u}} [IsAffine X]
    (p : Y ⟶ X) [IsFinite p] (z : Z ⟶ X) [IsClosedImmersion z]
    (U : Y.Opens) (V : X.Opens)
    (hsource : p ⁻¹' Set.range z ⊆ U) (htarget : Set.range z ⊆ V)
    (LB : LineBundle Y) (LA : LineBundle X)
    (n d : LB.val ⟶ SheafOfModules.unit Y.ringCatSheaf)
    (a c : LA.val ⟶ SheafOfModules.unit X.ringCatSheaf)
    [IsIso ((Modules.pullback (pullback.fst p z)).map n)]
    [IsIso ((Modules.pullback (pullback.fst p z)).map d)]
    [IsIso ((Modules.pullback z).map a)]
    [IsIso ((Modules.pullback z).map c)] :
    ∃ r : Γ(X, ⊤),
      IsAffineOpen (X.basicOpen r) ∧ IsAffineOpen (p ⁻¹ᵁ X.basicOpen r) ∧
      X.basicOpen r ≤ V ∧ p ⁻¹ᵁ X.basicOpen r ≤ U ∧
      X.basicOpen r ≤ zeroSupportUnitOpen LA a ∧
      X.basicOpen r ≤ zeroSupportUnitOpen LA c ∧
      p ⁻¹ᵁ X.basicOpen r ≤ zeroSupportUnitOpen LB n ∧
      p ⁻¹ᵁ X.basicOpen r ≤ zeroSupportUnitOpen LB d ∧
      ∃ t : Z ⟶ (X.basicOpen r).toScheme, t ≫ (X.basicOpen r).ι = z := by
  obtain ⟨r, hr, hrp, hrV, hrU, hra, hrc, hrn, hrd, _, _, t, ht⟩ :=
    exists_principal_common_unit_frame_neighborhood p z U V hsource htarget
      LB LB LB LA LA n d n d a c
  exact ⟨r, hr, hrp, hrV, hrU, hra, hrc, hrn, hrd, t, ht⟩

end AlgebraicGeometry.Scheme
