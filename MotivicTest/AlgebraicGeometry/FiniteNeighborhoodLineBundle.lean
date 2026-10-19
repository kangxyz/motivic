/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteBaseNeighborhood
public import Mathlib.Data.ZMod.Basic

/-! # Actual finite-neighborhood line-bundle consumers -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- A finite set of primes can include nonmaximal and comparable points. -/
example (R : CommRingCat.{u}) (L : LineBundle (Spec R)) (p q : PrimeSpectrum R) :
    ∃ U : (Spec R).Opens, p ∈ U ∧ q ∈ U ∧
      Nonempty ((restrictFunctor U.ι).obj L.val ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  classical
  obtain ⟨r, hr, he⟩ := exists_principal_unitIso_around_finset R L {p, q}
  exact ⟨PrimeSpectrum.basicOpen r, hr p (by simp), hr q (by simp), he⟩

/-- Empty point sets and nonreduced ambient schemes are covered. -/
example (L : LineBundle (Spec (.of (ZMod 4)))) :
    ∃ U : (Spec (.of (ZMod 4))).Opens,
      Nonempty ((restrictFunctor U.ι).obj L.val ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  obtain ⟨U, _, he⟩ := exists_open_unitIso_around_finite _ L ∅ Set.finite_empty
  exact ⟨U, he⟩

/-- The zero-ring affine scheme is allowed in the spreading theorem. -/
example (L : LineBundle (Spec (.of (ZMod 1)))) :
    ∃ U : (Spec (.of (ZMod 1))).Opens,
      Nonempty ((restrictFunctor U.ι).obj L.val ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  obtain ⟨U, _, he⟩ := exists_open_unitIso_around_finite _ L ∅ Set.finite_empty
  exact ⟨U, he⟩

/-- The entire actual inverse image of the base neighborhood is trivialized,
without requiring the source or base to be globally affine. -/
example {B S : Scheme.{u}} (f : B ⟶ S) [IsFinite f] (s : S) (L : LineBundle B) :
    ∃ U : S.Opens, s ∈ U ∧
      Nonempty ((restrictFunctor (f ⁻¹ᵁ U).ι).obj L.val ≅
        SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.ringCatSheaf) :=
  exists_base_open_unitIso_of_isFinite f s L

/-- A finite boundary can lie in an ambient affine curve of positive dimension.
Only its projection is finite; the original ambient line bundle is trivialized
on an open containing all boundary points over the new base neighborhood. -/
example {B C S : Scheme.{u}} [IsAffine C]
    (f : B ⟶ S) [IsFinite f] (i : B ⟶ C) [IsClosedImmersion i]
    (s : S) (L : LineBundle C) :
    ∃ (Ω : C.Opens) (U : S.Opens), s ∈ U ∧
      (∀ b : B, f b ∈ U → i b ∈ Ω) ∧
      Nonempty ((restrictFunctor Ω.ι).obj L.val ≅
        SheafOfModules.unit Ω.toScheme.ringCatSheaf) := by
  obtain ⟨Ω, U, hs, hinc, he⟩ := exists_base_open_support_unitIso f i s L
  exact ⟨Ω, U, hs, fun _ hb ↦ hinc hb, he⟩

end
