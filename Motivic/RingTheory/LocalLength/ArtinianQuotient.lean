/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Length
public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Finite length from an annihilating Artinian quotient

A Noetherian module annihilated by an ideal with Artinian quotient has finite
length. The quotient-ring module structure is actually constructed, and
Artinianness is transported through the resulting bijective semilinear map.
-/

@[expose] public section

universe u v

namespace Motivic.LocalLength

variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- An annihilating Artinian quotient makes a Noetherian module finite-length. -/
theorem length_ne_top_of_artinian_quotient [IsNoetherian R M] (I : Ideal R)
    [IsArtinianRing (R ⧸ I)] (hI : I ≤ Module.annihilator R M) :
    Module.length R M ≠ ⊤ := by
  have hT : Module.IsTorsionBySet R M I :=
    (Module.isTorsionBySet_iff_subset_annihilator R M).mpr hI
  let := hT.module
  have : IsScalarTower R (R ⧸ I) M := Module.IsTorsionBySet.isScalarTower hT
  have : Module.Finite (R ⧸ I) M := Module.Finite.of_restrictScalars_finite R (R ⧸ I) M
  have : IsArtinian R M :=
    (hT.semilinearMap.isArtinian_iff_of_bijective Function.bijective_id).mpr inferInstance
  exact Module.length_ne_top_iff.mpr
    (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

end Motivic.LocalLength
