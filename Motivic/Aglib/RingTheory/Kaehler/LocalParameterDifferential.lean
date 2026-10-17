/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Smooth.Field
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Nonzero residue differentials of local parameters over a perfect field -/
@[expose] public noncomputable section
open Module TensorProduct KaehlerDifferential IsLocalRing
universe u v
namespace KaehlerDifferential

/-- Formal smoothness of the residue extension makes the conormal map injective,
so a positive-rank regular local ring has a maximal-ideal element with nonzero differential. -/
theorem exists_maximalIdeal_residue_differential_ne_zero
    (k : Type u) (A : Type v) [Field k] [PerfectField k] [CommRing A]
    [Algebra k A] [IsRegularLocalRing A]
    [Algebra.FormallySmooth k A] [Algebra.EssFiniteType k (ResidueField A)]
    (hpos : 0 < ringKrullDim A) :
    ∃ f ∈ maximalIdeal A, (1 ⊗ₜ[A] D k A f : ResidueField A ⊗[A] Ω[A⁄k]) ≠ 0 := by
  have hdim := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := A)).mp
    (inferInstance : IsRegularLocalRing A)
  have hfin : 0 < Module.finrank (ResidueField A) (CotangentSpace A) := by
    exact_mod_cast hdim ▸ hpos
  have hker : RingHom.ker (algebraMap A (ResidueField A)) = maximalIdeal A := ker_residue
  have : Nontrivial (CotangentSpace A) := Module.nontrivial_of_finrank_pos hfin
  have : Nontrivial (RingHom.ker (algebraMap A (ResidueField A))).Cotangent := by
    rw [hker]
    infer_instance
  obtain ⟨x, hx⟩ := exists_ne (0 : (RingHom.ker (algebraMap A (ResidueField A))).Cotangent)
  obtain ⟨f, hf⟩ := (RingHom.ker (algebraMap A (ResidueField A))).toCotangent_surjective x
  have hinj : Function.Injective (kerCotangentToTensor k A (ResidueField A)) :=
    (Algebra.FormallySmooth.kerCotangentToTensor_injective_iff residue_surjective).mpr
      inferInstance
  refine ⟨f, hker ▸ f.property, ?_⟩
  intro hz
  have hz' : kerCotangentToTensor k A (ResidueField A) (Ideal.toCotangent _ f) = 0 := hz
  have hh := hinj (hz'.trans (map_zero _).symm)
  exact hx (hf.symm.trans hh)

end KaehlerDifferential
