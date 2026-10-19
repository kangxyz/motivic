/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.DimensionZeroHead
public import Motivic.Aglib.Algebra.Homology.Koszul.DimensionSupport
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness

/-!
# Dimension vanishing for actual coefficient Koszul Euler length

Over a Noetherian local ring, a finite coefficient module has zero Koszul
Euler characteristic when its support dimension is smaller than the list
length, all equations lie in the maximal ideal, and the equation quotient
on coefficient support is Artinian.

The proof uses the actual prime-filtration induction principle, coefficient
Euler additivity, signed two-column cancellation for an annihilating head,
and the genuine regular-head quasi-isomorphism and local dimension drop.
-/

@[expose] public section

universe u

open CategoryTheory _root_.HomologicalComplex.ModuleLengthEuler

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Strict support-dimension deficiency forces the genuine all-degree Koszul
Euler characteristic to vanish. All finiteness is derived from Artinian
coefficient support; no regularity of the list or module is assumed. -/
theorem koszulDimension_chainEuler_zero (M : ModuleCat R) [Module.Finite R M]
    (s : List R) (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R)
    (hd : Module.supportDim R M < s.length)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔ Module.annihilator R M))] :
    chainEuler (coefficientComplex M s) (finiteHomology_of_artinian_support_quotient M s) = 0 := by
  induction s generalizing M with
  | nil =>
    exact koszulDimension_chainEuler_zero_of_supportDim_lt_zero M [] hd _
  | cons a s ih =>
    have hAll : ∀ (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
        Module.supportDim R N < (a :: s).length →
        ∀ [IsArtinianRing (R ⧸ (Ideal.ofList (a :: s) ⊔ Module.annihilator R N))],
        chainEuler (coefficientComplex (ModuleCat.of R N) (a :: s))
          (finiteHomology_of_artinian_support_quotient _ _) = 0 := by
      intro N _ _ hN
      induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
      | subsingleton N =>
        intro _ _
        exact koszulDimension_chainEuler_zero_of_subsingleton _ _ _
      | quotient N p e =>
        intro hdN hArtN
        by_cases ha : a ∈ p.asIdeal
        · apply koszulDimension_chainEuler_zero_of_mem_annihilator
          change a ∈ Module.annihilator R N
          rw [e.annihilator_eq, Ideal.annihilator_quotient]
          exact ha
        · have hreg : IsSMulRegular N a := by
            intro x y hxy
            apply e.injective
            apply Module.scalar_regular_primeQuotient p.asIdeal a ha
            simpa only [map_smul] using congrArg e hxy
          have hArtQ := koszulDimension_artinian_scalarQuotient (ModuleCat.of R N) a s
          have hdQ := koszulDimensionReduction_supportDim_lt (ModuleCat.of R N) a s hreg
            (hs a List.mem_cons_self) hdN
          rw [koszulDimensionReduction_chainEuler _ _ _ hreg]
          have : Module.Finite R ((scalarQuotientFunctor a).obj (ModuleCat.of R N)) := by
            change Module.Finite R (SingleQuotient N a)
            infer_instance
          exact ih ((scalarQuotientFunctor a).obj (ModuleCat.of R N))
            (fun b hb => hs b (List.mem_cons_of_mem a hb)) hdQ
      | exact N₁ N₂ N₃ f g hf hg hex ih₁ ih₃ =>
        intro hdN hArtN
        have hAnn₁ := f.annihilator_le_of_injective hf
        have hAnn₃ := g.annihilator_le_of_surjective hg
        have hArt₁ : IsArtinianRing
            (R ⧸ (Ideal.ofList (a :: s) ⊔ Module.annihilator R N₁)) :=
          koszulDimension_artinian_quotient_of_le _ _ (sup_le_sup_left hAnn₁ _)
        have hArt₃ : IsArtinianRing
            (R ⧸ (Ideal.ofList (a :: s) ⊔ Module.annihilator R N₃)) :=
          koszulDimension_artinian_quotient_of_le _ _ (sup_le_sup_left hAnn₃ _)
        have hz₁ := ih₁ ((Module.supportDim_le_of_injective f hf).trans_lt hdN)
        have hz₃ := ih₃ ((Module.supportDim_le_of_surjective g hg).trans_lt hdN)
        let S := ModuleCat.shortComplexOfCompEqZero f g hex.linearMap_comp_eq_zero
        have hS : S.ShortExact := ModuleCat.shortComplex_shortExact _ hex hf hg
        have he := coefficient_chainEuler_add_of_shortExact (a :: s) S hS
          (finiteHomology_of_artinian_support_quotient _ _)
          (finiteHomology_of_artinian_support_quotient _ _)
          (finiteHomology_of_artinian_support_quotient _ _)
        exact he.trans (by rw [hz₁, hz₃]; rfl)
    exact hAll M hd

end ChainComplex.Koszul
