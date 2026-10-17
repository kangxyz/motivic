/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.KoszulResolutionQuotient
public import Motivic.Algebra.Homology.TorComparison.IdealQuotientFunctor

/-!
# The actual quotient-ring target of the regular-Koszul augmentation

The iterated scalar quotient of an arbitrary complex is naturally identified
with tensoring each term by the actual generated-ideal quotient ring. This
turns the previously proved regular augmentation into a genuine comparison
with the tensor complex that computes the one-sided categorical Tor functor.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open Motivic.Koszul

universe u

namespace Motivic.TorComparison

variable {R : Type u} [CommRing R]

/-- Applying the iterated quotient functor gives the literal iterated quotient complex. -/
theorem iteratedQuotientComplex_eq_map (s : List R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    iteratedQuotientComplex s K = mappedComplex (iteratedQuotientFunctor s) K := by
  induction s generalizing K with
  | nil => rfl
  | cons a s ih => exact ih (quotientComplex a K)

/-- The actual iterated quotient is the actual quotient-ring tensor complex. -/
def iteratedQuotientComplexTensorIso (s : List R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    iteratedQuotientComplex s K ≅
      mappedComplex ((tensoringLeft (ModuleCat R)).obj (ModuleCat.of R (R ⧸ Ideal.ofList s))) K :=
  eqToIso (iteratedQuotientComplex_eq_map s K) ≪≫
    (NatIso.mapHomologicalComplex (iteratedQuotientFunctorIso s) (ComplexShape.down ℕ)).app K ≪≫
      (NatIso.mapHomologicalComplex (idealQuotientFunctorIsoTensor (Ideal.ofList s))
        (ComplexShape.down ℕ)).app K

/-- The constructed regular augmentation has the genuine quotient-ring tensor target. -/
def koszulResolutionTensor (s : List R) (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex.tensorObj (chainComplex s) K ⟶
      mappedComplex ((tensoringLeft (ModuleCat R)).obj (ModuleCat.of R (R ⧸ Ideal.ofList s))) K :=
  koszulResolutionQuotient s K ≫ (iteratedQuotientComplexTensorIso s K).hom

/-- Termwise weak regularity proves the actual quotient-ring tensor comparison. -/
theorem koszulResolutionTensor_quasiIso (s : List R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hs : ∀ n, RingTheory.Sequence.IsWeaklyRegular (K.X n) s) :
    QuasiIso (koszulResolutionTensor s K) := by
  have := koszulResolutionQuotient_quasiIso s K hs
  dsimp only [koszulResolutionTensor]
  infer_instance

/-- Ring regularity supplies the comparison for every genuine projective resolution. -/
theorem projectiveResolutionTensor_quasiIso (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    QuasiIso (koszulResolutionTensor s P.complex) :=
  koszulResolutionTensor_quasiIso s P.complex
    (weaklyRegular_projectiveResolution_terms M P s hs)

/-- The explicit regular augmentation induces the comparison on actual homology modules. -/
def projectiveResolutionTensorHomologyIso (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (n : ℕ) :
    (HomologicalComplex.tensorObj (chainComplex s) P.complex).homology n ≅
      (mappedComplex ((tensoringLeft (ModuleCat R)).obj
        (ModuleCat.of R (R ⧸ Ideal.ofList s))) P.complex).homology n := by
  have := projectiveResolutionTensor_quasiIso M P s hs
  exact isoOfQuasiIsoAt (koszulResolutionTensor s P.complex) n

end Motivic.TorComparison
