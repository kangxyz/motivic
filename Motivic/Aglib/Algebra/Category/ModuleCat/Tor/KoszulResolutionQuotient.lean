/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatRegularSequence
public import Aglib.Algebra.Homology.Koszul.Coefficient.Regular
public import Aglib.Algebra.Homology.Koszul.Single.Tensor.Quotient

/-!
# The regular-Koszul augmentation on arbitrary resolution complexes

The actual finite Koszul complex tensored with a nonnegative complex maps to
its literal iterated degreewise scalar quotient. Termwise weak regularity
proves this constructed map is a quasi-isomorphism, by the proved one-element
augmentation and finite-list induction. For a projective resolution, ring
regularity supplies the hypotheses in every degree. No bound or regularity
is required on its resolved module.

This establishes the regular-augmentation side of the intended two-resolution
comparison. Identifying the iterated quotient with extension of scalars to the
single ideal quotient, and the exterior-resolution construction, are separate.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory
open _root_.ChainComplex.Koszul

universe u

namespace ModuleCat.TorComparison

variable {R : Type u} [CommRing R]

/-- An actual right-associated finite string of one-element tensor complexes. -/
def iteratedKoszulTensor : List R → ChainComplex (ModuleCat.{u} R) ℕ →
    ChainComplex (ModuleCat R) ℕ
  | [], K => K
  | a :: s, K => HomologicalComplex.tensorObj (singleComplex R a) (iteratedKoszulTensor s K)

/-- Reassociating the actual finite Koszul tensor gives its iterated form. -/
def iteratedKoszulTensorIso : (s : List R) → (K : ChainComplex (ModuleCat.{u} R) ℕ) →
    iteratedKoszulTensor s K ≅ HomologicalComplex.tensorObj (chainComplex s) K
  | [], K => (HomologicalComplex.leftUnitor K).symm
  | a :: s, K => whiskerLeftIso (singleComplex R a) (iteratedKoszulTensorIso s K) ≪≫
      (HomologicalComplex.associator (singleComplex R a) (chainComplex s) K).symm

/-- The literal complex obtained by successively quotienting by each scalar. -/
def iteratedQuotientComplex : List R → ChainComplex (ModuleCat.{u} R) ℕ →
    ChainComplex (ModuleCat R) ℕ
  | [], K => K
  | a :: s, K => iteratedQuotientComplex s (quotientComplex a K)

/-- Quotienting commutes with the remaining finite Koszul tensor factors. -/
def quotientIteratedKoszulTensorIso (a : R) : (s : List R) →
    (K : ChainComplex (ModuleCat.{u} R) ℕ) →
    quotientComplex a (iteratedKoszulTensor s K) ≅
      iteratedKoszulTensor s (quotientComplex a K)
  | [], K => Iso.refl (quotientComplex a K)
  | b :: s, K => singleTensorMapIso (scalarQuotientFunctor a) b
        (iteratedKoszulTensor s K) (fun X => scalarQuotientFunctor_map_lsmul a X b) ≪≫
      whiskerLeftIso (singleComplex R b) (quotientIteratedKoszulTensorIso a s K)

/-- Termwise scalar injectivity survives any finite string of one-element tensors. -/
theorem iteratedKoszulTensor_isSMulRegular (a : R) (s : List R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (ha : ∀ n, IsSMulRegular (K.X n) a) (n : ℕ) :
    IsSMulRegular ((iteratedKoszulTensor s K).X n) a := by
  induction s generalizing n with
  | nil => exact ha n
  | cons b s ih => exact singleTensor_isSMulRegular a b (iteratedKoszulTensor s K) ih n

/-- The successive genuine scalar-quotient augmentations, as one chain map. -/
def iteratedKoszulAugmentation : (s : List R) →
    (K : ChainComplex (ModuleCat.{u} R) ℕ) →
    iteratedKoszulTensor s K ⟶ iteratedQuotientComplex s K
  | [], K => 𝟙 K
  | a :: s, K => tensorAugmentation a (iteratedKoszulTensor s K) ≫
      (quotientIteratedKoszulTensorIso a s K).hom ≫
        iteratedKoszulAugmentation s (quotientComplex a K)

set_option backward.isDefEq.respectTransparency false in
/-- Degreewise weak regularity proves the constructed iterated augmentation is a
quasi-isomorphism, with no boundedness assumption on the coefficient complex. -/
theorem iteratedKoszulAugmentation_quasiIso (s : List R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hs : ∀ n, RingTheory.Sequence.IsWeaklyRegular (K.X n) s) :
    QuasiIso (iteratedKoszulAugmentation s K) := by
  induction s generalizing K with
  | nil => exact quasiIso_of_isIso (𝟙 K)
  | cons a s ih =>
    have ha : ∀ n, IsSMulRegular (K.X n) a := fun n =>
      ((coefficient_isWeaklyRegular_cons_iff (K.X n) a s).mp (hs n)).1
    have ht : ∀ n, RingTheory.Sequence.IsWeaklyRegular ((quotientComplex a K).X n) s :=
      fun n => ((coefficient_isWeaklyRegular_cons_iff (K.X n) a s).mp (hs n)).2
    have := tensorAugmentation_quasiIso_of_regular a (iteratedKoszulTensor s K)
      (iteratedKoszulTensor_isSMulRegular a s K ha)
    have := ih (quotientComplex a K) ht
    dsimp only [iteratedKoszulAugmentation]
    infer_instance

/-- The regular augmentation starts from the actual, already constructed finite
Koszul tensor complex rather than a stipulated comparison object. -/
def koszulResolutionQuotient (s : List R) (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    HomologicalComplex.tensorObj (chainComplex s) K ⟶ iteratedQuotientComplex s K :=
  (iteratedKoszulTensorIso s K).inv ≫ iteratedKoszulAugmentation s K

/-- The actual finite Koszul tensor computes the literal iterated quotient
whenever the scalar list is weakly regular on every term. -/
theorem koszulResolutionQuotient_quasiIso (s : List R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (hs : ∀ n, RingTheory.Sequence.IsWeaklyRegular (K.X n) s) :
    QuasiIso (koszulResolutionQuotient s K) := by
  have := iteratedKoszulAugmentation_quasiIso s K hs
  dsimp only [koszulResolutionQuotient]
  infer_instance

/-- Ring regularity proves the comparison for any actual projective resolution;
the resolution can be unbounded and its resolved module can have higher Tor. -/
theorem projectiveResolutionQuotient_quasiIso (M : ModuleCat.{u} R)
    (P : ProjectiveResolution M) (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) :
    QuasiIso (koszulResolutionQuotient s P.complex) :=
  koszulResolutionQuotient_quasiIso s P.complex
    (weaklyRegular_projectiveResolution_terms M P s hs)

end ModuleCat.TorComparison
