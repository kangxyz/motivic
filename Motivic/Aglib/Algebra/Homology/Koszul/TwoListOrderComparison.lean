/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.TwoListReplacement
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.Balanced

/-!
# One common total coefficient for the two Koszul-list orders

The genuine tensor associators and signed tensor symmetry identify the two
actual list orders. Finite homology and Euler length transport along this
chain isomorphism. For a finite coefficient module over a Noetherian local
ring, a single Artinian final support quotient supplies both orders of the
two-list replacement theorem. Their actual fixed-support generic sums are
therefore equal. Geometric coefficient, list and stalk matching remain separate.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.MonoidalCategory
open HomologicalComplex
open _root_.HomologicalComplex.ModuleLengthEuler

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- The actual two outer Koszul factors commute by associators and the signed
chain-tensor braiding, for an arbitrary final coefficient complex. -/
def koszulTensorOrderIso (K : ChainComplex (ModuleCat R) ℕ) (s t : List R) :
    HomologicalComplex.tensorObj (chainComplex s)
        (HomologicalComplex.tensorObj (chainComplex t) K) ≅
      HomologicalComplex.tensorObj (chainComplex t)
        (HomologicalComplex.tensorObj (chainComplex s) K) :=
  (α_ (chainComplex s) (chainComplex t) K).symm ≪≫
    whiskerRightIso (_root_.ModuleCat.TorComparison.tensorTotalSymmetryIso (chainComplex s)
        (chainComplex t)) K ≪≫
    (α_ (chainComplex t) (chainComplex s) K)

/-- The coefficient recursion is identified with its actual degree-zero tensor
before and after the signed order comparison. -/
def twoListOrderIso (M : ModuleCat R) (s t : List R) :
    HomologicalComplex.tensorObj (chainComplex s) (coefficientComplex M t) ≅
      HomologicalComplex.tensorObj (chainComplex t) (coefficientComplex M s) :=
  whiskerLeftIso (chainComplex s) (_root_.ModuleCat.TorComparison.coefficientComplexTensorIso M t)
      ≪≫
    koszulTensorOrderIso ((ChainComplex.single₀ (ModuleCat R)).obj M) s t ≪≫
    whiskerLeftIso (chainComplex t) (_root_.ModuleCat.TorComparison.coefficientComplexTensorIso M
        s).symm

/-- The order comparison respects the literal total-complex differentials. -/
theorem twoListOrderIso_hom_comm (M : ModuleCat R) (s t : List R) (i j : ℕ) :
    (twoListOrderIso M s t).hom.f i ≫
        (HomologicalComplex.tensorObj (chainComplex t) (coefficientComplex M s)).d i j =
      (HomologicalComplex.tensorObj (chainComplex s) (coefficientComplex M t)).d i j ≫
        (twoListOrderIso M s t).hom.f j :=
  (twoListOrderIso M s t).hom.comm i j

/-- Genuine finite homology in one order supplies genuine finite homology in
the other order, without hypotheses on the original module's length. -/
theorem twoListOrder_finiteHomology (M : ModuleCat R) (s t : List R)
    (h : FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) (coefficientComplex M t))) :
    FiniteHomology (HomologicalComplex.tensorObj (chainComplex t) (coefficientComplex M s)) :=
  h.of_quasiIso (twoListOrderIso M s t).hom

/-- The actual signed chain Euler is the same for the two list orders. -/
theorem twoListOrder_chainEuler (M : ModuleCat R) (s t : List R)
    (h : FiniteHomology (HomologicalComplex.tensorObj (chainComplex s) (coefficientComplex M t))) :
    chainEuler (HomologicalComplex.tensorObj (chainComplex s) (coefficientComplex M t)) h =
      chainEuler (HomologicalComplex.tensorObj (chainComplex t) (coefficientComplex M s))
        (twoListOrder_finiteHomology M s t h) :=
  homologyEuler_eq_of_quasiIso (twoListOrderIso M s t).hom (fun n => (-1) ^ n) _ _

/-- The same actual final ideal gives the Artinian quotient for the swapped order. -/
theorem twoList_swappedArtinian (M : ModuleCat R) (s t : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      (Ideal.ofList t ⊔ Module.annihilator R M)))] :
    IsArtinianRing (R ⧸ (Ideal.ofList t ⊔
      (Ideal.ofList s ⊔ Module.annihilator R M))) := by
  rw [sup_left_comm]
  infer_instance

variable [IsNoetherianRing R]

/-- The literal fixed-support generic sum occurring in actual two-list replacement. -/
def twoListFixedSupportSum (M : ModuleCat R) [Module.Finite R M] (s t : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      (Ideal.ofList t ⊔ Module.annihilator R M)))] : ℤ :=
  ∑ᶠ p : (Ideal.ofList t ⊔ Module.annihilator R M).minimalPrimes,
    twoListGenericEuler M t p *
      chainEuler (coefficientComplex (ModuleCat.of R (R ⧸ p.1)) s)
        (fixedSupport_prime_finiteHomology s
          (Ideal.ofList t ⊔ Module.annihilator R M) p.1 p.2.le)

/-- Applying genuine two-list replacement in both orders identifies their two
actual fixed-support generic sums with one common total-complex coefficient.
Only one final Artinian quotient is assumed; the other one is derived. -/
theorem twoListFixedSupportSum_order [IsLocalRing R]
    (M : ModuleCat R) [Module.Finite R M] (s t : List R)
    [IsArtinianRing (R ⧸ (Ideal.ofList s ⊔
      (Ideal.ofList t ⊔ Module.annihilator R M)))]
    (hs : ∀ a ∈ s, a ∈ IsLocalRing.maximalIdeal R)
    (ht : ∀ a ∈ t, a ∈ IsLocalRing.maximalIdeal R) :
    let := twoList_swappedArtinian M s t
    twoListFixedSupportSum M s t = twoListFixedSupportSum M t s := by
  let := twoList_swappedArtinian M s t
  obtain ⟨hst, est⟩ := twoList_chainEuler_replacement M s t hs
  obtain ⟨hts, ets⟩ := twoList_chainEuler_replacement M t s ht
  exact est.symm.trans
    ((homologyEuler_eq_of_quasiIso (twoListOrderIso M s t).hom
      (fun n => (-1) ^ n) hst hts).trans ets)

end ChainComplex.Koszul
