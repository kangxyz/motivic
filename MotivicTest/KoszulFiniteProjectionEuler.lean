/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulFiniteProjectionEuler
public import Motivic.Algebra.Homology.KoszulHyperhomologyPlacement
public import MotivicTest.LengthEulerFiniteAlgebra
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Finite Koszul projection with genuine total-homology inputs

Consumers include a nonflat residue quotient, all maximal branches of the
two-branch algebra with a calculated negative Euler sum, and a contractible
coefficient complex built from a completely unrestricted original complex.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory Motivic.Koszul Motivic.LengthEuler

namespace MotivicTest.KoszulFiniteProjectionEuler

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R S]

/-- The source total has finite homology without finiteness of the original complex. -/
theorem actualSourceFinite (s : List R) (K : ChainComplex (ModuleCat S) ℕ)
    (hK : FiniteHomology (finiteProjectionTotal R S s K)) :
    FiniteHomology (finiteProjectionSource R S s K) :=
  finiteProjectionSource_finiteHomology R S s K hK

omit [IsLocalRing R] in
/-- Every genuine maximal localization has finite total homology. -/
theorem actualLocalFinite (s : List R) (K : ChainComplex (ModuleCat S) ℕ)
    (hK : FiniteHomology (finiteProjectionTotal R S s K)) (p : MaximalSpectrum S) :
    FiniteHomology (finiteProjectionLocal R S s K p) :=
  finiteProjectionLocal_finiteHomology R S s K hK p

/-- Repeated and zero equations participate in the actual residue-weighted sum. -/
theorem repeatedZeroProjection (a : R) (K : ChainComplex (ModuleCat S) ℕ)
    (hK : FiniteHomology (finiteProjectionTotal R S [a, a, 0] K)) :
    chainEuler (finiteProjectionSource R S [a, a, 0] K)
        (finiteProjectionSource_finiteHomology R S [a, a, 0] K hK) =
      ∑ᶠ p : MaximalSpectrum S, (Module.finiteAlgebraResidueDegree R S p : ℤ) *
        chainEuler (finiteProjectionLocal R S [a, a, 0] K p)
          (finiteProjectionLocal_finiteHomology R S [a, a, 0] K hK p) :=
  finiteProjection_chainEuler_finsum R S [a, a, 0] K hK

omit [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R S] in
/-- The empty total's finite homology is derived from the actual unit isomorphism. -/
theorem emptyTotalFinite (K : ChainComplex (ModuleCat S) ℕ) (hK : FiniteHomology K) :
    FiniteHomology (finiteProjectionTotal R S [] K) := by
  let e : finiteProjectionTotal R S [] K ≅ K := λ_ K
  exact hK.of_iso (fun n =>
    (HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.down ℕ) n).mapIso e.symm)

/-- The empty-list weighted formula agrees with the previously established
actual finite-algebra fiber Euler, rather than an assumed numerical comparison. -/
theorem emptyWeightedEuler (K : ChainComplex (ModuleCat S) ℕ) (hK : FiniteHomology K) :
    (∑ᶠ p : MaximalSpectrum S, (Module.finiteAlgebraResidueDegree R S p : ℤ) *
        chainEuler (finiteProjectionLocal R S [] K p)
          (finiteProjectionLocal_finiteHomology R S [] K (emptyTotalFinite R S K hK) p)) =
      finiteAlgebraFiberEuler R S K (fun n => (-1) ^ n) hK := by
  rw [← finiteProjection_chainEuler_finsum R S [] K (emptyTotalFinite R S K hK),
    ← homologyEuler_finiteAlgebra_eq_fiberEuler R S K (fun n => (-1) ^ n) hK]
  exact homologyEuler_eq_of_quasiIso (λ_ (finiteAlgebraRestrictedComplex R S K)).hom
    (fun n => (-1) ^ n) _ _

omit [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R S] in
/-- A genuine contractible total has finite homology even when the original
complex is entirely unrestricted in length, support and homology. -/
theorem contractibleTotalFinite (s : List R) (K : ChainComplex (ModuleCat S) ℕ) :
    FiniteHomology (finiteProjectionTotal R S s
      (HomologicalComplex.tensorObj (singleComplex S 1) K)) :=
  finiteHomology_of_identity_homotopy _ (koszulUnitTensorHomotopy K (s.map (algebraMap R S)))

/-- The projection theorem consumes that constructed finite-homology evidence,
without an external boundedness or finite-length premise on any original term. -/
theorem unrestrictedContractibleProjection (s : List R) (K : ChainComplex (ModuleCat S) ℕ) :
    chainEuler (finiteProjectionSource R S s
        (HomologicalComplex.tensorObj (singleComplex S 1) K))
        (finiteProjectionSource_finiteHomology R S s _ (contractibleTotalFinite R S s K)) =
      ∑ᶠ p : MaximalSpectrum S, (Module.finiteAlgebraResidueDegree R S p : ℤ) *
        chainEuler (finiteProjectionLocal R S s
          (HomologicalComplex.tensorObj (singleComplex S 1) K) p)
          (finiteProjectionLocal_finiteHomology R S s _ (contractibleTotalFinite R S s K) p) :=
  finiteProjection_chainEuler_finsum R S s _ (contractibleTotalFinite R S s K)

section Residue

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]

/-- At a nonzero element of the maximal ideal of a local domain, the actual
residue module is not flat: it has genuine nonzero scalar torsion. -/
theorem residueNotFlat (a : A) (ha : a ≠ 0) (hm : a ∈ IsLocalRing.maximalIdeal A) :
    ¬ Module.Flat A (IsLocalRing.ResidueField A) := by
  intro h
  let := h
  have hz : a • (1 : IsLocalRing.ResidueField A) = 0 := by
    rw [Algebra.smul_def, mul_one]
    exact (IsLocalRing.residue_eq_zero_iff a).mpr hm
  exact one_ne_zero ((smul_eq_zero_iff_right ha).mp hz)

variable [IsNoetherianRing A]

omit [IsDomain A] in
/-- The finite residue quotient is a valid projection input without flatness. -/
theorem residueProjection (s : List A)
    (K : ChainComplex (ModuleCat (IsLocalRing.ResidueField A)) ℕ)
    (hK : FiniteHomology (finiteProjectionTotal A (IsLocalRing.ResidueField A) s K)) :
    chainEuler (finiteProjectionSource A (IsLocalRing.ResidueField A) s K)
        (finiteProjectionSource_finiteHomology A (IsLocalRing.ResidueField A) s K hK) =
      ∑ᶠ p : MaximalSpectrum (IsLocalRing.ResidueField A),
        (Module.finiteAlgebraResidueDegree A (IsLocalRing.ResidueField A) p : ℤ) *
          chainEuler (finiteProjectionLocal A (IsLocalRing.ResidueField A) s K p)
            (finiteProjectionLocal_finiteHomology A (IsLocalRing.ResidueField A) s K hK p) :=
  finiteProjection_chainEuler_finsum A (IsLocalRing.ResidueField A) s K hK

end Residue

variable (k : Type u) [Field k]

/-- Both branches over the same base point contribute to the actual odd-degree
localized Koszul sum, whose value is -2 rather than an unsigned or single-point length. -/
theorem twoBranchOddWeightedEuler :
    let K := (HomologicalComplex.single (ModuleCat (k × k)) (ComplexShape.down ℕ) 1).obj
      (ModuleCat.of (k × k) (k × k))
    let hK := finiteHomology_single (ComplexShape.down ℕ) 1 _
      (Motivic.MotivicTest.LengthEulerFiniteAlgebra.twoBranchFiniteLength k)
    (∑ᶠ p : MaximalSpectrum (k × k),
      (Module.finiteAlgebraResidueDegree k (k × k) p : ℤ) *
        chainEuler (finiteProjectionLocal k (k × k) [] K p)
          (finiteProjectionLocal_finiteHomology k (k × k) [] K
            (emptyTotalFinite k (k × k) K hK) p)) = -2 := by
  dsimp only
  rw [emptyWeightedEuler]
  exact Motivic.MotivicTest.LengthEulerFiniteAlgebra.twoBranchOddEuler k

end MotivicTest.KoszulFiniteProjectionEuler
