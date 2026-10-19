/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.FiniteLength.FiniteAlgebraFiber
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Points of a localized finite algebra

For a finite algebra `A → B` and a prime `p` of `A`, the relevant algebra is
`Aₚ ⊗[A] B`, before quotienting by the base maximal ideal. Its maximal ideals
correspond to the points of `Spec B` above `p`. Localizing this algebra again
recovers the localization of `B` at the corresponding source prime.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace PrimeSpectrum.FiniteFiber

universe u v

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
  (p : PrimeSpectrum A)

/-- The actual finite algebra over the target local ring, retaining base infinitesimals. -/
abbrev localAlgebra := Localization.AtPrime p.asIdeal ⊗[A] B

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The tensor algebra is the localization of the source ring away from the base prime. -/
def localAlgebraEquiv :
    localAlgebra A B p ≃ₐ[Localization.AtPrime p.asIdeal]
      Localization (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl) :=
  Localization.tensorRightAlgEquiv p.asIdeal.primeCompl B

/-- The localization comparison commutes with the source ring map. -/
@[simp]
theorem localAlgebraEquiv_one_tmul (b : B) :
    localAlgebraEquiv A B p (1 ⊗ₜ[A] b) =
      algebraMap B (Localization (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl)) b :=
  Localization.tensorRightAlgEquiv_apply_one_tmul p.asIdeal.primeCompl b

/-- The localization comparison commutes with the target local ring map. -/
@[simp]
theorem localAlgebraEquiv_tmul_one (a : Localization.AtPrime p.asIdeal) :
    localAlgebraEquiv A B p (a ⊗ₜ[A] 1) =
      algebraMap (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl)) a :=
  (localAlgebraEquiv A B p).commutes a

variable [Module.Finite A B]

/-- Base change preserves finiteness of the whole semilocal algebra. -/
theorem localAlgebra_finite :
    Module.Finite (Localization.AtPrime p.asIdeal) (localAlgebra A B p) :=
  inferInstance

/-- A maximal ideal of the localized finite algebra contracts to the original target prime. -/
theorem maximal_under_base (q : MaximalSpectrum (localAlgebra A B p)) :
    q.asIdeal.under A = p.asIdeal := by
  rw [← Ideal.under_under (B := Localization.AtPrime p.asIdeal),
    Module.finiteAlgebra_maximal_under (Localization.AtPrime p.asIdeal)
      (localAlgebra A B p) q,
    IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime p.asIdeal) p.asIdeal]

/-- The source point determined by a maximal ideal lies over the specified target point. -/
def sourcePoint (q : MaximalSpectrum (localAlgebra A B p)) :
    {x : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) x = p} :=
  ⟨PrimeSpectrum.comap (algebraMap B (localAlgebra A B p)) q.toPrimeSpectrum,
    PrimeSpectrum.ext (by
      change (q.asIdeal.under B).under A = p.asIdeal
      rw [Ideal.under_under, maximal_under_base])⟩

/-- A source point over `p` extends to a maximal ideal of the whole localized algebra. -/
def maximalPoint
    (x : {x : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) x = p}) :
    MaximalSpectrum (localAlgebra A B p) := by
  letI : x.1.asIdeal.LiesOver p.asIdeal := ⟨congrArg PrimeSpectrum.asIdeal x.2.symm⟩
  let J := x.1.asIdeal.map (algebraMap B (localAlgebra A B p))
  have hdisj := Ideal.disjoint_primeCompl_of_liesOver x.1.asIdeal p.asIdeal
  letI : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl) (localAlgebra A B p)
    x.1.asIdeal x.1.isPrime hdisj
  letI : J.LiesOver (p.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal))) :=
    IsLocalization.liesOver_of_isPrime_of_disjoint p.asIdeal.primeCompl
      (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl) p.asIdeal hdisj
  refine ⟨J, Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := Localization.AtPrime p.asIdeal)
    J ?_⟩
  rw [← Ideal.over_def J (p.asIdeal.map (algebraMap A (Localization.AtPrime p.asIdeal)))]
  infer_instance

/-- Maximal points of the localized finite algebra are exactly source points over `p`. -/
def maximalSpectrumEquivFiber :
    MaximalSpectrum (localAlgebra A B p) ≃
      {x : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) x = p} where
  toFun := sourcePoint A B p
  invFun := maximalPoint A B p
  left_inv q := MaximalSpectrum.ext <|
    IsLocalization.map_under (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl)
      (localAlgebra A B p) q.asIdeal
  right_inv x := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    have : x.1.asIdeal.LiesOver p.asIdeal := ⟨congrArg PrimeSpectrum.asIdeal x.2.symm⟩
    exact IsLocalization.under_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl) (localAlgebra A B p) x.1.isPrime
      (Ideal.disjoint_primeCompl_of_liesOver x.1.asIdeal p.asIdeal)

/-- The source-ideal square is literal contraction along `B → Aₚ ⊗[A] B`. -/
@[simp]
theorem maximalSpectrumEquivFiber_asIdeal (q : MaximalSpectrum (localAlgebra A B p)) :
    (maximalSpectrumEquivFiber A B p q).1.asIdeal = q.asIdeal.under B := rfl

/-- The inverse point comparison is literal extension along the same localization map. -/
@[simp]
theorem maximalSpectrumEquivFiber_symm_asIdeal
    (x : {x : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) x = p}) :
    ((maximalSpectrumEquivFiber A B p).symm x).asIdeal =
      x.1.asIdeal.map (algebraMap B (localAlgebra A B p)) := rfl

/-- A further localization is the source localization, as a `B`-algebra.
This does not assert that this individual local ring is finite over `Aₚ`. -/
def sourceLocalizationEquiv (q : MaximalSpectrum (localAlgebra A B p)) :
    Localization.AtPrime q.asIdeal ≃ₐ[B]
      Localization.AtPrime (sourcePoint A B p q).1.asIdeal := by
  change Localization.AtPrime q.asIdeal ≃ₐ[B] Localization.AtPrime (q.asIdeal.under B)
  letI : IsLocalization.AtPrime (Localization.AtPrime q.asIdeal) (q.asIdeal.under B) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl) _ q.asIdeal
  exact IsLocalization.algEquiv (q.asIdeal.under B).primeCompl _ _

/-- The source-localization comparison respects the original source ring map. -/
theorem sourceLocalizationEquiv_algebraMap (q : MaximalSpectrum (localAlgebra A B p)) (b : B) :
    sourceLocalizationEquiv A B p q (algebraMap B (Localization.AtPrime q.asIdeal) b) =
      algebraMap B (Localization.AtPrime (sourcePoint A B p q).1.asIdeal) b :=
  (sourceLocalizationEquiv A B p q).commutes b

/-- The actual map of prime localizations from the target to the source. -/
def sourceLocalMap (q : MaximalSpectrum (localAlgebra A B p)) :
    Localization.AtPrime p.asIdeal →+* Localization.AtPrime (sourcePoint A B p q).1.asIdeal :=
  Localization.localRingHom p.asIdeal (sourcePoint A B p q).1.asIdeal (algebraMap A B)
    (congrArg PrimeSpectrum.asIdeal (sourcePoint A B p q).2.symm)

instance sourceLocalMap_isLocalHom (q : MaximalSpectrum (localAlgebra A B p)) :
    IsLocalHom (sourceLocalMap A B p q) :=
  Localization.isLocalHom_localRingHom _ _ _ _

/-- The source-localization equivalence commutes with the actual target-local map. -/
theorem sourceLocalizationEquiv_base_square (q : MaximalSpectrum (localAlgebra A B p)) :
    (sourceLocalizationEquiv A B p q).toRingHom.comp
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) =
      sourceLocalMap A B p q := by
  symm
  apply Localization.localRingHom_unique
  intro a
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]
  rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime q.asIdeal)]
  exact (sourceLocalizationEquiv A B p q).commutes ((algebraMap A B) a)

/-- The scalar map from the target local ring to a source localization is local. -/
instance sourceLocalization_base_isLocalHom (q : MaximalSpectrum (localAlgebra A B p)) :
    IsLocalHom (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal)) := by
  have : IsLocalHom ((sourceLocalizationEquiv A B p q).toRingHom.comp
      (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))) := by
    rw [sourceLocalizationEquiv_base_square]
    infer_instance
  exact isLocalHom_of_comp _ (sourceLocalizationEquiv A B p q).toRingHom

/-- The source residue field comparison is induced by the actual local-ring equivalence. -/
def sourceResidueEquiv (q : MaximalSpectrum (localAlgebra A B p)) :
    q.asIdeal.ResidueField ≃+* (sourcePoint A B p q).1.asIdeal.ResidueField :=
  IsLocalRing.ResidueField.mapEquiv (sourceLocalizationEquiv A B p q).toRingEquiv

/-- The residue comparison respects reduction of every element of the source local ring. -/
@[simp]
theorem sourceResidueEquiv_residue (q : MaximalSpectrum (localAlgebra A B p))
    (z : Localization.AtPrime q.asIdeal) :
    sourceResidueEquiv A B p q (IsLocalRing.residue _ z) =
      IsLocalRing.residue _ (sourceLocalizationEquiv A B p q z) := rfl

/-- The residue comparison commutes with the target residue action.
The bottom arrow is induced by the actual localized source ring map. -/
theorem sourceResidueEquiv_base_square (q : MaximalSpectrum (localAlgebra A B p)) :
    (sourceResidueEquiv A B p q).toRingHom.comp
        (IsLocalRing.ResidueField.map
          (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal))) =
      IsLocalRing.ResidueField.map (sourceLocalMap A B p q) := by
  apply RingHom.ext
  intro a
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective a
  change IsLocalRing.residue _
      (sourceLocalizationEquiv A B p q
        (algebraMap (Localization.AtPrime p.asIdeal) (Localization.AtPrime q.asIdeal) a)) =
    IsLocalRing.residue _ (sourceLocalMap A B p q a)
  exact congrArg (IsLocalRing.residue _)
    (RingHom.congr_fun (sourceLocalizationEquiv_base_square A B p q) a)

/-- The actual point fiber is finite without requiring its individual local rings to be finite. -/
theorem pointFiber_finite :
    Finite {x : PrimeSpectrum B // PrimeSpectrum.comap (algebraMap A B) x = p} := by
  have := Module.finiteAlgebra_maximalSpectrum_finite
    (Localization.AtPrime p.asIdeal) (localAlgebra A B p)
  exact (maximalSpectrumEquivFiber A B p).finite_iff.mp inferInstance

end PrimeSpectrum.FiniteFiber
