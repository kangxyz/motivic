/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootScalarBranches
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity

/-!
# Actual local lengths of repeated polynomial factors

The localization of the original polynomial quotient at a monic irreducible
factor is the quotient of the polynomial discrete valuation ring by the
original polynomial. Its length is exactly the exponent of that factor,
including all repeated-factor multiplicities.
-/

@[expose] public noncomputable section

open Polynomial UniqueFactorizationMonoid

namespace AdjoinRoot

variable {k : Type*} [Field k]

instance factorIdeal_isMaximal (p : k[X]) (q : IrreducibleBranch p) :
    (Ideal.span {q.val.val}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible q.val.property.2

/-- The polynomial discrete valuation ring belonging to the literal factor. -/
abbrev FactorLocalRing (p : k[X]) (q : IrreducibleBranch p) :=
  Localization.AtPrime (Ideal.span {q.val.val})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Localizing the original quotient is the same as taking its original
principal quotient in the polynomial local ring. -/
def branchLocalizationQuotientEquiv (p : k[X]) (q : IrreducibleBranch p) :
    Localization.AtPrime (branchMaximal p q).asIdeal ≃+*
      FactorLocalRing p q ⧸ (Ideal.span {p}).map (algebraMap k[X] (FactorLocalRing p q)) := by
  letI : Algebra k[X] (AdjoinRoot p) :=
    inferInstanceAs (Algebra k[X] (k[X] ⧸ Ideal.span {p}))
  letI : Algebra (AdjoinRoot p)
      (FactorLocalRing p q ⧸ (Ideal.span {p}).map
        (algebraMap k[X] (FactorLocalRing p q))) :=
    inferInstanceAs (Algebra (k[X] ⧸ Ideal.span {p})
      (FactorLocalRing p q ⧸ (Ideal.span {p}).map
        (algebraMap k[X] (FactorLocalRing p q))))
  have hm : Algebra.algebraMapSubmonoid (AdjoinRoot p) (Ideal.span {q.val.val}).primeCompl =
      (branchMaximal p q).asIdeal.primeCompl := by
    change Submonoid.map (mk p) (Ideal.span {q.val.val}).primeCompl = _
    simpa only [branchMaximal_comap] using
      Ideal.map_primeCompl_comap_of_surjective (mk p) mk_surjective
        (branchMaximal p q).asIdeal
  letI : IsLocalization (branchMaximal p q).asIdeal.primeCompl
      (FactorLocalRing p q ⧸ (Ideal.span {p}).map
        (algebraMap k[X] (FactorLocalRing p q))) :=
    hm ▸ (inferInstanceAs
      (IsLocalization (Algebra.algebraMapSubmonoid (k[X] ⧸ Ideal.span {p})
        (Ideal.span {q.val.val}).primeCompl)
        (FactorLocalRing p q ⧸ (Ideal.span {p}).map
          (algebraMap k[X] (FactorLocalRing p q)))))
  exact (IsLocalization.algEquiv (branchMaximal p q).asIdeal.primeCompl
    (Localization.AtPrime (branchMaximal p q).asIdeal)
    (FactorLocalRing p q ⧸ (Ideal.span {p}).map
      (algebraMap k[X] (FactorLocalRing p q)))).toRingEquiv

instance factorLocalRing_isDiscreteValuationRing (p : k[X]) (q : IrreducibleBranch p) :
    IsDiscreteValuationRing (FactorLocalRing p q) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain k[X]
    (P := Ideal.span {q.val.val})
    (by simpa only [ne_eq, Ideal.span_singleton_eq_bot] using q.val.property.2.ne_zero) _

/-- In the polynomial local ring, the whole polynomial cuts out exactly the
power of the maximal ideal recorded by the factor's multiplicity. -/
theorem factorLocalRing_map_span (p : k[X]) (hp : p ≠ 0) (q : IrreducibleBranch p) :
    (Ideal.span {p}).map (algebraMap k[X] (FactorLocalRing p q)) =
      IsLocalRing.maximalIdeal (FactorLocalRing p q) ^ multiplicity q.val.val p := by
  have hf : FiniteMultiplicity q.val.val p :=
    FiniteMultiplicity.of_not_isUnit q.val.property.2.not_isUnit hp
  obtain ⟨g, hg, hqg⟩ := hf.exists_eq_pow_mul_and_not_dvd
  have hu : IsUnit (algebraMap k[X] (FactorLocalRing p q) g) := by
    apply (IsLocalization.AtPrime.isUnit_to_map_iff (FactorLocalRing p q)
      (Ideal.span {q.val.val}) g).mpr
    simpa only [Ideal.mem_primeCompl_iff, Ideal.mem_span_singleton] using hqg
  have hmax : Ideal.span {algebraMap k[X] (FactorLocalRing p q) q.val.val} =
      IsLocalRing.maximalIdeal (FactorLocalRing p q) := by
    simpa only [Ideal.map_span, Set.image_singleton] using
      IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {q.val.val})
        (FactorLocalRing p q)
  rw [Ideal.map_span, Set.image_singleton]
  calc
    _ = Ideal.span {algebraMap k[X] (FactorLocalRing p q)
        (q.val.val ^ multiplicity q.val.val p * g)} :=
      congrArg (fun a : k[X] => Ideal.span {algebraMap k[X] (FactorLocalRing p q) a}) hg
    _ = _ := by
      rw [map_mul, map_pow, Ideal.span_singleton_mul_right_unit hu,
        ← Ideal.span_singleton_pow, hmax]

private theorem self_length_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : Module.length R R = Module.length S S := by
  let := RingHomInvPair.of_ringEquiv e
  let := RingHomInvPair.symm (↑e : R →+* S) (e.symm : S →+* R)
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective e.toSemilinearEquiv.toLinearMap e.bijective)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual local ring of the original quotient has length equal to the
irreducible factor's multiplicity. No reducedness hypothesis is used. -/
theorem branch_local_length_eq_multiplicity (p : k[X]) (hp : p ≠ 0)
    (q : IrreducibleBranch p) :
    Module.length (Localization.AtPrime (branchMaximal p q).asIdeal)
      (Localization.AtPrime (branchMaximal p q).asIdeal) = (multiplicity q.val.val p : ℕ∞) := by
  have he := self_length_eq_of_ringEquiv
    (R := Localization.AtPrime (branchMaximal p q).asIdeal)
    (S := FactorLocalRing p q ⧸ (Ideal.span {p}).map
      (algebraMap k[X] (FactorLocalRing p q)))
    (branchLocalizationQuotientEquiv p q)
  rw [he, ← Module.length_eq_of_surjective Ideal.Quotient.mk_surjective,
    factorLocalRing_map_span p hp q]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal _ _

/-- The local length also agrees directly with the extended multiplicity. -/
theorem branch_local_length_eq_emultiplicity (p : k[X]) (hp : p ≠ 0)
    (q : IrreducibleBranch p) :
    Module.length (Localization.AtPrime (branchMaximal p q).asIdeal)
      (Localization.AtPrime (branchMaximal p q).asIdeal) = emultiplicity q.val.val p := by
  rw [branch_local_length_eq_multiplicity p hp q,
    (FiniteMultiplicity.of_not_isUnit q.val.property.2.not_isUnit hp).emultiplicity_eq_multiplicity]

open scoped Classical in
/-- Each factor's repeated occurrences in the normalized factor multiset are
exactly its length in the original polynomial quotient. -/
theorem branch_local_length_eq_count_normalizedFactors (p : k[X]) (hp : p.Monic)
    (q : IrreducibleBranch p) :
    Module.length (Localization.AtPrime (branchMaximal p q).asIdeal)
      (Localization.AtPrime (branchMaximal p q).asIdeal) =
        ((normalizedFactors p).count q.val.val : ℕ∞) := by
  classical
  rw [branch_local_length_eq_emultiplicity p hp.ne_zero q,
    UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors
      q.val.property.2 hp.ne_zero, q.val.property.1.normalize_eq_self]

end AdjoinRoot
