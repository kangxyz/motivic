module

public import Mathlib.RingTheory.Polynomial.GaussLemma
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Prime factorization of monic polynomials over normal domains

Only the fraction field is a unique factorization domain. The coefficient ring
is assumed integrally closed, not factorial.
-/

@[expose] public noncomputable section

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]

/-- A monic factor over the fraction field descends to the normal coefficient ring. -/
theorem exists_monic_factor_descent {p : R[X]} (hp : p.Monic)
    {g : (FractionRing R)[X]} (hg : g.Monic)
    (hd : g ∣ p.map (algebraMap R (FractionRing R))) :
    ∃ q : R[X], q.Monic ∧ q.map (algebraMap R (FractionRing R)) = g ∧ q ∣ p := by
  obtain ⟨q, hq⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd (FractionRing R) hp hd
  simp only [hg.leadingCoeff, C_1, mul_one] at hq
  have hm : q.Monic := monic_of_injective (IsFractionRing.injective R _) (hq ▸ hg)
  exact ⟨q, hm, hq, (map_dvd_map _ (IsFractionRing.injective R _) hm).mp (hq ▸ hd)⟩

omit [IsIntegrallyClosed R] in
/-- Primality of a monic polynomial descends from the fraction field. -/
theorem Monic.prime_of_prime_map_fractionRing {p : R[X]} (hp : p.Monic)
    (h : Prime (p.map (algebraMap R (FractionRing R)))) : Prime p := by
  refine ⟨hp.ne_zero, fun hu => h.not_isUnit (hu.map (mapRingHom _)), ?_⟩
  intro a b hab
  have hm := map_dvd (algebraMap R (FractionRing R)) hab
  rw [Polynomial.map_mul] at hm
  have hd := h.dvd_or_dvd hm
  exact hd.imp ((map_dvd_map _ (IsFractionRing.injective R _) hp).mp)
    ((map_dvd_map _ (IsFractionRing.injective R _) hp).mp)

/-- Every nonunit monic polynomial has a monic prime divisor over a normal domain. -/
theorem exists_monic_prime_factor_of_normal {p : R[X]} (hp : p.Monic) (hu : ¬ IsUnit p) :
    ∃ q : R[X], q.Monic ∧ Prime q ∧ q ∣ p := by
  have hu' : ¬ IsUnit (p.map (algebraMap R (FractionRing R))) :=
    fun h => hu (hp.isPrimitive.isUnit_iff_isUnit_map.mpr h)
  obtain ⟨g, hg, hi, hd⟩ := exists_monic_irreducible_factor _ hu'
  obtain ⟨q, hq, he, hdq⟩ := exists_monic_factor_descent hp hg hd
  exact ⟨q, hq, hq.prime_of_prime_map_fractionRing (he ▸ hi.prime), hdq⟩

/-- Monic polynomials with invertible constant term factor into monic prime
polynomials with invertible constant terms, even when the normal ring is not a UFD. -/
theorem exists_list_monic_prime_factors_of_normal (p : R[X]) (hp : p.Monic)
    (hu : IsUnit (p.coeff 0)) :
    ∃ l : List R[X], l.prod = p ∧
      ∀ q ∈ l, q.Monic ∧ Prime q ∧ IsUnit (q.coeff 0) := by
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hunit : IsUnit p
    · have he : p = 1 := hp.eq_one_of_isUnit hunit
      exact ⟨[], by simpa using he.symm, by simp⟩
    obtain ⟨q, hq, hprime, r, hr⟩ := exists_monic_prime_factor_of_normal hp hunit
    have hmr : r.Monic := hq.of_mul_monic_left (hr ▸ hp)
    have hc : IsUnit (q.coeff 0 * r.coeff 0) := by simpa [hr, mul_coeff_zero] using hu
    have hqr : q.natDegree + r.natDegree = p.natDegree := by
      rw [hr, natDegree_mul hq.ne_zero hmr.ne_zero]
    have hpos : 0 < q.natDegree := by
      by_contra h
      have hz : q.natDegree = 0 := by omega
      exact hprime.not_isUnit (hq.isUnit_iff.mpr (eq_one_of_monic_natDegree_zero hq hz))
    obtain ⟨l, hl, hf⟩ := ih r.natDegree (by omega) r hmr (isUnit_of_mul_isUnit_right hc) rfl
    refine ⟨q :: l, by simp [hl, ← hr], ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨hq, hprime, (isUnit_of_mul_isUnit_left hc)⟩
    · exact hf s hs

end Polynomial
