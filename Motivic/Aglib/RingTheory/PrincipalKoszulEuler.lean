/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.KoszulCoefficientComplex
public import Motivic.Algebra.Homology.KoszulScalarRestrictionLength
public import Aglib.RingTheory.Multiplicity.PrincipalEuler.Basic

/-!
# Principal Euler expressions from actual singleton Koszul homology

The degree-zero quotient and degree-one kernel both contribute. No regularity
is imposed on the scalar or on the coefficient module. The ring-coefficient
comparison combines with the existing surjective scalar-restriction theorem
for the literal closed-immersion stalk map.
-/

@[expose] public noncomputable section

open CategoryTheory HomologicalComplex Motivic.LengthEuler

universe u

namespace Motivic.Koszul

variable {R : Type u} [CommRing R]

/-- Both homology terms of the original multiplication complex give exactly
the native principal Euler expression, retaining possible scalar torsion. -/
theorem singleComplex_chainEuler_eq_principalEuler
    (M : ModuleCat R) (t : R) (h : FiniteHomology (singleComplex M t)) :
    chainEuler (singleComplex M t) h = Module.principalEuler (N := M) t := by
  unfold chainEuler homologyEuler
  rw [signedLengthSum_eq_sum _ _ h {0, 1}]
  · simp only [Finset.sum_insert, Finset.mem_singleton, zero_ne_one, not_false_eq_true,
      Finset.sum_singleton, pow_zero, pow_one, one_mul, neg_one_mul,
      integerLength, (singleHomologyZeroIso M t).toLinearEquiv.length_eq,
      (singleHomologyOneIso M t).toLinearEquiv.length_eq, Module.principalEuler,
      sub_eq_add_neg]
  · intro n hn
    by_contra hn01
    have hn2 : 2 ≤ n := by
      change n ∉ ({0, 1} : Finset ℕ) at hn01
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn01
      omega
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn2
    have hz := (singleExactAt_add_two M t m).isZero_homology
    have : Subsingleton ((singleComplex M t).homology (2 + m)) := by
      simpa only [Nat.add_comm] using ModuleCat.subsingleton_of_isZero hz
    exact hn Module.length_eq_zero

/-- A singleton ring Koszul test equals its native principal Euler expression,
without deleting a possibly nonzero kernel contribution. -/
theorem singleton_ring_chainEuler_eq_principalEuler (t : R)
    (h : FiniteHomology (coefficientComplex (ModuleCat.of R R) [t])) :
    chainEuler (coefficientComplex (ModuleCat.of R R) [t]) h =
      Module.principalEuler (N := R) t := by
  have h' : FiniteHomology (chainComplex [t]) := by
    simpa only [coefficientComplex_ring] using h
  have hs := h'.of_iso (fun n =>
    (homologyFunctor (ModuleCat R) (ComplexShape.down ℕ) n).mapIso (singletonIso t))
  change chainEuler (chainComplex [t]) h' = _
  exact (homologyEuler_eq_of_quasiIso (singletonIso t).hom
    (fun n => (-1 : ℤ) ^ n) h' hs).trans
      (singleComplex_chainEuler_eq_principalEuler (ModuleCat.of R R) t hs)

/-- The original surjective scalar map transports the singleton test to the
native principal Euler expression of its target ring. This applies to the
literal surjective closed-immersion stalk map, with no flatness hypothesis. -/
theorem singleton_restrict_chainEuler_eq_principalEuler
    {S : Type u} [CommRing S] (f : R →+* S) (hf : Function.Surjective f) (t : R)
    (h : FiniteHomology
      (coefficientComplex ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) [t])) :
    chainEuler
        (coefficientComplex ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S)) [t]) h =
      Module.principalEuler (N := S) (f t) := by
  have hs := (coefficientRestrict_finiteLengthSupport_iff f hf (ModuleCat.of S S) [t]).mp h
  have he := coefficientRestrict_signedLengthSum f hf (ModuleCat.of S S) [t]
    (fun n => (-1 : ℤ) ^ n) h
  change chainEuler _ h = _
  exact he.trans (by
    simpa only [chainEuler, homologyEuler, List.map_cons, List.map_nil] using
      singleton_ring_chainEuler_eq_principalEuler (f t)
        (by simpa only [List.map_cons, List.map_nil] using hs))

end Motivic.Koszul
