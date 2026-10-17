module
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis

/-! # A nonzero parameter equation from generic incidence dimension bounds

A dominant affine parameter map would remain injective in one minimal-prime
quotient. Thus strict transcendence-degree bounds on those actual quotients
already give a single nonzero equation for the full incidence image, including
nonreduced incidence rings. No finite-component or reducedness premise is needed.
-/
@[expose] public noncomputable section
namespace Algebra
universe u
variable {k A B : Type u} [CommRing k] [CommRing A] [IsDomain A]
  [CommRing B] [Algebra k A] [Algebra k B]

/-- Generic-component dimension bounds rule out dominance of the actual parameter map. -/
theorem not_injective_of_minimal_quotient_trdeg_lt (f : A →ₐ[k] B)
    (h : ∀ P ∈ minimalPrimes B, trdeg k (B ⧸ P) < trdeg k A) :
    ¬ Function.Injective f := by
  intro hf
  have hbot : (⊥ : Ideal A) ∈ (Ideal.comap f.toRingHom (⊥ : Ideal B)).minimalPrimes := by
    rw [Ideal.comap_bot_of_injective f.toRingHom hf,
      Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton _
  obtain ⟨P, hP, hcomap⟩ :=
    Ideal.exists_minimalPrimes_comap_eq f.toRingHom (⊥ : Ideal A) hbot
  let q := (Ideal.Quotient.mkₐ k P).comp f
  have hq : Function.Injective q := by
    apply (RingHom.injective_iff_ker_eq_bot q.toRingHom).mpr
    have hk : RingHom.ker q.toRingHom = Ideal.comap f.toRingHom P := by
      ext x
      simp [q, Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem]
    exact hk.trans hcomap
  exact (not_le_of_gt (h P hP)) (trdeg_le_of_injective q hq)

/-- The resulting equation vanishes on the original full incidence ring itself. -/
theorem exists_nonzero_kernel_of_minimal_quotient_trdeg_lt (f : A →ₐ[k] B)
    (h : ∀ P ∈ minimalPrimes B, trdeg k (B ⧸ P) < trdeg k A) :
    ∃ a : A, a ≠ 0 ∧ f a = 0 := by
  have hn := not_injective_of_minimal_quotient_trdeg_lt f h
  by_contra he
  push Not at he
  apply hn
  exact (injective_iff_map_eq_zero f).mpr fun a ha => by
    by_contra hne
    exact he a hne ha

end Algebra
