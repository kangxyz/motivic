/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientLength
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.AmbientLocalization

/-!
# Actual prime-local ambient Tor lengths and finite Euler sums

The genuine localized ambient Tor comparison and surjectivity of its literal
local ring map identify the two local module lengths. Finite length and
finite degree support are transferred from actual evidence, yielding equal
local finite signed Euler sums. This is a prime-local algebraic theorem;
identification with particular geometric incidence stalks is a further consumer.
-/

@[expose] public section

open CategoryTheory _root_.HomologicalComplex.ModuleLengthEuler
open scoped TensorProduct

universe u

namespace ModuleCat.TorComparison

variable {k U V Q : Type u} [Field k] [CommRing U] [CommRing V] [CommRing Q]
  [Algebra k U] [Algebra k V]

/-- Actual ambient Tor localized at the specified ambient prime. -/
noncomputable abbrev localizedAmbientTorFamily (μ : U ⊗[k] V →+* Q)
    (P : Ideal (U ⊗[k] V)) [P.IsPrime]
    (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) (n : ℕ) :=
  ModuleCat.of (Localization.AtPrime P)
    (LocalizedModule P.primeCompl (ambientTorFamily μ M N n))

/-- Actual extended-ring Tor localized at the specified extended-ring prime. -/
noncomputable abbrev localizedExtendedTorFamily (μ : U ⊗[k] V →+* Q)
    (q : Ideal Q) [q.IsPrime] (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) (n : ℕ) :=
  ModuleCat.of (Localization.AtPrime q)
    (LocalizedModule q.primeCompl (extendedTorFamily μ M N n))

variable (μ : U ⊗[k] V →+* Q) (hμ : Function.Surjective μ)
  (hleft : (MixedBase.leftMap k U V Q μ).Flat)
  (hright : (MixedBase.rightMap k U V Q μ).Flat)
  (P : Ideal (U ⊗[k] V)) [P.IsPrime] (q : Ideal Q) [q.IsPrime]
  (hPq : P = q.comap μ) (M : ModuleCat.{u} U) (N : ModuleCat.{u} V)

include hμ hleft hright hPq

/-- Actual corresponding local-ring Tor lengths agree degree by degree. -/
theorem ambientLocalTor_length (n : ℕ) :
    Module.length (Localization.AtPrime P) (localizedAmbientTorFamily μ P M N n) =
      Module.length (Localization.AtPrime q) (localizedExtendedTorFamily μ q M N n) :=
  (primeLocalizedAmbientTorIso μ hμ hleft hright P q hPq M N n).toLinearEquiv.length_eq.trans
    (length_restrictScalars_of_surjective (Localization.localRingHom P q μ hPq)
      (localRingHom_surjective μ hμ P q hPq) _)

/-- Local finite lengths and finite degree support transfer in both directions. -/
theorem ambientLocalTor_finiteLengthSupport_iff :
    FiniteLengthSupport (localizedAmbientTorFamily μ P M N) ↔
      FiniteLengthSupport (localizedExtendedTorFamily μ q M N) := by
  have hlen : (fun n ↦ Module.length (Localization.AtPrime P)
      (localizedAmbientTorFamily μ P M N n)) =
      fun n ↦ Module.length (Localization.AtPrime q)
        (localizedExtendedTorFamily μ q M N n) :=
    funext (ambientLocalTor_length μ hμ hleft hright P q hPq M N)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro n
      rw [← ambientLocalTor_length μ hμ hleft hright P q hPq M N n]
      exact h.finite_length n
    · simpa only [hlen] using h.finite_support
  · intro h
    refine ⟨?_, ?_⟩
    · intro n
      rw [ambientLocalTor_length μ hμ hleft hright P q hPq M N n]
      exact h.finite_length n
    · simpa only [hlen] using h.finite_support

/-- Actual finite signed Euler sums agree over the two corresponding local rings. -/
theorem ambientLocalTor_signedLengthSum (sign : ℕ → ℤ)
    (h : FiniteLengthSupport (localizedAmbientTorFamily μ P M N)) :
    signedLengthSum (localizedAmbientTorFamily μ P M N) sign h =
      signedLengthSum (localizedExtendedTorFamily μ q M N) sign
        ((ambientLocalTor_finiteLengthSupport_iff μ hμ hleft hright P q hPq M N).mp h) := by
  unfold signedLengthSum
  apply finsum_congr
  intro n
  simp only [integerLength, ambientLocalTor_length μ hμ hleft hright P q hPq M N n]

end ModuleCat.TorComparison
