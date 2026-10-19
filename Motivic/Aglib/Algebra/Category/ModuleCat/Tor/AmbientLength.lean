/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.Ambient
public import Motivic.Aglib.Algebra.Homology.LengthEuler.Basic

/-!
# Actual ambient Tor length and finite Euler comparison

When the ambient map is surjective, the constructed ambient Tor isomorphism
preserves the actual module length over the two different rings. This
transfers genuine finite-length support in both directions and identifies
finite signed Euler sums. Infinite length is not converted to an integer;
finite support is transferred from an actual input proof, not assumed as a
universal property of the affine-coordinate Tor modules.
-/

@[expose] public section

open CategoryTheory _root_.HomologicalComplex.ModuleLengthEuler
open scoped TensorProduct

universe u

section
open _root_.ModuleCat.TorComparison

/-- Literal restriction along a surjective ring map preserves module length. -/
theorem _root_.ModuleCat.length_restrictScalars_of_surjective
    {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (M : ModuleCat.{u} S) :
    Module.length R ((ModuleCat.restrictScalars f).obj M) = Module.length S M := by
  let := f.toAlgebra
  let : IsScalarTower R S ((ModuleCat.restrictScalars f).obj M) := ⟨fun r s x ↦ by
    change (f r * s) • x = f r • (s • x)
    exact mul_smul (f r) s x⟩
  exact Module.length_eq_of_surjective (R := S)
    (M := (ModuleCat.restrictScalars f).obj M) hf

variable {k U V Q : Type u} [Field k] [CommRing U] [CommRing V] [CommRing Q]
  [Algebra k U] [Algebra k V]

/-- The actual ambient Tor family, in coefficient-first exterior-module order. -/
noncomputable abbrev _root_.ModuleCat.TorComparison.ambientTorFamily (μ : U ⊗[k] V →+* Q)
    (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) (n : ℕ) :=
  ((Tor (ModuleCat (U ⊗[k] V)) n).obj (ExteriorModule.obj k U V M N)).obj
    ((ModuleCat.restrictScalars μ).obj (ModuleCat.of Q Q))

/-- The actual Tor family of the two induced factor scalar extensions. -/
noncomputable abbrev _root_.ModuleCat.TorComparison.extendedTorFamily (μ : U ⊗[k] V →+* Q)
    (M : ModuleCat.{u} U) (N : ModuleCat.{u} V) (n : ℕ) :=
  ((Tor (ModuleCat Q) n).obj
    ((ModuleCat.extendScalars (MixedBase.leftMap k U V Q μ)).obj M)).obj
      ((ModuleCat.extendScalars (MixedBase.rightMap k U V Q μ)).obj N)

variable (μ : U ⊗[k] V →+* Q) (hμ : Function.Surjective μ)
  (hleft : (MixedBase.leftMap k U V Q μ).Flat)
  (hright : (MixedBase.rightMap k U V Q μ).Flat)
  (M : ModuleCat.{u} U) (N : ModuleCat.{u} V)

include hμ hleft hright

/-- Surjectivity of the ambient quotient compares actual Tor lengths in each degree. -/
theorem _root_.ModuleCat.TorComparison.ambientTor_length (n : ℕ) :
    Module.length (U ⊗[k] V) (ambientTorFamily μ M N n) =
      Module.length Q (extendedTorFamily μ M N n) :=
  (ambientTorIso μ hleft hright M N n).toLinearEquiv.length_eq.trans
    (_root_.ModuleCat.length_restrictScalars_of_surjective μ hμ _)

/-- Genuine finite length and finite degree support transfer across the actual comparison. -/
theorem _root_.ModuleCat.TorComparison.ambientTor_finiteLengthSupport_iff :
    FiniteLengthSupport (ambientTorFamily μ M N) ↔
      FiniteLengthSupport (extendedTorFamily μ M N) := by
  have hlen : (fun n ↦ Module.length (U ⊗[k] V) (ambientTorFamily μ M N n)) =
      fun n ↦ Module.length Q (extendedTorFamily μ M N n) :=
    funext (ambientTor_length μ hμ hleft hright M N)
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro n
      rw [← ambientTor_length μ hμ hleft hright M N n]
      exact h.finite_length n
    · simpa only [hlen] using h.finite_support
  · intro h
    refine ⟨?_, ?_⟩
    · intro n
      rw [ambientTor_length μ hμ hleft hright M N n]
      exact h.finite_length n
    · simpa only [hlen] using h.finite_support

/-- Every genuine finite signed ambient Tor Euler sum equals the extended-ring sum. -/
theorem _root_.ModuleCat.TorComparison.ambientTor_signedLengthSum (sign : ℕ → ℤ)
    (h : FiniteLengthSupport (ambientTorFamily μ M N)) :
    signedLengthSum (ambientTorFamily μ M N) sign h =
      signedLengthSum (extendedTorFamily μ M N) sign
        ((ambientTor_finiteLengthSupport_iff μ hμ hleft hright M N).mp h) := by
  unfold signedLengthSum
  apply finsum_congr
  intro n
  simp only [integerLength, ambientTor_length μ hμ hleft hright M N n]

end
