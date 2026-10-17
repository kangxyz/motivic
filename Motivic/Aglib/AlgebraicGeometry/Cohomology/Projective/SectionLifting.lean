/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.SerreVanishing

/-!
# Lifting sections of coherent quotients after projective twisting

The restriction kernel is the actual categorical kernel, not an invertible ideal.
This result is on explicit polynomial projective space over a Noetherian ring.
It makes no assertion that a merely proper scheme has a projective embedding.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u
namespace AlgebraicGeometry.Scheme.Cohomology

/-- A short exact module sequence whose actual kernel has vanishing H¹ is
surjective on actual global sections. -/
theorem globalSections_surjective_of_h1_zero (X : Scheme.{u})
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) 1)] :
    Function.Surjective (S.g.app ⊤) := by
  intro s
  exact Sheaf.H.longSequence_equiv₀_exact₃.{u + 1}
    (moduleCoefficientSequence_shortExact X S hS) Limits.isTerminalTop s
    (by
      exact @Subsingleton.elim (Sheaf.H.{u + 1} (moduleAddSheaf X S.X₁) 1) _ _ _)

/-- Every section of every sufficiently positive twist of a coherent quotient
lifts globally. The bound is obtained from Serre vanishing of the actual kernel.
No local freeness or invertibility hypothesis is imposed on that kernel. -/
theorem projective_coherentQuotient_eventually_sections_surjective
    (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u)
    (n : ℕ) (e : ι ≃ Fin (n + 1))
    {M Q : (ProjectiveSpace R ι).Modules}
    (hM : affineLocallyFiniteType (ProjectiveSpace R ι) M)
    (hQ : affineLocallyFiniteType (ProjectiveSpace R ι) Q)
    (π : M ⟶ Q) [Epi π] :
    ∃ B : ℕ, ∀ d : ℤ, (B : ℤ) ≤ d →
      Function.Surjective
        (((moduleTensorLeftFunctor (ProjectiveSpace R ι)
          (twistingSheaf R ι d)).map π).app ⊤) := by
  let := Fintype.ofEquiv (Fin (n + 1)) e.symm
  have hK : affineLocallyFiniteType (ProjectiveSpace R ι) (kernel π) :=
    (affineLocallyFiniteType (ProjectiveSpace R ι)).prop_kernel π hM hQ
  obtain ⟨B, hB⟩ := projectiveSerreVanishing R ι n e (kernel π) hK
  refine ⟨B, fun d hd => ?_⟩
  let T := moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)
  let S := (ShortComplex.kernelSequence π).map T
  have hS : S.ShortExact := tensor_shortExact_finiteLocallyFree
    (twistingSheaf R ι d) (ShortComplex.kernelSequence π)
    { exact := ShortComplex.kernelSequence_exact π, epi_g := ‹Epi π› }
  let : Subsingleton (Sheaf.H.{u + 1} (moduleAddSheaf (ProjectiveSpace R ι) S.X₁) 1) :=
    hB d hd 1 (by decide)
  exact globalSections_surjective_of_h1_zero (ProjectiveSpace R ι) S hS

end AlgebraicGeometry.Scheme.Cohomology
