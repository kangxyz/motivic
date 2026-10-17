module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticJetParameters
public import Motivic.Aglib.RingTheory.Bertini.NormalizedIncidenceConstraints
public import Motivic.Aglib.RingTheory.Kaehler.ResidueGeneratorGradient

/-! # Quadratic incidence constraints on the original affine cotangent fiber

The ambient coordinates are the given algebra generators. The cotangent quotient
is derived from them, so no separately selected smooth coordinate system is used.
-/
@[expose] public noncomputable section
open Module TensorProduct MvPolynomial KaehlerDifferential LinearMap
universe u v w z
namespace KaehlerDifferential
variable (k : Type u) (R : Type v) (K : Type w)
  [CommRing k] [CommRing R] [Field K] [Algebra k R] [Algebra R K]
  {σ : Type z} [Fintype σ]

/-- Value difference and the actual cotangent gradient from the fixed embedding. -/
def quadraticResidueJet (g : σ → R) (a b : σ → K) :
    restrictTotalDegree σ K 2 →ₗ[K] K × (K ⊗[R] Ω[R⁄k]) :=
  ((LinearMap.id : K →ₗ[K] K).prodMap (residueGeneratorGradient k R K g)).comp
    (quadraticJetParameters a b)

theorem quadraticResidueJet_surjective (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (a b : σ → K) (hab : a ≠ b) :
    Function.Surjective (quadraticResidueJet k R K g a b) := by
  rintro ⟨c, v⟩
  obtain ⟨w, hw⟩ := residueGeneratorGradient_surjective k R K g hg v
  obtain ⟨f, hf⟩ := quadraticJetParameters_surjective a b hab (c, w)
  refine ⟨f, ?_⟩
  change ((LinearMap.id : K →ₗ[K] K).prodMap (residueGeneratorGradient k R K g))
    (quadraticJetParameters a b f) = (c, v)
  rw [hf]
  exact Prod.ext rfl hw

/-- Exact independent-equation count on the normalized bad-fiber chart for an
actual affine embedding and its actual cotangent fiber. -/
theorem finrank_ker_quadraticResidueIncidence [Algebra.EssFiniteType k R]
    (g : σ → R) (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (a b : σ → K) (hab : a ≠ b) (d : ℕ)
    (hd : Module.finrank K (K ⊗[R] Ω[R⁄k]) = d + 1)
    (w : Fin d → K) (i₀ : Fin d) (hw : w i₀ = 1) :
    (2 * d + 1) +
      Module.finrank K (normalizedJetConstraints (quadraticResidueJet k R K g a b) w).ker =
        Module.finrank K (Fin d → restrictTotalDegree σ K 2) := by
  have h := finrank_ker_normalizedJetConstraints _
    (quadraticResidueJet_surjective k R K g hg a b hab) w i₀ hw
  simpa [hd, two_mul, Nat.add_assoc] using h

end KaehlerDifferential
