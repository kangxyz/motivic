module
import Motivic.Aglib.RingTheory.Bertini.QuadraticResidueIncidence
import Lean.Util.CollectAxioms

/-! # Original affine generators supply the incidence cotangent quotient -/
open Module TensorProduct _root_.MvPolynomial KaehlerDifferential LinearMap

example (k R K : Type) [CommRing k] [CommRing R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra.EssFiniteType k R]
    {σ : Type} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (a b : σ → K) (hab : a ≠ b)
    (d : ℕ) (hd : Module.finrank K (K ⊗[R] Ω[R⁄k]) = d + 1)
    (w : Fin d → K) (i₀ : Fin d) (hw : w i₀ = 1) :
    (2 * d + 1) +
      Module.finrank K (normalizedJetConstraints (quadraticResidueJet k R K g a b) w).ker =
        Module.finrank K (Fin d → restrictTotalDegree σ K 2) :=
  finrank_ker_quadraticResidueIncidence k R K g hg a b hab d hd w i₀ hw

open Lean in
run_cmd do
  for name in #[``span_generator_differentials, ``span_residue_generator_differentials,
      ``residueGeneratorGradient_surjective, ``quadraticResidueJet_surjective,
      ``finrank_ker_quadraticResidueIncidence] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual residue incidence: standard foundations only."
