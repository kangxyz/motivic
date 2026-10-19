module
public import Motivic.Aglib.RingTheory.NoetherNormalization.Differential.Projection
public import Motivic.Aglib.RingTheory.Kaehler.SimultaneousResidueCoordinates
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! # Finite projection on the original closed subscheme with prescribed tangent rank

Common original differential coordinates and every finite-elimination step are
joined. No polynomial presentation, relation, chart, or residue minor is supplied.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential _root_.MvPolynomial ParameterizedNoetherNormalization
universe u v w
namespace KaehlerDifferential

/-- A genuine finite projection on the entire closed quotient whose coordinate
differentials are independent at all selected residue fibers. -/
theorem exists_finite_closed_projection_independent_differentials
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (d r : ℕ) (hdr : d ≤ r)
    (htr : Algebra.trdeg k (R ⧸ I) ≤ d)
    {ι : Type v} [Finite ι] (K : ι → Type w)
    [∀ i, Field (K i)] [∀ i, Algebra R (K i)] [∀ i, Algebra k (K i)]
    [∀ i, IsScalarTower k R (K i)]
    (hdim : ∀ i, Module.finrank (K i) (K i ⊗[R] Ω[R⁄k]) = r) :
    ∃ ψ : MvPolynomial (Fin d) k →ₐ[k] R,
      ((Ideal.Quotient.mkₐ k I).comp ψ).Finite ∧ ∀ i,
        LinearIndependent (K i)
          (fun j => (1 ⊗ₜ[R] D k R (ψ (X j)) : K i ⊗[R] Ω[R⁄k])) := by
  classical
  obtain ⟨g, hg⟩ := exists_simultaneous_residue_differential_coordinates k R K r hdim
  let b (i : ι) := basisOfLinearIndependentOfCardEqFinrank'
    (fun j => (1 ⊗ₜ[R] D k R (g j) : K i ⊗[R] Ω[R⁄k])) (hg i)
      (by simpa using (hdim i).symm)
  have hb (i : ι) (j : Fin r) : b i j = 1 ⊗ₜ[R] D k R (g j) :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) j
  let T (i : ι) : R →ₗ[k] K i ⊗[R] Ω[R⁄k] :=
    ((TensorProduct.mk R (K i) Ω[R⁄k] 1).restrictScalars k).comp (D k R).toLinearMap
  let L (i : ι) (a : Fin d) : R →ₗ[k] K i :=
    ((b i).coord (Fin.castLE hdr a)).restrictScalars k |>.comp (T i)
  have hminor : ∀ i,
      Matrix.det (fun a c => L i a (g (Fin.castLE hdr c))) ≠ 0 := by
    intro i
    have heq : (fun a c => L i a (g (Fin.castLE hdr c))) =
        (1 : Matrix (Fin d) (Fin d) (K i)) := by
      ext a c
      change (b i).coord (Fin.castLE hdr a) (1 ⊗ₜ[R] D k R (g (Fin.castLE hdr c))) = _
      rw [← hb]
      simp [Basis.coord_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
    rw [heq, Matrix.det_one]
    exact one_ne_zero
  obtain ⟨ψ, hfin, hψ⟩ :=
    exists_finite_quotient_projection_preserving_differential_minors
      k R I d htr K L (fun j => g (Fin.castLE hdr j)) hminor
  refine ⟨ψ, hfin, fun i => ?_⟩
  let C : (K i ⊗[R] Ω[R⁄k]) →ₗ[K i] (Fin d → K i) :=
    LinearMap.pi fun a => (b i).coord (Fin.castLE hdr a)
  apply LinearIndependent.of_comp C
  exact Matrix.linearIndependent_cols_of_det_ne_zero (hψ i)

end KaehlerDifferential
