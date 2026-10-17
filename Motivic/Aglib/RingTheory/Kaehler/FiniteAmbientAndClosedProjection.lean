module
public import Motivic.Aglib.RingTheory.Kaehler.FiniteProjectionWithCotangentRank

/-! # One finite ambient projection with a finite prescribed bad locus

The last eliminated coordinate is retained as the relative curve coordinate.
Thus ambient finiteness and closed-boundary finiteness use the same functions.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential MvPolynomial ParameterizedNoetherNormalization
universe u v w
namespace KaehlerDifferential

/-- Finite ambient coordinates with full differential rank at every selected fiber. -/
theorem exists_finite_projection_independent_differentials
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (n : ℕ) (htr : Algebra.trdeg k R ≤ n)
    {ι : Type v} [Finite ι] (K : ι → Type w)
    [∀ i, Field (K i)] [∀ i, Algebra R (K i)] [∀ i, Algebra k (K i)]
    [∀ i, IsScalarTower k R (K i)]
    (hdim : ∀ i, Module.finrank (K i) (K i ⊗[R] Ω[R⁄k]) = n) :
    ∃ ψ : MvPolynomial (Fin n) k →ₐ[k] R, ψ.Finite ∧ ∀ i,
      LinearIndependent (K i)
        (fun j => (1 ⊗ₜ[R] D k R (ψ (X j)) : K i ⊗[R] Ω[R⁄k])) := by
  have ht : Algebra.trdeg k (R ⧸ (⊥ : Ideal R)) ≤ n := by
    rw [(AlgEquiv.quotientBot k R).trdeg_eq]
    exact htr
  obtain ⟨ψ, hf, hi⟩ := exists_finite_closed_projection_independent_differentials
    k R ⊥ n n le_rfl ht K hdim
  have he := AlgHom.Finite.of_surjective (AlgEquiv.quotientBot k R).toAlgHom
    (AlgEquiv.quotientBot k R).surjective
  have hh := he.comp hf
  have heq : (AlgEquiv.quotientBot k R).toAlgHom.comp
      ((Ideal.Quotient.mkₐ k (⊥ : Ideal R)).comp ψ) = ψ := by
    apply AlgHom.ext
    intro x
    exact AlgEquiv.quotientBot_mk (R := k) (ψ x)
  exact ⟨ψ, heq ▸ hh, hi⟩

/-- A single actual finite map to affine `(d+1)`-space whose last `d` coordinates
are finite on the unchanged closed quotient and independent at selected fibers. -/
theorem exists_finite_ambient_and_closed_projection_with_initial_chart
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (d : ℕ)
    (hR : Algebra.trdeg k R ≤ d + 1) (hI : Algebra.trdeg k (R ⧸ I) ≤ d)
    {ι : Type v} [Finite ι] (K : ι → Type w)
    [∀ i, Field (K i)] [∀ i, Algebra R (K i)] [∀ i, Algebra k (K i)]
    [∀ i, IsScalarTower k R (K i)]
    (hdim : ∀ i, Module.finrank (K i) (K i ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ ψ : MvPolynomial (Fin (d + 1)) k →ₐ[k] R, ψ.Finite ∧
      ((Ideal.Quotient.mkₐ k I).comp (ψ.comp (MvPolynomial.rename Fin.succ))).Finite ∧
      (∀ i, LinearIndependent (K i)
        (fun j : Fin d => (1 ⊗ₜ[R] D k R (ψ (X j.succ)) : K i ⊗[R] Ω[R⁄k]))) ∧
      ∃ θ : MvPolynomial (Fin (d + 1)) k →ₐ[k] R,
        ∃ E : MvPolynomial (Fin (d + 1)) k ≃ₐ[k] MvPolynomial (Fin (d + 1)) k,
          ψ = θ.comp E.toAlgHom ∧ ∀ i, LinearIndependent (K i)
            (fun j => (1 ⊗ₜ[R] D k R (θ (X j)) : K i ⊗[R] Ω[R⁄k])) := by
  classical
  obtain ⟨θ, hθ, hdiff⟩ := exists_finite_projection_independent_differentials
    k R (d + 1) (by simpa using hR) K hdim
  let b (i : ι) := basisOfLinearIndependentOfCardEqFinrank'
    (fun j => (1 ⊗ₜ[R] D k R (θ (X j)) : K i ⊗[R] Ω[R⁄k])) (hdiff i)
      (by simpa using (hdim i).symm)
  have hb (i : ι) (j : Fin (d + 1)) : b i j = 1 ⊗ₜ[R] D k R (θ (X j)) :=
    congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' _ _ _) j
  let T (i : ι) : R →ₗ[k] K i ⊗[R] Ω[R⁄k] :=
    ((TensorProduct.mk R (K i) Ω[R⁄k] 1).restrictScalars k).comp (D k R).toLinearMap
  let L (i : ι) (a : Fin d) :=
    (((b i).coord a.succ).restrictScalars k).comp ((T i).comp θ.toLinearMap)
  have hminor : ∀ i, Matrix.det (fun a c : Fin d => L i a (X c.succ)) ≠ 0 := by
    intro i
    have heq : (fun a c : Fin d => L i a (X c.succ)) =
        (1 : Matrix (Fin d) (Fin d) (K i)) := by
      ext a c
      change (b i).coord a.succ (1 ⊗ₜ[R] D k R (θ (X c.succ))) = _
      rw [← hb]
      simp [Basis.coord_apply, Matrix.one_apply, Finsupp.single_apply, eq_comm]
    rw [heq, Matrix.det_one]
    exact one_ne_zero
  let q := (Ideal.Quotient.mkₐ k I).comp θ
  have hq : q.Finite := (AlgHom.Finite.of_surjective (Ideal.Quotient.mkₐ k I)
    (Ideal.Quotient.mkₐ_surjective k I)).comp hθ
  obtain ⟨f, hf, hIf⟩ := exists_nonzero_kernel_relation_of_trdeg_le q hI (Nat.lt_succ_self d)
  obtain ⟨c, _, hfin, hminor'⟩ := exists_finite_projection_preserving_differential_minors
    f (RingHom.ker q) hf hIf K L (fun _ => id) hminor
  let E := (coordinateChange f c).symm
  let ψ := θ.comp E.toAlgHom
  have hψ : ψ.Finite := hθ.comp (AlgHom.Finite.of_surjective E.toAlgHom E.surjective)
  let qbar := Ideal.kerLiftAlg q
  have hfactor : qbar.comp (Ideal.Quotient.mkₐ k (RingHom.ker q)) = q := by
    apply AlgHom.ext
    intro x
    exact Ideal.kerLiftAlg_mk q x
  have hqbar : qbar.Finite := AlgHom.Finite.of_comp_finite (hfactor ▸ hq)
  refine ⟨ψ, hψ, ?_, ?_, θ, E, rfl, hdiff⟩
  · have hh := hqbar.comp hfin
    simpa only [← AlgHom.comp_assoc, hfactor] using! hh
  · intro i
    let C : (K i ⊗[R] Ω[R⁄k]) →ₗ[K i] (Fin d → K i) :=
      LinearMap.pi fun a => (b i).coord a.succ
    apply LinearIndependent.of_comp C
    exact Matrix.linearIndependent_cols_of_det_ne_zero (hminor' i)

/-- The same finite ambient and closed projection, without exposing its initial chart. -/
theorem exists_finite_ambient_and_closed_projection
    (k R : Type u) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    [Algebra.FiniteType k R] (I : Ideal R) (d : ℕ)
    (hR : Algebra.trdeg k R ≤ d + 1) (hI : Algebra.trdeg k (R ⧸ I) ≤ d)
    {ι : Type v} [Finite ι] (K : ι → Type w)
    [∀ i, Field (K i)] [∀ i, Algebra R (K i)] [∀ i, Algebra k (K i)]
    [∀ i, IsScalarTower k R (K i)]
    (hdim : ∀ i, Module.finrank (K i) (K i ⊗[R] Ω[R⁄k]) = d + 1) :
    ∃ ψ : MvPolynomial (Fin (d + 1)) k →ₐ[k] R, ψ.Finite ∧
      ((Ideal.Quotient.mkₐ k I).comp (ψ.comp (MvPolynomial.rename Fin.succ))).Finite ∧
      ∀ i, LinearIndependent (K i)
        (fun j : Fin d => (1 ⊗ₜ[R] D k R (ψ (X j.succ)) : K i ⊗[R] Ω[R⁄k])) := by
  obtain ⟨ψ, hfin, hclosed, hi, _⟩ :=
    exists_finite_ambient_and_closed_projection_with_initial_chart k R I d hR hI K hdim
  exact ⟨ψ, hfin, hclosed, hi⟩

end KaehlerDifferential
