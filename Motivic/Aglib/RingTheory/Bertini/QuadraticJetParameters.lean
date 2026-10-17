module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticJetsOverRing
public import Mathlib.RingTheory.MvPolynomial.Basic

/-! # The finite-dimensional quadratic parameter map for two-point incidence -/
@[expose] public noncomputable section
namespace MvPolynomial
universe u v
variable {K : Type u} {σ : Type v}

/-- The actual linear constraint map on quadratic parameters: equality of values
and the first derivative at the moving second point are independent constraints. -/
def quadraticJetParameters [CommRing K] (a b : σ → K) :
    restrictTotalDegree σ K 2 →ₗ[K] K × (σ → K) where
  toFun f := (eval b f.val - eval a f.val, fun i => eval b (pderiv i f.val))
  map_add' f g := by
    ext <;> simp [sub_add_sub_comm]
  map_smul' c f := by
    ext <;> simp [mul_sub]

/-- All value-difference and cotangent constraints are simultaneously realizable
inside the same finite-dimensional quadratic parameter space. -/
theorem quadraticJetParameters_surjective [Field K] [Finite σ] (a b : σ → K) (hab : a ≠ b) :
    Function.Surjective (quadraticJetParameters a b) := by
  rintro ⟨c, v⟩
  obtain ⟨f, hf, hv, hd⟩ := exists_quadratic_value_difference_jet a b hab c v
  refine ⟨⟨f, (mem_restrictTotalDegree σ 2 f).mpr hf⟩, ?_⟩
  exact Prod.ext hv (funext hd)

/-- Over an actual principal chart off the diagonal the parameter map is surjective
as a map of modules over the chart ring, not merely on its geometric fibers. -/
theorem quadraticJetParameters_surjective_of_inverse [CommRing K] [Finite σ]
    (a b : σ → K) (j : σ) (e : K) (he : e * (b j - a j) = 1) :
    Function.Surjective (quadraticJetParameters a b) := by
  rintro ⟨c, v⟩
  obtain ⟨f, hf, hv, hd⟩ := exists_quadratic_value_difference_jet_of_inverse a b j e he c v
  refine ⟨⟨f, (mem_restrictTotalDegree σ 2 f).mpr hf⟩, ?_⟩
  exact Prod.ext hv (funext hd)

end MvPolynomial
