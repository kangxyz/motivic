module
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Simultaneous ground-field specialization of residue-field polynomials

Taking a nonzero coefficient through a ground-field linear functional reduces
all residue-field obstructions to nonzero polynomials over the same infinite field.
No residue-field separability or rational-point hypothesis is needed.
-/
@[expose] public noncomputable section
open _root_.MvPolynomial
universe u v w z
namespace MvPolynomial

/-- Coefficientwise application of a linear functional commutes with evaluation
at ground-field coordinates. -/
theorem eval_coefficientLinearMap {k : Type u} [Field k]
    {K : Type w} [Field K] [Algebra k K] {σ : Type z}
    (L : K →ₗ[k] k) (p : MvPolynomial σ K) (x : σ → k) :
    eval x (AddMonoidAlgebra.map L.toAddMonoidHom p) =
      L (eval (fun a => algebraMap k K (x a)) p) := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
      simp only [AddMonoidAlgebra.map_add, map_add, hp, hq]
  | monomial m a =>
      rw [show AddMonoidAlgebra.map L.toAddMonoidHom (monomial m a) =
          monomial m (L a) by
        ext t
        simp only [coeff_addMonoidAlgebraMap, coeff_monomial]
        split_ifs <;> simp]
      simp only [eval_monomial]
      have hprod : (m.prod fun n e => algebraMap k K (x n) ^ e) =
          algebraMap k K (m.prod fun n e => x n ^ e) := by
        simp [Finsupp.prod]
      rw [mul_comm a, hprod, ← Algebra.smul_def, map_smul]
      simp [mul_comm]

/-- One assignment over the infinite ground field avoids finitely many nonzero
multivariate polynomial conditions over arbitrary extension fields. -/
theorem exists_ground_specialization_avoiding_residue_polynomials
    (k : Type u) [Field k] [Infinite k] {ι : Type v} [Finite ι] {σ : Type z}
    (K : ι → Type w) [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    (p : (i : ι) → MvPolynomial σ (K i)) (hp : ∀ i, p i ≠ 0) :
    ∃ x : σ → k, ∀ i, eval (fun a => algebraMap k (K i) (x a)) (p i) ≠ 0 := by
  classical
  let := Fintype.ofFinite ι
  have hcoeff : ∀ i, ∃ m, (p i).coeff m ≠ 0 := by
    intro i
    by_contra! h
    exact hp i (MvPolynomial.ext _ _ fun m => by simpa using h m)
  choose m hm using hcoeff
  choose L hL using fun i => Module.Projective.exists_dual_ne_zero k (hm i)
  let q : ι → MvPolynomial σ k := fun i => AddMonoidAlgebra.map (L i).toAddMonoidHom (p i)
  have hq : ∀ i, q i ≠ 0 := by
    intro i h
    have hh := congrArg (fun a : MvPolynomial σ k => a.coeff (m i)) h
    exact hL i (by simpa [q] using hh)
  have hprod : (∏ i, q i) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hq i
  have hex : ∃ x : σ → k, eval x (∏ i, q i) ≠ 0 := by
    by_contra! h
    exact hprod (MvPolynomial.funext fun x => by simpa using h x)
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, fun i hi => ?_⟩
  have hqi : eval x (q i) ≠ 0 := by
    rw [map_prod] at hx
    exact Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ i)
  exact hqi (by simp [q, eval_coefficientLinearMap, hi])

end MvPolynomial
