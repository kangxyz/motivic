module
public import Motivic.Aglib.RingTheory.Kaehler.ResidueFunctionBasis
public import Motivic.Aglib.RingTheory.NoetherNormalization.Residue.LinearProjection

/-! # Common original functions with independent residue differentials

Finite residue fibers of equal cotangent dimension admit the same original
functions as differential coordinates over an infinite ground field.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential Matrix
universe u v w z
namespace KaehlerDifferential

/-- Actual original functions simultaneously give independent differentials at
finitely many residue fibers. No local chart or rationality premise is supplied. -/
theorem exists_simultaneous_residue_differential_coordinates
    (k : Type u) (R : Type v) [Field k] [Infinite k] [CommRing R] [Algebra k R]
    [Algebra.EssFiniteType k R] {ι : Type z} [Finite ι]
    (K : ι → Type w) [∀ i, Field (K i)] [∀ i, Algebra R (K i)]
    [∀ i, Algebra k (K i)] [∀ i, IsScalarTower k R (K i)] (d : ℕ)
    (hd : ∀ i, Module.finrank (K i) (K i ⊗[R] Ω[R⁄k]) = d) :
    ∃ g : Fin d → R, ∀ i,
      LinearIndependent (K i) (fun j => (1 ⊗ₜ[R] D k R (g j) : K i ⊗[R] Ω[R⁄k])) := by
  classical
  let := Fintype.ofFinite ι
  choose g b hb using fun i => exists_residue_basis_fin_original_functions k R (K i) d (hd i)
  let v (i : ι) (x : R) : K i ⊗[R] Ω[R⁄k] := 1 ⊗ₜ[R] D k R x
  let A (i : ι) : Matrix (Fin d) (ι × Fin d) (K i) :=
    fun a t => (b i).equivFun (v i (g t.1 t.2)) a
  have hA (i : ι) : Function.Surjective (A i).mulVec := by
    intro y
    refine ⟨fun t => if t.1 = i then y t.2 else 0, ?_⟩
    ext a
    simp [A, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, v, ← hb,
      Finsupp.single_apply]
  obtain ⟨B, hB⟩ := Matrix.exists_simultaneous_residue_linear_projection k K A hA
  let h : Fin d → R := fun a => ∑ t : ι × Fin d, B t a • g t.1 t.2
  refine ⟨h, fun i => ?_⟩
  have heq : (fun a c => (b i).equivFun (v i (h c)) a) =
      A i * B.map (algebraMap k (K i)) := by
    ext a c
    simp only [h, v, map_sum, Derivation.map_smul, tmul_sum, map_sum,
      Matrix.mul_apply, Matrix.map_apply, A, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro t _
    rw [TensorProduct.tmul_smul]
    have hh := ((b i).equivFun.restrictScalars k).map_smul (B t c)
      (1 ⊗ₜ[R] D k R (g t.1 t.2))
    have hha := congrFun hh a
    exact hha.trans (by
      simp only [Pi.smul_apply, Algebra.smul_def, mul_comm]
      rfl)
  have hli := Matrix.linearIndependent_cols_of_det_ne_zero (hB i)
  rw [← heq] at hli
  exact hli.of_comp (b i).equivFun.toLinearMap

end KaehlerDifferential
