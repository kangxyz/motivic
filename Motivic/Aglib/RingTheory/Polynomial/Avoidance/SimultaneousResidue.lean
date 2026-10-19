module
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Set.Finite.Lattice

/-! # One ground-field scalar avoiding finitely many residue-field obstructions

The coefficient fields may be arbitrary extensions, including inseparable ones.
Only the ground field is required to be infinite.  This is the scalar-selection
step for simultaneous polynomial rank conditions in finite-coordinate changes.
-/
@[expose] public noncomputable section
universe u v w
namespace Polynomial

/-- A single nonzero ground-field scalar avoids finitely many nonzero polynomial
conditions in possibly different residue fields. -/
theorem exists_nonzero_scalar_avoiding_residue_polynomials
    (k : Type u) [Field k] [Infinite k] {ι : Type v} [Finite ι]
    (K : ι → Type w) [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    (p : (i : ι) → Polynomial (K i)) (hp : ∀ i, p i ≠ 0) :
    ∃ c : k, c ≠ 0 ∧ ∀ i, (p i).eval (algebraMap k (K i) c) ≠ 0 := by
  let bad : ι → Set k := fun i =>
    (algebraMap k (K i)) ⁻¹' {x | (p i).IsRoot x}
  have hbad : ∀ i, (bad i).Finite := fun i =>
    Set.Finite.preimage (algebraMap k (K i)).injective.injOn
      (Polynomial.finite_setOfPred_isRoot (hp i))
  obtain ⟨c, hc⟩ := ((Set.finite_iUnion hbad).insert 0).exists_notMem
  refine ⟨c, fun h => hc (Or.inl h), fun i hi => ?_⟩
  exact hc (Or.inr (Set.mem_iUnion.mpr ⟨i, hi⟩))

/-- Nonvanishing of each obstruction at the identity parameter ensures a common
nonzero parameter exists; no chosen residue-field identification is needed. -/
theorem exists_nonzero_scalar_preserving_residue_conditions
    (k : Type u) [Field k] [Infinite k] {ι : Type v} [Finite ι]
    (K : ι → Type w) [∀ i, Field (K i)] [∀ i, Algebra k (K i)]
    (p : (i : ι) → Polynomial (K i)) (hp : ∀ i, (p i).eval 0 ≠ 0) :
    ∃ c : k, c ≠ 0 ∧ ∀ i, (p i).eval (algebraMap k (K i) c) ≠ 0 := by
  apply exists_nonzero_scalar_avoiding_residue_polynomials k K p
  intro i hi
  exact hp i (by simp [hi])

end Polynomial
