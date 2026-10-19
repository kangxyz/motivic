/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Actual graph relations in a polynomial relative tensor product

For arbitrary compatible polynomial algebras `A` and `B`, the quotient of
`A ⊗[R] B` by the differences of their polynomial coordinates is
`A ⊗[MvPolynomial σ R] B`. An actual polynomial-algebra map `B → A`
then induces graph evaluation on both tensor products. No flatness of this map,
reducedness of `A`, or finiteness of the coordinate type is assumed.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace Algebra.TensorProduct.PolynomialGraph

variable (R σ A B : Type*) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [Algebra (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) A]
  [Algebra (MvPolynomial σ R) B] [IsScalarTower R (MvPolynomial σ R) B]

/-- The right polynomial coordinate minus its prescribed value in the left factor. -/
def difference (i : σ) : A ⊗[R] B :=
  1 ⊗ₜ[R] algebraMap (MvPolynomial σ R) B (MvPolynomial.X i) -
    algebraMap (MvPolynomial σ R) A (MvPolynomial.X i) ⊗ₜ[R] 1

/-- The literal coordinate-relation ideal. -/
def ideal : Ideal (A ⊗[R] B) := Ideal.span (Set.range (difference R σ A B))

/-- The actual map from the absolute to the relative tensor product. -/
def toRelative : A ⊗[R] B →ₐ[A] A ⊗[MvPolynomial σ R] B :=
  Algebra.TensorProduct.lift Algebra.TensorProduct.includeLeft
    (Algebra.TensorProduct.includeRight.restrictScalars R) (fun _ _ => .all _ _)

@[simp]
theorem toRelative_tmul (a : A) (b : B) :
    toRelative R σ A B (a ⊗ₜ[R] b) = a ⊗ₜ[MvPolynomial σ R] b := by
  simp [toRelative, Algebra.TensorProduct.tmul_mul_tmul]

@[simp]
theorem toRelative_difference (i : σ) :
    toRelative R σ A B (difference R σ A B i) = 0 := by
  simp only [difference, map_sub, toRelative_tmul]
  exact sub_eq_zero.mpr (Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm

/-- The coordinate relations vanish under the actual relative tensor map. -/
theorem ideal_le_ker_toRelative :
    ideal R σ A B ≤ RingHom.ker (toRelative R σ A B) := by
  apply Ideal.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact toRelative_difference R σ A B i

/-- The map induced on the quotient by the coordinate relations. -/
def quotientToRelative :
    (A ⊗[R] B ⧸ ideal R σ A B) →ₐ[A] A ⊗[MvPolynomial σ R] B :=
  Ideal.Quotient.liftₐ (ideal R σ A B) (toRelative R σ A B)
    (ideal_le_ker_toRelative R σ A B)

@[simp]
theorem quotientToRelative_mk (x : A ⊗[R] B) :
    quotientToRelative R σ A B (Ideal.Quotient.mk (ideal R σ A B) x) =
      toRelative R σ A B x := rfl

omit [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B] in
/-- The two coordinate values agree in the graph-relation quotient. -/
theorem mk_right_X_eq_left (i : σ) :
    Ideal.Quotient.mk (ideal R σ A B)
      (1 ⊗ₜ[R] algebraMap (MvPolynomial σ R) B (MvPolynomial.X i)) =
    Ideal.Quotient.mk (ideal R σ A B)
      (algebraMap (MvPolynomial σ R) A (MvPolynomial.X i) ⊗ₜ[R] 1) := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_range_self i)

/-- Polynomial extensionality promotes the coordinate equations to all polynomials. -/
theorem mk_right_eq_left (p : MvPolynomial σ R) :
    Ideal.Quotient.mk (ideal R σ A B) (1 ⊗ₜ[R] algebraMap (MvPolynomial σ R) B p) =
    Ideal.Quotient.mk (ideal R σ A B) (algebraMap (MvPolynomial σ R) A p ⊗ₜ[R] 1) := by
  let q := Ideal.Quotient.mkₐ R (ideal R σ A B)
  have h : (q.comp Algebra.TensorProduct.includeRight).comp
      (IsScalarTower.toAlgHom R (MvPolynomial σ R) B) =
      (q.comp Algebra.TensorProduct.includeLeft).comp
        (IsScalarTower.toAlgHom R (MvPolynomial σ R) A) := by
    ext i
    exact mk_right_X_eq_left R σ A B i
  exact DFunLike.congr_fun h p

/-- The right inclusion becomes linear over the polynomial algebra in the quotient. -/
def quotientIncludeRight : B →ₐ[MvPolynomial σ R] (A ⊗[R] B ⧸ ideal R σ A B) where
  __ := (Ideal.Quotient.mk (ideal R σ A B)).comp Algebra.TensorProduct.includeRight.toRingHom
  commutes' p := mk_right_eq_left R σ A B p

@[simp]
theorem quotientIncludeRight_apply (b : B) :
    quotientIncludeRight R σ A B b = Ideal.Quotient.mk (ideal R σ A B) (1 ⊗ₜ[R] b) := rfl

/-- The inverse map is induced by the actual two quotient inclusions. -/
def fromRelative :
    A ⊗[MvPolynomial σ R] B →ₐ[A] (A ⊗[R] B ⧸ ideal R σ A B) :=
  Algebra.TensorProduct.lift
    ((Ideal.Quotient.mkₐ A (ideal R σ A B)).comp Algebra.TensorProduct.includeLeft)
    (quotientIncludeRight R σ A B) (fun _ _ => .all _ _)

@[simp]
theorem fromRelative_tmul (a : A) (b : B) :
    fromRelative R σ A B (a ⊗ₜ[MvPolynomial σ R] b) =
      Ideal.Quotient.mk (ideal R σ A B) (a ⊗ₜ[R] b) := by
  simp [fromRelative, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul]

/-- The quotient by graph coordinate relations is the actual relative tensor product. -/
def quotientEquiv :
    (A ⊗[R] B ⧸ ideal R σ A B) ≃ₐ[A] A ⊗[MvPolynomial σ R] B :=
  AlgEquiv.ofAlgHom (quotientToRelative R σ A B) (fromRelative R σ A B)
    (by
      apply AlgHom.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul a b => simp
      | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy)
    (by
      apply Ideal.Quotient.algHom_ext
      apply AlgHom.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul a b => simp
      | add x y hx hy => simpa using congrArg₂ (· + ·) hx hy)

@[simp]
theorem quotientEquiv_mk (x : A ⊗[R] B) :
    quotientEquiv R σ A B (Ideal.Quotient.mk (ideal R σ A B) x) =
      toRelative R σ A B x := rfl

/-- The actual relative tensor map has exactly the coordinate-relation kernel. -/
theorem ker_toRelative : RingHom.ker (toRelative R σ A B) = ideal R σ A B := by
  apply le_antisymm
  · intro x hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply (quotientEquiv R σ A B).injective
    simpa using hx
  · exact ideal_le_ker_toRelative R σ A B

/-- The actual relative tensor map is surjective. -/
theorem toRelative_surjective : Function.Surjective (toRelative R σ A B) := by
  intro y
  obtain ⟨x, hx⟩ := (quotientEquiv R σ A B).surjective y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨x, hx⟩

variable (f : B →ₐ[MvPolynomial σ R] A)

/-- Actual graph evaluation sends a pure tensor to the left value times its right image. -/
def evaluation : A ⊗[R] B →ₐ[A] A :=
  Algebra.TensorProduct.lift (AlgHom.id A A) (f.restrictScalars R) (fun _ _ => .all _ _)

@[simp]
theorem evaluation_tmul (a : A) (b : B) : evaluation R σ A B f (a ⊗ₜ[R] b) = a * f b := by
  simp [evaluation]

/-- Graph evaluation on the relative tensor algebra. -/
def relativeEvaluation : A ⊗[MvPolynomial σ R] B →ₐ[A] A :=
  Algebra.TensorProduct.lift (AlgHom.id A A) f (fun _ _ => .all _ _)

omit [Algebra R A] [Algebra R B]
    [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B] in
@[simp]
theorem relativeEvaluation_tmul (a : A) (b : B) :
    relativeEvaluation R σ A B f (a ⊗ₜ[MvPolynomial σ R] b) = a * f b := by
  simp [relativeEvaluation]

omit [Algebra R A] [Algebra R B]
    [IsScalarTower R (MvPolynomial σ R) A] [IsScalarTower R (MvPolynomial σ R) B] in
/-- Relative graph evaluation is a split surjection, without flatness of the graph map. -/
theorem relativeEvaluation_surjective : Function.Surjective (relativeEvaluation R σ A B f) :=
  fun a => ⟨a ⊗ₜ 1, by simp⟩

/-- The actual graph map factors through the actual relative tensor quotient. -/
theorem relativeEvaluation_comp_toRelative :
    (relativeEvaluation R σ A B f).comp (toRelative R σ A B) = evaluation R σ A B f := by
  ext
  simp

@[simp]
theorem evaluation_difference (i : σ) : evaluation R σ A B f (difference R σ A B i) = 0 := by
  simp [difference]

end Algebra.TensorProduct.PolynomialGraph
