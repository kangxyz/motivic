/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.MvPolynomial.DiagonalFlat
public import Motivic.Aglib.RingTheory.TensorProduct.UnramifiedDiagonal
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!
# Regular local diagonal presentations in étale polynomial coordinates

The polynomial tensor square is identified with the ring on two sets of
coordinates. For an actual flat polynomial-algebra map, its tensor square is
flat, so the literal coordinate differences remain weakly regular. Localizing
at a diagonal point gives a regular sequence: the differences belong to the
maximal ideal. For an étale polynomial-algebra map, these same elements generate
the kernel of the actual localized multiplication map. The coefficient ring
is arbitrary; no regularity of coefficient or support modules is assumed.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct
open RingTheory.Sequence

namespace MvPolynomial.Diagonal

variable (R σ : Type*) [CommRing R]

/-- The actual polynomial tensor square, with the left and right coordinate copies. -/
def tensorEquiv : Ambient R σ ≃ₐ[R] MvPolynomial σ R ⊗[R] MvPolynomial σ R :=
  (MvPolynomial.tensorEquivSum R σ σ R).symm

@[simp]
theorem tensorEquiv_X_left (i : σ) :
    tensorEquiv R σ (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X i ⊗ₜ[R] 1 :=
  (MvPolynomial.tensorEquivSum R σ σ R).symm_apply_eq.mpr (by simp)

@[simp]
theorem tensorEquiv_X_right (i : σ) :
    tensorEquiv R σ (MvPolynomial.X (Sum.inr i)) = 1 ⊗ₜ[R] MvPolynomial.X i :=
  (MvPolynomial.tensorEquivSum R σ σ R).symm_apply_eq.mpr (by simp)

@[simp]
theorem tensorEquiv_difference (i : σ) :
    tensorEquiv R σ (difference R σ i) =
      1 ⊗ₜ[R] MvPolynomial.X i - MvPolynomial.X i ⊗ₜ[R] 1 := by
  simp [difference]

end MvPolynomial.Diagonal

namespace Algebra.TensorProduct.RelativePolynomial

variable (R σ S : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra (MvPolynomial σ R) S] [IsScalarTower R (MvPolynomial σ R) S]

/-- The tensor square of the actual polynomial-algebra map. -/
def polynomialTensorMap :
    MvPolynomial σ R ⊗[R] MvPolynomial σ R →ₐ[R] S ⊗[R] S :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom R (MvPolynomial σ R) S)
    (IsScalarTower.toAlgHom R (MvPolynomial σ R) S)

/-- The actual ambient coordinate map, factored through the polynomial tensor square. -/
def coordinateMap : _root_.MvPolynomial.Diagonal.Ambient R σ →ₐ[R] S ⊗[R] S :=
  (polynomialTensorMap R σ S).comp (_root_.MvPolynomial.Diagonal.tensorEquiv R σ).toAlgHom

@[simp]
theorem coordinateMap_X_left (i : σ) :
    coordinateMap R σ S (MvPolynomial.X (Sum.inl i)) =
      algebraMap (MvPolynomial σ R) S (MvPolynomial.X i) ⊗ₜ[R] 1 := by
  simp [coordinateMap, polynomialTensorMap]

@[simp]
theorem coordinateMap_X_right (i : σ) :
    coordinateMap R σ S (MvPolynomial.X (Sum.inr i)) =
      1 ⊗ₜ[R] algebraMap (MvPolynomial σ R) S (MvPolynomial.X i) := by
  simp [coordinateMap, polynomialTensorMap]

@[simp]
theorem coordinateMap_difference (i : σ) :
    coordinateMap R σ S (_root_.MvPolynomial.Diagonal.difference R σ i) = difference R σ S i := by
  simp [coordinateMap, polynomialTensorMap, difference]

/-- Flatness is proved for the tensor square of the actual map, rather than assumed. -/
theorem polynomialTensorMap_flat [Module.Flat (MvPolynomial σ R) S] :
    (polynomialTensorMap R σ S).Flat := by
  apply RingHom.Flat.tensorProductMap
  all_goals exact RingHom.flat_algebraMap_iff.mpr inferInstance

/-- The ambient coordinate map is flat because its first factor is an isomorphism. -/
theorem coordinateMap_flat [Module.Flat (MvPolynomial σ R) S] :
    (coordinateMap R σ S).Flat :=
  (RingHom.Flat.of_bijective (_root_.MvPolynomial.Diagonal.tensorEquiv R σ).bijective).comp
    (polynomialTensorMap_flat R σ S)

/-- The literal differences remain weakly regular under an actual flat coordinate map. -/
theorem isWeaklyRegular_differences [Module.Flat (MvPolynomial σ R) S]
    (l : List σ) (hl : l.Nodup) :
    IsWeaklyRegular (S ⊗[R] S) (l.map (difference R σ S)) := by
  let := (coordinateMap R σ S).toAlgebra
  let : Module.Flat (_root_.MvPolynomial.Diagonal.Ambient R σ) (S ⊗[R] S) :=
    coordinateMap_flat R σ S
  have h := _root_.MvPolynomial.Diagonal.isWeaklyRegular_differences_baseChange R σ (S ⊗[R] S) l hl
  change IsWeaklyRegular (S ⊗[R] S)
    (l.map (fun i => coordinateMap R σ S (_root_.MvPolynomial.Diagonal.difference R σ i))) at h
  simpa only [coordinateMap_difference] using h

/-- The actual localized coordinate difference at a diagonal point. -/
def localDifference (p : Ideal S) [p.IsPrime] (i : σ) :
    Localization.AtPrime (diagonalPrime R S p) :=
  algebraMap (S ⊗[R] S) _ (difference R σ S i)

omit [IsScalarTower R (MvPolynomial σ R) S] in
/-- Tensor multiplication annihilates each literal coordinate difference. -/
theorem multiplication_difference (i : σ) :
    multiplication R S (difference R σ S i) = 0 := by
  simp [multiplication, difference]

omit [IsScalarTower R (MvPolynomial σ R) S] in
/-- Every coordinate difference lies in the prime of its diagonal point. -/
theorem difference_mem_diagonalPrime (p : Ideal S) (i : σ) :
    difference R σ S i ∈ diagonalPrime R S p := by
  change multiplication R S (difference R σ S i) ∈ p
  rw [multiplication_difference]
  exact p.zero_mem

omit [IsScalarTower R (MvPolynomial σ R) S] in
/-- In the actual local tensor ring the differences belong to its maximal ideal. -/
theorem localDifference_mem_maximalIdeal (p : Ideal S) [p.IsPrime] (i : σ) :
    localDifference R σ S p i ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime (diagonalPrime R S p)) :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ _).mpr
    (difference_mem_diagonalPrime R σ S p i)

/-- Flatness of the actual coordinate map survives localization at the diagonal point. -/
theorem localCoordinateMap_flat [Module.Flat (MvPolynomial σ R) S]
    (p : Ideal S) [p.IsPrime] :
    ((algebraMap (S ⊗[R] S) (Localization.AtPrime (diagonalPrime R S p))).comp
      (coordinateMap R σ S).toRingHom).Flat :=
  (coordinateMap_flat R σ S).comp (RingHom.flat_algebraMap_iff.mpr inferInstance)

-- The localization additive-group instance agrees with the one induced by its ring.
set_option backward.isDefEq.respectTransparency false in
/-- The literal localized differences form a regular sequence for every distinct list. -/
theorem isRegular_localDifferences [Module.Flat (MvPolynomial σ R) S]
    (p : Ideal S) [p.IsPrime] (l : List σ) (hl : l.Nodup) :
    IsRegular (Localization.AtPrime (diagonalPrime R S p))
      (l.map (localDifference R σ S p)) := by
  let f := (algebraMap (S ⊗[R] S) (Localization.AtPrime (diagonalPrime R S p))).comp
    (coordinateMap R σ S).toRingHom
  let := f.toAlgebra
  let : Module.Flat (_root_.MvPolynomial.Diagonal.Ambient R σ)
      (Localization.AtPrime (diagonalPrime R S p)) := localCoordinateMap_flat R σ S p
  have h := _root_.MvPolynomial.Diagonal.isWeaklyRegular_differences_baseChange R σ
    (Localization.AtPrime (diagonalPrime R S p)) l hl
  have hw : IsWeaklyRegular (Localization.AtPrime (diagonalPrime R S p))
      (l.map (localDifference R σ S p)) := by
    convert! h using 1
    simp only [RingHom.algebraMap_toAlgebra, f, RingHom.comp_apply, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, coordinateMap_difference]
    rfl
  apply IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal _ _ hw
  intro x hx
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  exact localDifference_mem_maximalIdeal R σ S p i

/-- A complete coordinate list generates exactly the actual localized diagonal kernel. -/
theorem ker_localMultiplication_eq_ofList
    [Algebra.EssFiniteType (MvPolynomial σ R) S]
    [Algebra.FormallyUnramified (MvPolynomial σ R) S]
    (p : Ideal S) [p.IsPrime] (l : List σ) (hcover : ∀ i, i ∈ l) :
    RingHom.ker (localMultiplication R S p) =
      Ideal.ofList (l.map (localDifference R σ S p)) := by
  rw [ker_localMultiplication R σ S p, ideal, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
    exact List.mem_map.mpr ⟨i, hcover i, rfl⟩
  · intro hx
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    exact ⟨difference R σ S i, ⟨i, rfl⟩, rfl⟩

/-- An étale polynomial coordinate chart gives an actual regular local diagonal presentation. -/
theorem etale_localDiagonalPresentation [Algebra.Etale (MvPolynomial σ R) S]
    (p : Ideal S) [p.IsPrime] (l : List σ) (hl : l.Nodup) (hcover : ∀ i, i ∈ l) :
    IsRegular (Localization.AtPrime (diagonalPrime R S p))
      (l.map (localDifference R σ S p)) ∧
    RingHom.ker (localMultiplication R S p) =
      Ideal.ofList (l.map (localDifference R σ S p)) :=
  ⟨isRegular_localDifferences R σ S p l hl,
    ker_localMultiplication_eq_ofList R σ S p l hcover⟩

end Algebra.TensorProduct.RelativePolynomial
