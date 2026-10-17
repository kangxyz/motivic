/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.QuadraticDiagonalFieldExtension
public import Mathlib.RingTheory.TensorProduct.Nontrivial

/-! # Common fields for residue points over the same original image prime -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential
universe u v
namespace QuadraticIncidence

/-- Two arbitrary field extensions admit an actual common field. The tensor product
is not assumed to be a domain; a maximal ideal supplies the common residue field. -/
theorem exists_common_field (F L M : Type u) [Field F] [Field L] [Field M]
    [Algebra F L] [Algebra F M] :
    ∃ (K : Type u) (_ : Field K) (i : L →+* K) (j : M →+* K),
      i.comp (algebraMap F L) = j.comp (algebraMap F M) := by
  let T := L ⊗[F] M
  have : Nontrivial T := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain
    F L M (algebraMap F L).injective (algebraMap F M).injective
  obtain ⟨I, hI⟩ := Ideal.exists_maximal (α := T)
  let : I.IsMaximal := hI
  let i := (algebraMap T I.ResidueField).comp (algebraMap L T)
  let j := (algebraMap T I.ResidueField).comp
    (Algebra.TensorProduct.includeRight : M →ₐ[F] T).toRingHom
  refine ⟨I.ResidueField, inferInstance, i, j, ?_⟩
  ext r
  apply congrArg (algebraMap T I.ResidueField)
  exact (IsScalarTower.algebraMap_apply F L T r).symm.trans
    ((Algebra.TensorProduct.includeRight : M →ₐ[F] T).commutes r).symm

/-- Residue fields of points over the same image prime embed in a common field,
compatibly with the original ground field and the original map. -/
theorem exists_common_residue_field (k A R : Type u) [Field k] [CommRing A] [CommRing R]
    [Algebra k A] [Algebra k R] (φ : A →ₐ[k] R) (P Q : PrimeSpectrum R)
    (hPQ : Ideal.comap φ.toRingHom P.asIdeal = Ideal.comap φ.toRingHom Q.asIdeal) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K)
      (i : P.asIdeal.ResidueField →ₐ[k] K) (j : Q.asIdeal.ResidueField →ₐ[k] K),
      ∀ a : A, i (algebraMap R P.asIdeal.ResidueField (φ a)) =
        j (algebraMap R Q.asIdeal.ResidueField (φ a)) := by
  let s := Ideal.comap φ.toRingHom P.asIdeal
  let α := Ideal.ResidueField.mapₐ s P.asIdeal φ rfl
  let β := Ideal.ResidueField.mapₐ s Q.asIdeal φ hPQ
  let : Algebra s.ResidueField P.asIdeal.ResidueField := α.toRingHom.toAlgebra
  let : Algebra s.ResidueField Q.asIdeal.ResidueField := β.toRingHom.toAlgebra
  obtain ⟨K, hK, i, j, hij⟩ := exists_common_field s.ResidueField
    P.asIdeal.ResidueField Q.asIdeal.ResidueField
  let : Field K := hK
  have hval (a : A) : i (algebraMap R P.asIdeal.ResidueField (φ a)) =
      j (algebraMap R Q.asIdeal.ResidueField (φ a)) := by
    have h := DFunLike.congr_fun hij (algebraMap A s.ResidueField a)
    change i (α (algebraMap A s.ResidueField a)) =
      j (β (algebraMap A s.ResidueField a)) at h
    simpa only [α, β, Ideal.ResidueField.mapₐ_apply, Ideal.ResidueField.map_algebraMap,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe] using h
  let : Algebra k K := (j.comp (algebraMap k Q.asIdeal.ResidueField)).toAlgebra
  let j' : Q.asIdeal.ResidueField →ₐ[k] K := ⟨j, fun _ => rfl⟩
  let i' : P.asIdeal.ResidueField →ₐ[k] K :=
    { toRingHom := i
      commutes' := fun r => by
        change i (algebraMap k P.asIdeal.ResidueField r) =
          j (algebraMap k Q.asIdeal.ResidueField r)
        have h := hval (algebraMap k A r)
        simpa only [φ.commutes, ← IsScalarTower.algebraMap_apply] using h }
  exact ⟨K, hK, inferInstance, i', j', hval⟩

/-- Independence of the actual differentials descends from any extension field. -/
theorem independent_differentials_descend (k R L K : Type u)
    [Field k] [CommRing R] [Field L] [Field K] [Algebra k R]
    [Algebra R L] [Algebra R K] [Algebra L K] [IsScalarTower R L K]
    {ι : Type v} (f : ι → R)
    (hf : LinearIndependent K (fun i => (1 ⊗ₜ[R] D k R (f i) : K ⊗[R] Ω[R⁄k]))) :
    LinearIndependent L (fun i => (1 ⊗ₜ[R] D k R (f i) : L ⊗[R] Ω[R⁄k])) := by
  let e := AlgebraTensorModule.cancelBaseChange R L K K Ω[R⁄k]
  let m : L ⊗[R] Ω[R⁄k] →ₗ[L] K ⊗[R] Ω[R⁄k] :=
    (e.toLinearMap.restrictScalars L).comp (TensorProduct.mk L K (L ⊗[R] Ω[R⁄k]) 1)
  have hm (r : R) : m (1 ⊗ₜ[R] D k R r) = 1 ⊗ₜ[R] D k R r := by
    simp [m, e]
  apply LinearIndependent.of_comp m
  simpa only [Function.comp_def, hm] using hf.restrict_scalars' L

/-- A condition valid over all actual coefficient-algebra fields applies at every
prime of the same original fiber, even without an embedding of its two residue fields. -/
theorem independent_differentials_of_same_fiber
    (k R : Type u) [Field k] [CommRing R] [Algebra k R]
    (P Q : PrimeSpectrum R) (d : ℕ) (f : Fin d → R)
    (hPQ : Ideal.comap (MvPolynomial.aeval (R := k) f).toRingHom P.asIdeal =
      Ideal.comap (MvPolynomial.aeval (R := k) f).toRingHom Q.asIdeal)
    (h : ∀ (K : Type u) [Field K] [Algebra k K] [Algebra R K]
      [Algebra (ClosedPoint.CoefficientRing k R P) K]
      [IsScalarTower k (ClosedPoint.CoefficientRing k R P) K]
      [IsScalarTower R (ClosedPoint.CoefficientRing k R P) K],
      (∀ i, algebraMap R K (f i) = algebraMap (ClosedPoint.CoefficientRing k R P) K
        (ClosedPoint.selectedValue k R P (f i))) →
      LinearIndependent K (fun i => (1 ⊗ₜ[R] D k R (f i) : K ⊗[R] Ω[R⁄k]))) :
    LinearIndependent Q.asIdeal.ResidueField
      (fun i => (1 ⊗ₜ[R] D k R (f i) : Q.asIdeal.ResidueField ⊗[R] Ω[R⁄k])) := by
  obtain ⟨K, hK, hkK, i, j, hij⟩ := exists_common_residue_field k
    (MvPolynomial (Fin d) k) R (MvPolynomial.aeval (R := k) f) P Q hPQ
  let : Field K := hK
  let : Algebra k K := hkK
  let : Algebra Q.asIdeal.ResidueField K := j.toRingHom.toAlgebra
  let m : R →ₐ[k] K := j.comp (IsScalarTower.toAlgHom k R Q.asIdeal.ResidueField)
  let : Algebra R K := m.toRingHom.toAlgebra
  let : IsScalarTower R Q.asIdeal.ResidueField K := IsScalarTower.of_algebraMap_eq' rfl
  let b : ClosedPoint.CoefficientRing k R P →ₐ[k] K :=
    Algebra.TensorProduct.lift m i (fun _ _ => Commute.all _ _)
  let : Algebra (ClosedPoint.CoefficientRing k R P) K := b.toRingHom.toAlgebra
  let : IsScalarTower k (ClosedPoint.CoefficientRing k R P) K :=
    IsScalarTower.of_algebraMap_eq fun r => (b.commutes r).symm
  let : IsScalarTower R (ClosedPoint.CoefficientRing k R P) K :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change m r = b (r ⊗ₜ[k] (1 : P.asIdeal.ResidueField))
      simp [b]
  have hv : ∀ n, algebraMap R K (f n) =
      algebraMap (ClosedPoint.CoefficientRing k R P) K
        (ClosedPoint.selectedValue k R P (f n)) := by
    intro n
    have hn := hij (MvPolynomial.X n)
    simp only [MvPolynomial.aeval_X] at hn
    change j (algebraMap R Q.asIdeal.ResidueField (f n)) =
      b (1 ⊗ₜ[k] algebraMap R P.asIdeal.ResidueField (f n))
    simpa [b] using hn.symm
  exact independent_differentials_descend k R Q.asIdeal.ResidueField K f (h K hv)

end QuadraticIncidence
