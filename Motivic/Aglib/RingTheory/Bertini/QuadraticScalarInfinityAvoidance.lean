/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.QuadraticBoundaryScalarMap
public import Motivic.Aglib.RingTheory.Bertini.QuadraticInfinityAvoidance
public import Motivic.Aglib.RingTheory.Bertini.ProjectiveScalarEvaluationAvoidance

/-! # Actual scalar-source infinity avoidance from original chart equations -/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open _root_.MvPolynomial

namespace QuadraticIncidence.InfinityChart

universe u

variable (k L R S : Type u) [Field k] [Field L] [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S] [Algebra k R] [Algebra k L] [Algebra L S]
  [Algebra k S] [IsScalarTower k L S]
  (f : R →ₐ[k] S) (hf : Function.Injective f)
  {σ : Type u} (g : σ → R)

/-- The actual full-quotient boundary map preserves the original ground scalars. -/
theorem scalarBoundaryMap_algebraMap (j : Exponent σ) (r : k) :
    scalarBoundaryMap k L R S f hf g j (algebraMap k (boundaryRing k R g j) r) =
      algebraMap k (boundaryRing L S (f ∘ g) j) r := by
  change Ideal.Quotient.mk _ (scalarChartMap k L R S f hf g j
    (algebraMap k (chart k R g j) r)) =
      Ideal.Quotient.mk _ (algebraMap k (chart L S (f ∘ g) j) r)
  congr 1
  apply Subtype.ext
  change scalarFractionMap k R S f hf (algebraMap k (FractionRing R) r) =
    algebraMap k (FractionRing S) r
  rw [IsScalarTower.algebraMap_apply k R (FractionRing R)]
  simp only [scalarFractionMap, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, f.commutes]
  exact (IsScalarTower.algebraMap_apply k S (FractionRing S) r).symm

/-- The scalar boundary map as an actual original-ground algebra morphism. -/
def scalarBoundaryAlgHom (j : Exponent σ) :
    boundaryRing k R g j →ₐ[k] boundaryRing L S (f ∘ g) j where
  __ := scalarBoundaryMap k L R S f hf g j
  commutes' := scalarBoundaryMap_algebraMap k L R S f hf g j

variable [Finite σ]

include hf in
/-- Every actual scalar-source infinity chart has no common zero whenever the
chosen scalar tuple avoids the unchanged original chart-relation polynomial. -/
theorem noCommonInfinityZero_of_original_eval₂_relation (d : ℕ)
    (F : MvPolynomial (Fin (d + 1) × Exponent σ) k)
    (hF : ∀ j : Exponent σ, monomialFunction k R g j ≠ 0 →
      ProjectiveEvaluationIncidence.parameterMap (boundaryRing k R g j) k
        (boundaryCoordinate k R g j) (d + 1) F = 0)
    (z : Fin (d + 1) × Exponent σ → L)
    (hz : eval₂ (algebraMap k L) z F ≠ 0) :
    NoCommonInfinityZero L S (f ∘ g) d z := by
  let := Fintype.ofFinite σ
  intro j hj
  dsimp only
  intro K _ _ _ _ hzero
  let A := boundaryRing k R g j
  let A' := boundaryRing L S (f ∘ g) j
  let : Algebra k K := ((algebraMap L K).comp (algebraMap k L)).toAlgebra
  let : IsScalarTower k L K := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower k A' K := IsScalarTower.to₁₃₄ k L A' K
  let φ : A' → K := IsScalarTower.toAlgHom L A' K
  let ψ : A →ₐ[k] K := (IsScalarTower.toAlgHom k A' K).comp
    (scalarBoundaryAlgHom k L R S f hf g j)
  let : Algebra A K := ψ.toRingHom.toAlgebra
  let : IsScalarTower k A K := IsScalarTower.of_algebraMap_eq (R := k) (S := A) (A := K)
    fun r => (ψ.commutes r).symm
  have hj₀ : monomialFunction k R g j ≠ 0 := by
    intro he
    apply hj
    rw [← scalarMap_monomialFunction k L R S f g j, he, map_zero]
  have hnonzero : eval₂ (algebraMap k K) (algebraMap L K ∘ z) F ≠ 0 := by
    rw [IsScalarTower.algebraMap_eq k L K, ← eval₂_comp_left]
    exact fun h => hz ((algebraMap L K).injective (by simpa using h))
  apply ProjectiveEvaluationIncidence.not_vanish_of_eval₂_relation k A K
    (boundaryCoordinate k R g j) (d + 1) F (hF j hj₀)
    (algebraMap L K ∘ z) hnonzero
  intro i
  change ∑ e, algebraMap L K (z (i, e)) *
    ψ (boundaryCoordinate k R g j e) = 0
  have hcoord (e : Exponent σ) : ψ (boundaryCoordinate k R g j e) =
      φ (boundaryCoordinate L S (f ∘ g) j e) := by
    change φ (scalarBoundaryMap k L R S f hf g j
      (boundaryCoordinate k R g j e)) = _
    rw [scalarBoundaryMap_coordinate]
  simp_rw [hcoord]
  exact hzero i

end QuadraticIncidence.InfinityChart
