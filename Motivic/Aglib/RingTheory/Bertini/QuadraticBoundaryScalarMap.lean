/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Bertini.QuadraticInfinityParameterRelation

/-! # Literal boundary chart maps under injective scalar extension

Only the direction needed to restrict field-valued boundary points is constructed.
The actual infinity quotient and all original monomial coordinates are retained.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open MvPolynomial

namespace QuadraticIncidence.InfinityChart

universe u

variable (k L R S : Type u) [Field k] [Field L] [CommRing R] [IsDomain R]
  [CommRing S] [IsDomain S] [Algebra k R] [Algebra k L] [Algebra L S]
  [Algebra k S] [IsScalarTower k L S]
  (f : R →ₐ[k] S) (hf : Function.Injective f)
  {σ : Type u} (g : σ → R)

/-- The canonical injective map on the actual fraction rings. -/
def scalarFractionMap : FractionRing R →+* FractionRing S :=
  IsFractionRing.lift (g := (algebraMap S (FractionRing S)).comp f.toRingHom)
    ((IsFractionRing.injective S (FractionRing S)).comp hf)

omit [IsDomain R] [IsDomain S] [Algebra k L] [IsScalarTower k L S] in
/-- Original monomial functions commute with the actual scalar ring map. -/
theorem scalarMap_monomialFunction (e : Exponent σ) :
    f (monomialFunction k R g e) = monomialFunction L S (f ∘ g) e := by
  simp [monomialFunction, aeval_def, eval₂_monomial, Function.comp_def, Finsupp.prod]

omit [Algebra k L] [IsScalarTower k L S] in
/-- The literal monomial ratios commute with the injective fraction-ring map. -/
theorem scalarFractionMap_ratio (j e : Exponent σ) :
    scalarFractionMap k R S f hf (ratio k R g j e) =
      ratio L S (f ∘ g) j e := by
  simp only [ratio, map_div₀, scalarFractionMap, IsFractionRing.lift_algebraMap,
    RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [scalarMap_monomialFunction k L R S f g e,
    scalarMap_monomialFunction k L R S f g j]

/-- Restrict the fraction-ring map to the unchanged adjoin-of-ratios chart. -/
def scalarChartMap (j : Exponent σ) : chart k R g j →+* chart L S (f ∘ g) j := by
  let φ := scalarFractionMap k R S f hf
  apply RingHom.codRestrict (φ.comp (chart k R g j).val.toRingHom) _
  rintro ⟨z, hz⟩
  change φ z ∈ chart L S (f ∘ g) j
  rw [chart_eq_adjoin_ratios] at hz
  induction hz using Algebra.adjoin_induction with
  | mem z hz =>
      obtain ⟨e, rfl⟩ := hz
      rw [scalarFractionMap_ratio k L R S f hf g]
      exact Algebra.subset_adjoin (Or.inl ⟨e, rfl⟩)
  | algebraMap r =>
      have he : φ (algebraMap k (FractionRing R) r) =
          algebraMap L (FractionRing S) (algebraMap k L r) := by
        rw [IsScalarTower.algebraMap_apply k R (FractionRing R)]
        simp only [φ, scalarFractionMap, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
        rw [f.commutes, IsScalarTower.algebraMap_apply k L S]
        exact (IsScalarTower.algebraMap_apply L S (FractionRing S) _).symm
      rw [he]
      exact (chart L S (f ∘ g) j).algebraMap_mem _
  | add x y _ _ hx hy => simpa only [map_add] using add_mem hx hy
  | mul x y _ _ hx hy => simpa only [map_mul] using mul_mem hx hy

/-- The infinity coordinate is carried to the actual new infinity coordinate. -/
theorem scalarChartMap_infinityCoordinate (j : Exponent σ) :
    scalarChartMap k L R S f hf g j (infinityCoordinate k R g j) =
      infinityCoordinate L S (f ∘ g) j := by
  apply Subtype.ext
  change scalarFractionMap k R S f hf
    ((algebraMap R (FractionRing R) (monomialFunction k R g j))⁻¹) = _
  rw [map_inv₀]
  simp only [scalarFractionMap, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [scalarMap_monomialFunction k L R S f g j]
  rfl

/-- The map descends through the full infinity ideal, without taking radicals. -/
def scalarBoundaryMap (j : Exponent σ) :
    boundaryRing k R g j →+* boundaryRing L S (f ∘ g) j := by
  apply Ideal.Quotient.lift _
    ((Ideal.Quotient.mk _).comp (scalarChartMap k L R S f hf g j))
  intro z hz
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hle : Ideal.span {infinityCoordinate k R g j} ≤
      Ideal.comap (scalarChartMap k L R S f hf g j)
        (Ideal.span {infinityCoordinate L S (f ∘ g) j}) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨rfl⟩
    change scalarChartMap k L R S f hf g j (infinityCoordinate k R g j) ∈
      Ideal.span {infinityCoordinate L S (f ∘ g) j}
    rw [scalarChartMap_infinityCoordinate]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact hle hz

/-- Every original boundary coordinate is retained literally on the full quotient. -/
theorem scalarBoundaryMap_coordinate (j e : Exponent σ) :
    scalarBoundaryMap k L R S f hf g j (boundaryCoordinate k R g j e) =
      boundaryCoordinate L S (f ∘ g) j e := by
  change Ideal.Quotient.mk _ (scalarChartMap k L R S f hf g j
    ⟨ratio k R g j e, _⟩) = Ideal.Quotient.mk _ ⟨ratio L S (f ∘ g) j e, _⟩
  congr 1
  apply Subtype.ext
  exact scalarFractionMap_ratio k L R S f hf g j e

end QuadraticIncidence.InfinityChart
