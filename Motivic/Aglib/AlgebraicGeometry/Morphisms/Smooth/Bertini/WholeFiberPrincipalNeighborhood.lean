/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Smooth.PrincipalNeighborhood
public import Motivic.Aglib.RingTheory.Bertini.WholeFiberSmoothProjection

/-!
# Whole-fiber principal neighborhoods
-/

@[expose] public noncomputable section

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
namespace QuadraticIncidence

/-- The image of an original closed finite-type point is closed, without a
rationality assumption on its residue field. -/
theorem comap_closedPoint_isMaximal (k A R : Type u) [Field k]
    [CommRing A] [CommRing R] [Algebra k A] [Algebra k R] [Algebra.FiniteType k R]
    (φ : A →ₐ[k] R) (p : PrimeSpectrum R) [p.asIdeal.IsMaximal] :
    (Ideal.comap φ.toRingHom p.asIdeal).IsMaximal := by
  let s : A →ₐ[k] p.asIdeal.ResidueField :=
    (IsScalarTower.toAlgHom k R p.asIdeal.ResidueField).comp φ
  let : Algebra A p.asIdeal.ResidueField := s.toRingHom.toAlgebra
  let : IsScalarTower k A p.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq' s.comp_algebraMap.symm
  let := ClosedPoint.residueField_finite k R p
  let : Algebra.IsIntegral A p.asIdeal.ResidueField := Algebra.IsIntegral.tower_top k
  have H := Algebra.ker_algebraMap_isMaximal_of_isIntegral A p.asIdeal.ResidueField
  change (RingHom.ker s.toRingHom).IsMaximal at H
  have he : RingHom.ker s.toRingHom = Ideal.comap φ.toRingHom p.asIdeal := by
    ext a
    change algebraMap R p.asIdeal.ResidueField (φ a) = 0 ↔ φ a ∈ p.asIdeal
    exact p.asIdeal.algebraMap_residueField_eq_zero
  exact he ▸ H

end QuadraticIncidence

namespace QuadraticIncidence

/-- Congruence to one modulo the original fiber ideal retains every fiber point. -/
theorem not_mem_of_sub_one_mem_fiber {A R : Type u} [CommRing A] [CommRing R]
    (φ : A →+* R) (p x : PrimeSpectrum R) (r : R)
    (hr : r - 1 ∈ Ideal.map φ (Ideal.comap φ p.asIdeal))
    (hx : Ideal.comap φ p.asIdeal = Ideal.comap φ x.asIdeal) : r ∉ x.asIdeal := by
  have hle : Ideal.map φ (Ideal.comap φ p.asIdeal) ≤ x.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr hx.le
  intro h
  have h1 : (1 : R) ∈ x.asIdeal := by
    have := x.asIdeal.sub_mem h (hle hr)
    simpa only [sub_sub_cancel] using this
  exact x.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)

/-- One principal affine neighborhood retains the entire original closed fiber,
not merely the selected point. -/
theorem exists_closedFiber_principal_smooth (k A R : Type u) [Field k]
    [CommRing A] [CommRing R] [Algebra k A] [Algebra k R] [Algebra.FiniteType k R]
    (φ : A →ₐ[k] R) (p : PrimeSpectrum R) [p.asIdeal.IsMaximal] (n : ℕ)
    (h : ∀ x : PrimeSpectrum R,
      Ideal.comap φ.toRingHom p.asIdeal = Ideal.comap φ.toRingHom x.asIdeal →
      ∃ a ∉ x.asIdeal, SmoothOfRelativeDimension n
        (Spec.map (CommRingCat.ofHom
          ((algebraMap R (Localization.Away a)).comp φ.toRingHom)))) :
    ∃ r : R, r - 1 ∈ Ideal.map φ.toRingHom (Ideal.comap φ.toRingHom p.asIdeal) ∧
      (∀ x : PrimeSpectrum R,
        Ideal.comap φ.toRingHom p.asIdeal = Ideal.comap φ.toRingHom x.asIdeal →
        r ∉ x.asIdeal) ∧
      SmoothOfRelativeDimension n
        ((Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) ≫
          Spec.map (CommRingCat.ofHom φ.toRingHom)) := by
  have hm := comap_closedPoint_isMaximal k A R φ p
  obtain ⟨r, hr, hs⟩ := exists_principal_smooth_neighborhood A R φ.toRingHom
    (Ideal.map φ.toRingHom (Ideal.comap φ.toRingHom p.asIdeal)) n (by
      intro x hx
      exact h x (hm.eq_of_le
        (Ideal.IsPrime.ne_top (inferInstance : (Ideal.comap φ.toRingHom x.asIdeal).IsPrime))
        (Ideal.map_le_iff_le_comap.mp hx)))
  exact ⟨r, hr, fun x hx => not_mem_of_sub_one_mem_fiber φ.toRingHom p x r hr hx, hs⟩

/-- The actual quadratic tuple has a single principal affine smooth neighborhood
of its entire selected fiber, preserving any prescribed parameter open. -/
theorem exists_wholeFiber_principal_smooth_projection (k R : Type u) [Field k] [Infinite k]
    [CommRing R] [IsDomain R] [Algebra k R] [Algebra.Smooth k R]
    (p : PrimeSpectrum R) [p.asIdeal.IsMaximal]
    {σ : Type u} [Fintype σ] (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k R = (d + 1 : ℕ))
    (q : MvPolynomial (Fin d × Exponent σ) k) (hq : q ≠ 0) :
    ∃ c : Fin d × Exponent σ → k, MvPolynomial.eval c q ≠ 0 ∧
      let f : Fin d → R := fun i => MvPolynomial.aeval g (parameterTuple k σ d c i).val
      let φ := (MvPolynomial.aeval (R := k) f).toRingHom
      ∃ r : R, r - 1 ∈ Ideal.map φ (Ideal.comap φ p.asIdeal) ∧
        (∀ x : PrimeSpectrum R, Ideal.comap φ p.asIdeal = Ideal.comap φ x.asIdeal →
          r ∉ x.asIdeal) ∧
        SmoothOfRelativeDimension 1
          ((Scheme.Opens.ι (X := Spec (.of R)) (PrimeSpectrum.basicOpen r)) ≫
            Spec.map (CommRingCat.ofHom φ)) := by
  obtain ⟨c, hc, H⟩ := exists_wholeFiber_smooth_projection k R p g hg d hd q hq
  refine ⟨c, hc, ?_⟩
  exact exists_closedFiber_principal_smooth k (MvPolynomial (Fin d) k) R
    (MvPolynomial.aeval (fun i => MvPolynomial.aeval g (parameterTuple k σ d c i).val)) p 1 H

end QuadraticIncidence
