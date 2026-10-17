/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.RingTheory.Bertini.ClosedPointMovingCoefficients
public import Motivic.Aglib.RingTheory.Bertini.QuadraticSelectedPointOpen
public import Motivic.Aglib.RingTheory.Bertini.QuadraticIncidenceBaseChange
public import Motivic.Aglib.RingTheory.Bertini.QuadraticParameterBaseChange
public import Mathlib.RingTheory.Flat.Basic

/-! # Actual field-valued diagonal points and cotangent scalar extension -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Module TensorProduct KaehlerDifferential MvPolynomial
universe u v
namespace QuadraticIncidence
namespace ClosedPoint
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  (p : PrimeSpectrum R) (K : Type u) [Field K]
  [Algebra k K] [Algebra R K] [Algebra (CoefficientRing k R p) K]
  [IsScalarTower k (CoefficientRing k R p) K]
  [IsScalarTower R (CoefficientRing k R p) K]

/-- The residue-field map is the original right tensor inclusion followed by the point. -/
def residueFieldMap : p.asIdeal.ResidueField →ₐ[k] K :=
  (IsScalarTower.toAlgHom k (CoefficientRing k R p) K).comp
    Algebra.TensorProduct.includeRight

/-- Agreement on the original generators forces the actual structural map to factor
through this original residue-field map. -/
theorem residueFieldMap_comp (σ : Type u) (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (hdiag : ∀ j, algebraMap R K (g j) =
      algebraMap (CoefficientRing k R p) K (selectedValue k R p (g j))) :
    (residueFieldMap k R p K).toRingHom.comp (algebraMap R p.asIdeal.ResidueField) =
      algebraMap R K := by
  have he : (residueFieldMap k R p K).comp
      (IsScalarTower.toAlgHom k R p.asIdeal.ResidueField) =
      (IsScalarTower.toAlgHom k (CoefficientRing k R p) K).comp
        (IsScalarTower.toAlgHom k R (CoefficientRing k R p)) := by
    apply AlgHom.ext_of_adjoin_eq_top hg
    rintro _ ⟨j, rfl⟩
    change algebraMap (CoefficientRing k R p) K (selectedValue k R p (g j)) =
      algebraMap (CoefficientRing k R p) K (algebraMap R (CoefficientRing k R p) (g j))
    rw [← IsScalarTower.algebraMap_apply R (CoefficientRing k R p) K]
    exact (hdiag j).symm
  ext r
  have hr := DFunLike.congr_fun he r
  change residueFieldMap k R p K (algebraMap R p.asIdeal.ResidueField r) = _ at hr
  exact hr.trans (IsScalarTower.algebraMap_apply R (CoefficientRing k R p) K r).symm

/-- The required tensor-cancellation tower is proved from diagonal membership. -/
theorem diagonal_scalarTower (σ : Type u) (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤)
    (hdiag : ∀ j, algebraMap R K (g j) =
      algebraMap (CoefficientRing k R p) K (selectedValue k R p (g j))) :
    letI : Algebra p.asIdeal.ResidueField K := (residueFieldMap k R p K).toRingHom.toAlgebra
    IsScalarTower R p.asIdeal.ResidueField K := by
  let : Algebra p.asIdeal.ResidueField K := (residueFieldMap k R p K).toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  exact (residueFieldMap_comp k R p K σ g hg hdiag).symm

end ClosedPoint

section Extension
variable (k R L K : Type u) [Field k] [CommRing R] [Field L] [Field K]
  [Algebra k R] [Algebra R L] [Algebra R K] [Algebra L K] [IsScalarTower R L K]
  {σ : Type u} [Fintype σ]

/-- Genuine extension-field linear independence after the actual cotangent cancellation. -/
theorem independent_residueGradient_baseChange {ι : Type v}
    (g : σ → R) (v : ι → σ → L)
    (hv : LinearIndependent L (fun i => residueGeneratorGradient k R L g (v i))) :
    LinearIndependent K (fun i => residueGeneratorGradient k R K g (algebraMap L K ∘ v i)) := by
  have h := Module.Flat.linearIndependent_one_tmul (S := K) hv
  have h' := h.map' (AlgebraTensorModule.cancelBaseChange R L K K Ω[R⁄k]).toLinearMap
    (LinearMap.ker_eq_bot.mpr (AlgebraTensorModule.cancelBaseChange R L K K Ω[R⁄k]).injective)
  simpa only [Function.comp_def, LinearEquiv.coe_coe,
    baseChange_residueGeneratorGradient] using h'

/-- The original ground-field coefficient tuple remains unchanged under field extension. -/
theorem independent_parameterTuple_baseChange [Algebra k L] [Algebra k K]
    [IsScalarTower k L K] (g : σ → R) (d : ℕ)
    (c : Fin d × Exponent σ → k)
    (hc : LinearIndependent L (fun i => residueGeneratorGradient k R L g
      (fun j => eval (fun l => algebraMap R L (g l))
        (pderiv j (parameterTuple L σ d (algebraMap k L ∘ c) i).val)))) :
    LinearIndependent K (fun i => residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l))
        (pderiv j (parameterTuple K σ d (algebraMap k K ∘ c) i).val))) := by
  have h := independent_residueGradient_baseChange k R L K g _ hc
  have hb : (algebraMap L K ∘ fun l => algebraMap R L (g l)) =
      fun l => algebraMap R K (g l) := by
    funext l
    exact (IsScalarTower.algebraMap_apply R L K (g l)).symm
  have hp : algebraMap L K ∘ (algebraMap k L ∘ c) = algebraMap k K ∘ c := by
    funext q
    exact (IsScalarTower.algebraMap_apply k L K (c q)).symm
  convert h using 1
  ext i
  congr 1
  funext j
  simp only [Function.comp_apply]
  rw [map_eval, ← pderiv_map, parameterTuple_map, hp, hb]

end Extension

namespace ClosedPoint
variable (k R : Type u) [Field k] [CommRing R] [Algebra k R]
  (p : PrimeSpectrum R) (K : Type u) [Field K]
  [Algebra k K] [Algebra R K] [Algebra (CoefficientRing k R p) K]
  [IsScalarTower k (CoefficientRing k R p) K]
  [IsScalarTower R (CoefficientRing k R p) K]
  {σ : Type u} [Fintype σ]

/-- Every actual field-valued diagonal point inherits the selected-point independence,
with the literal original coefficient tuple and the original moving cotangent fiber. -/
theorem independent_parameterTuple_at_diagonal (g : σ → R)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (c : Fin d × Exponent σ → k)
    (hc : LinearIndependent p.asIdeal.ResidueField
      (fun i => residueGeneratorGradient k R p.asIdeal.ResidueField g
        (fun j => eval (fun l => algebraMap R p.asIdeal.ResidueField (g l))
          (pderiv j (parameterTuple p.asIdeal.ResidueField σ d
            (algebraMap k p.asIdeal.ResidueField ∘ c) i).val))))
    (hdiag : ∀ j, algebraMap R K (g j) =
      algebraMap (CoefficientRing k R p) K (selectedValue k R p (g j))) :
    LinearIndependent K (fun i => residueGeneratorGradient k R K g
      (fun j => eval (fun l => algebraMap R K (g l))
        (pderiv j (parameterTuple K σ d (algebraMap k K ∘ c) i).val))) := by
  let : Algebra p.asIdeal.ResidueField K := (residueFieldMap k R p K).toRingHom.toAlgebra
  let : IsScalarTower R p.asIdeal.ResidueField K :=
    diagonal_scalarTower k R p K σ g hg hdiag
  let : IsScalarTower k p.asIdeal.ResidueField K :=
    IsScalarTower.of_algebraMap_eq fun r => (residueFieldMap k R p K).commutes r |>.symm
  exact independent_parameterTuple_baseChange k R p.asIdeal.ResidueField K g d c hc

end ClosedPoint
end QuadraticIncidence
