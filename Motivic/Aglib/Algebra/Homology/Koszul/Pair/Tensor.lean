/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Homology.Koszul.Pair.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Tensoring the two-element Koszul complex

Tensoring the actual Koszul complex on `R` with an arbitrary `R`-module `M`
is explicitly isomorphic to the actual Koszul complex on `M`. The coordinate
isomorphism in degree one distributes tensor product across the two factors.
The signs and both differential squares are checked on pure tensors.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped ZeroObject TensorProduct

namespace Module.KoszulPair

variable {R : Type u} [CommRing R]
variable (M : Type u) [AddCommGroup M] [Module R M] (a b : R)

/-- The degree-one tensor-product coordinate identification. -/
noncomputable def tensorProdEquiv : M ⊗[R] (R × R) ≃ₗ[R] (M × M) :=
  (TensorProduct.prodRight R R M R R).trans
    ((TensorProduct.rid R M).prodCongr (TensorProduct.rid R M))

@[simp]
theorem tensorProdEquiv_tmul (m : M) (r : R × R) :
    tensorProdEquiv M (m ⊗ₜ[R] r) = (r.1 • m, r.2 • m) := rfl

/-- Degreewise identifications between the tensored ring Koszul complex and the module complex. -/
noncomputable def tensorXIso (n : ℕ) :
    (((tensoringLeft (ModuleCat R)).obj (ModuleCat.of R M)).mapHomologicalComplex
      (ComplexShape.down ℕ) |>.obj (chainComplex R a b)).X n ≅
        (chainComplex M a b).X n := by
  obtain (_ | _ | _ | n) := n
  · exact (TensorProduct.rid R M).toModuleIso
  · exact (tensorProdEquiv M).toModuleIso
  · exact (TensorProduct.rid R M).toModuleIso
  · exact (Functor.map_isZero ((tensoringLeft (ModuleCat R)).obj (ModuleCat.of R M))
      (isZero_zero (ModuleCat R))).isoZero

/-- Tensoring the ring Koszul complex gives the literal module Koszul complex. -/
noncomputable def tensorIso :
    (((tensoringLeft (ModuleCat R)).obj (ModuleCat.of R M)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (chainComplex R a b) ≅ chainComplex M a b := by
  refine HomologicalComplex.Hom.isoOfComponents (tensorXIso M a b) ?_
  intro i j hij
  have hi : j + 1 = i := hij
  subst i
  obtain (_ | _ | n) := j
  · apply ModuleCat.hom_ext
    refine TensorProduct.ext (LinearMap.ext fun m => LinearMap.ext fun r => ?_)
    change R × R at r
    change M at m
    change d₁ M a b (tensorProdEquiv M (m ⊗ₜ[R] r)) =
      TensorProduct.rid R M (m ⊗ₜ[R] d₁ R a b r)
    change a • (r.1 • m) + b • (r.2 • m) = (a * r.1 + b * r.2) • m
    simp only [smul_smul, add_smul]
  · apply ModuleCat.hom_ext
    refine TensorProduct.ext (LinearMap.ext fun m => LinearMap.ext fun r => ?_)
    change R at r
    change M at m
    change d₂ M a b (TensorProduct.rid R M (m ⊗ₜ[R] r)) =
      tensorProdEquiv M (m ⊗ₜ[R] d₂ R a b r)
    change (-(b • (r • m)), a • (r • m)) = ((-(b * r)) • m, (a * r) • m)
    simp only [smul_smul, neg_smul]
  · change (tensorXIso M a b (n + 3)).hom ≫
        (chainComplex M a b).d (n + 3) (n + 2) =
      (((tensoringLeft (ModuleCat R)).obj (ModuleCat.of R M)).map
        ((chainComplex R a b).d (n + 3) (n + 2))) ≫ (tensorXIso M a b (n + 2)).hom
    rw [chainComplex_d_add_three, chainComplex_d_add_three, Functor.map_zero,
      zero_comp, comp_zero]

end Module.KoszulPair
