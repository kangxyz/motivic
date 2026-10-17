/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.MixedBaseFunctor
public import Motivic.Algebra.Homology.TorComparison.ExteriorModuleBicomplex
public import Motivic.Algebra.Homology.TorComparison.ExteriorMapTotal
public import Motivic.Algebra.Homology.TorComparison.FlatBaseChange

/-!
# The mixed-base comparison on actual signed total complexes

The degreewise tensor comparison commutes with both actual differentials.
It therefore identifies the genuine scalar-extended exterior bicomplex with
the ordinary tensor bicomplex of the two scalar-extended complexes. Scalar
extension preserves the diagonal coproducts, so the comparison also identifies
the actual signed total complexes. None of these comparisons requires flatness.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory HomologicalComplex
open scoped TensorProduct

universe u

namespace Motivic.TorComparison.MixedBase

variable (k U V Q : Type u) [CommRing k] [CommRing U] [CommRing V] [CommRing Q]
  [Algebra k U] [Algebra k V] (μ : U ⊗[k] V →+* Q)

/-- Extend both levels of the actual exterior bicomplex along the ambient map. -/
abbrev extendedExteriorBicomplex (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) :=
  exteriorMapBicomplex (ModuleCat.extendScalars μ) (ExteriorModule.exteriorBicomplex k U V K L)

/-- The ordinary tensor bicomplex of the two induced scalar extensions. -/
abbrev extendedFactorsBicomplex (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) :=
  (((curriedTensor (ModuleCat.{u} Q)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
      (((ModuleCat.extendScalars (leftMap k U V Q μ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K)).obj
      (((ModuleCat.extendScalars (rightMap k U V Q μ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj L)

/-- The genuine mixed-base bicomplex isomorphism, with both differential squares proved. -/
def bicomplexIso (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) :
    extendedExteriorBicomplex k U V Q μ K L ≅ extendedFactorsBicomplex k U V Q μ K L :=
  Hom.isoOfComponents
    (fun i ↦ Hom.isoOfComponents
      (fun j ↦ iso μ (K.X i) (L.X j)) (by
        intro j j' _
        apply ModuleCat.hom_ext
        apply source_ext μ (K.X i) (L.X j)
        intro q m n
        rfl)) (by
      intro i i' _
      ext1 j
      apply ModuleCat.hom_ext
      apply source_ext μ (K.X i) (L.X j)
      intro q m n
      rfl)

/-- Every bicomplex component is the constructed mixed-base module comparison. -/
@[simp] theorem bicomplexIso_hom_f_f (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) (i j : ℕ) :
    ((bicomplexIso k U V Q μ K L).hom.f i).f j = (iso μ (K.X i) (L.X j)).hom := rfl

/-- Totalizing the actual bicomplex isomorphism respects the signed differential. -/
def totalBicomplexIso (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) :
    (extendedExteriorBicomplex k U V Q μ K L).total (ComplexShape.down ℕ) ≅
      (extendedFactorsBicomplex k U V Q μ K L).total (ComplexShape.down ℕ) :=
  HomologicalComplex₂.total.mapIso (bicomplexIso k U V Q μ K L) (ComplexShape.down ℕ)

/-- Scalar extension of the actual exterior total equals the actual total tensor
of the two scalar-extended complexes, without any flatness hypothesis. -/
def totalIso (K : ChainComplex (ModuleCat.{u} U) ℕ)
    (L : ChainComplex (ModuleCat.{u} V) ℕ) :
    ((ModuleCat.extendScalars μ).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        ((ExteriorModule.exteriorBicomplex k U V K L).total (ComplexShape.down ℕ)) ≅
      (extendedFactorsBicomplex k U V Q μ K L).total (ComplexShape.down ℕ) :=
  (exteriorMapTotalIso (ModuleCat.extendScalars μ)
    (ExteriorModule.exteriorBicomplex k U V K L) (ComplexShape.down ℕ)).symm ≪≫
      totalBicomplexIso k U V Q μ K L

variable {k U V Q}

/-- The scalar-extended map of genuine exterior bicomplexes. -/
abbrev extendedExteriorMap {K K' : ChainComplex (ModuleCat.{u} U) ℕ}
    {L L' : ChainComplex (ModuleCat.{u} V) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    extendedExteriorBicomplex k U V Q μ K L ⟶ extendedExteriorBicomplex k U V Q μ K' L' :=
  (((ModuleCat.extendScalars μ).mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
    (ComplexShape.down ℕ)).map (ExteriorModule.exteriorBicomplexMap k f g)

/-- The map of ordinary tensor bicomplexes of the extended factors. -/
abbrev extendedFactorsMap {K K' : ChainComplex (ModuleCat.{u} U) ℕ}
    {L L' : ChainComplex (ModuleCat.{u} V) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    extendedFactorsBicomplex k U V Q μ K L ⟶ extendedFactorsBicomplex k U V Q μ K' L' :=
  (((curriedTensor (ModuleCat.{u} Q)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map
      (((ModuleCat.extendScalars (leftMap k U V Q μ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map f)).app
      (((ModuleCat.extendScalars (rightMap k U V Q μ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj L) ≫
  (((curriedTensor (ModuleCat.{u} Q)).mapBifunctorHomologicalComplex
    (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
      (((ModuleCat.extendScalars (leftMap k U V Q μ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj K')).map
      (((ModuleCat.extendScalars (rightMap k U V Q μ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map g)

/-- Naturality of the actual bicomplex comparison in both chain maps. -/
theorem bicomplexIso_naturality {K K' : ChainComplex (ModuleCat.{u} U) ℕ}
    {L L' : ChainComplex (ModuleCat.{u} V) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    extendedExteriorMap μ f g ≫ (bicomplexIso k U V Q μ K' L').hom =
      (bicomplexIso k U V Q μ K L).hom ≫ extendedFactorsMap μ f g := by
  ext1 i
  ext1 j
  apply ModuleCat.hom_ext
  apply source_ext μ (K.X i) (L.X j)
  intro q m n
  rfl

/-- Naturality survives the actual signed totalization. -/
theorem totalBicomplexIso_naturality {K K' : ChainComplex (ModuleCat.{u} U) ℕ}
    {L L' : ChainComplex (ModuleCat.{u} V) ℕ} (f : K ⟶ K') (g : L ⟶ L') :
    HomologicalComplex₂.total.map (extendedExteriorMap μ f g) (ComplexShape.down ℕ) ≫
        (totalBicomplexIso k U V Q μ K' L').hom =
      (totalBicomplexIso k U V Q μ K L).hom ≫
        HomologicalComplex₂.total.map (extendedFactorsMap μ f g) (ComplexShape.down ℕ) := by
  change HomologicalComplex₂.total.map _ _ ≫ HomologicalComplex₂.total.map _ _ =
    HomologicalComplex₂.total.map _ _ ≫ HomologicalComplex₂.total.map _ _
  rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp,
    bicomplexIso_naturality]

end Motivic.TorComparison.MixedBase
