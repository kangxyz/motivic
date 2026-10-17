/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Algebra.Homology.TorComparison.ExteriorMapQuasiIso
public import Motivic.Algebra.Homology.TorComparison.ExteriorRestrictionHomotopy
public import Motivic.Algebra.Homology.TorComparison.ExteriorModuleBicomplex
public import Motivic.Algebra.Homology.TorComparison.ExteriorModuleTotal

/-!
# The projective resolution of an exterior tensor product

Over an arbitrary field k, the actual signed exterior total complex of genuine
U- and V-projective resolutions is a projective resolution over U tensor_k V
of the literal exterior tensor module. Projectivity uses the actual exterior
algebra action on each summand. Exactness is proved after exact faithful scalar
restriction using explicit homotopy equivalences over k and the actual natural
comparison between restriction and totalization.

No finite-length resolution, flat support, Tor symmetry, or totalization
exactness axiom is assumed. This is a resolution construction, not yet the
ambient-change-of-rings Tor comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomologicalComplex
open scoped TensorProduct

universe u

namespace Motivic.TorComparison

variable {k U V : Type u} [Field k] [CommRing U] [CommRing V]
  [Algebra k U] [Algebra k V]

/-- The total map of the two literal exterior resolution augmentations is a
quasi-isomorphism over the full tensor-product algebra. -/
theorem exteriorAugmentations_quasiIso
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    QuasiIso (mapBifunctorMap P.π Q.π (ExteriorModule.bifunctor k U V)
      (ComplexShape.down ℕ)) := by
  let res := ModuleCat.restrictScalars (algebraMap k (U ⊗[k] V))
  let φ := (((ExteriorModule.bifunctor k U V).mapBifunctorHomologicalComplex
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)).map P.π).app Q.complex ≫
    (((ExteriorModule.bifunctor k U V).mapBifunctorHomologicalComplex
      (ComplexShape.down ℕ) (ComplexShape.down ℕ)).obj
      ((ChainComplex.single₀ (ModuleCat U)).obj M)).map Q.π
  have hfield : QuasiIso (mapBifunctorMap
      (((ModuleCat.restrictScalars (algebraMap k U)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map P.π)
      (((ModuleCat.restrictScalars (algebraMap k V)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map Q.π)
      (curriedTensor (ModuleCat k)) (ComplexShape.down ℕ)) :=
    (exteriorTotalHomotopyEquiv (curriedTensor (ModuleCat k)) (ComplexShape.down ℕ)
      (fieldRestrictionAugmentationHomotopyEquiv (k := k) P)
      (fieldRestrictionAugmentationHomotopyEquiv (k := k) Q)).quasiIso_hom
  have hmapped : QuasiIso (HomologicalComplex₂.total.map
      (((res.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
        (ComplexShape.down ℕ)).map φ) (ComplexShape.down ℕ)) := by
    let e₁ := HomologicalComplex₂.total.mapIso
      (ExteriorModule.scalarBicomplexIso k U V P.complex Q.complex) (ComplexShape.down ℕ)
    let e₂ := HomologicalComplex₂.total.mapIso
      (ExteriorModule.scalarBicomplexIso k U V
        ((ChainComplex.single₀ (ModuleCat U)).obj M)
        ((ChainComplex.single₀ (ModuleCat V)).obj N)) (ComplexShape.down ℕ)
    have hnat : HomologicalComplex₂.total.map
        (((res.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map φ) (ComplexShape.down ℕ) ≫ e₂.hom =
        e₁.hom ≫ mapBifunctorMap
          (((ModuleCat.restrictScalars (algebraMap k U)).mapHomologicalComplex
            (ComplexShape.down ℕ)).map P.π)
          (((ModuleCat.restrictScalars (algebraMap k V)).mapHomologicalComplex
            (ComplexShape.down ℕ)).map Q.π)
          (curriedTensor (ModuleCat k)) (ComplexShape.down ℕ) := by
      change HomologicalComplex₂.total.map
          (ExteriorModule.restrictedBicomplexMap k P.π Q.π) (ComplexShape.down ℕ) ≫
          HomologicalComplex₂.total.map
            (ExteriorModule.scalarBicomplexIso k U V
              ((ChainComplex.single₀ (ModuleCat U)).obj M)
              ((ChainComplex.single₀ (ModuleCat V)).obj N)).hom (ComplexShape.down ℕ) =
        HomologicalComplex₂.total.map
            (ExteriorModule.scalarBicomplexIso k U V P.complex Q.complex).hom
            (ComplexShape.down ℕ) ≫
          HomologicalComplex₂.total.map (ExteriorModule.baseBicomplexMap k P.π Q.π)
            (ComplexShape.down ℕ)
      rw [← HomologicalComplex₂.total.map_comp, ← HomologicalComplex₂.total.map_comp]
      exact congrArg (fun ψ => HomologicalComplex₂.total.map ψ (ComplexShape.down ℕ))
        (ExteriorModule.scalarBicomplexIso_naturality k P.π Q.π)
    have hcomp : QuasiIso (HomologicalComplex₂.total.map
        (((res.mapHomologicalComplex (ComplexShape.down ℕ)).mapHomologicalComplex
          (ComplexShape.down ℕ)).map φ) (ComplexShape.down ℕ) ≫ e₂.hom) := by
      rw [hnat]
      infer_instance
    exact quasiIso_of_comp_right _ e₂.hom
  exact exteriorTotalMap_quasiIso_of_map res (ComplexShape.down ℕ) φ

/-- The actual exterior total complex, with its literal tensor-product algebra
action, is a projective resolution of the exterior tensor module. -/
noncomputable def exteriorProjectiveResolution
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) :
    ProjectiveResolution (ExteriorModule.obj k U V M N) where
  complex := mapBifunctor P.complex Q.complex (ExteriorModule.bifunctor k U V)
    (ComplexShape.down ℕ)
  projective n := ExteriorModule.projective_total_X k U V (ComplexShape.down ℕ)
    P.complex Q.complex n
  π := mapBifunctorMap P.π Q.π (ExteriorModule.bifunctor k U V) (ComplexShape.down ℕ) ≫
    (exteriorSingleIso (ExteriorModule.bifunctor k U V) M N).hom
  quasiIso := by
    have := exteriorAugmentations_quasiIso (k := k) P Q
    exact quasiIso_comp
      (mapBifunctorMap P.π Q.π (ExteriorModule.bifunctor k U V) (ComplexShape.down ℕ))
      (exteriorSingleIso (ExteriorModule.bifunctor k U V) M N).hom

/-- Positive homological degrees of the literal exterior-algebra complex are exact. -/
theorem exteriorProjectiveResolution_exactAt_succ
    {M : ModuleCat.{u} U} {N : ModuleCat.{u} V}
    (P : ProjectiveResolution M) (Q : ProjectiveResolution N) (n : ℕ) :
    (mapBifunctor P.complex Q.complex (ExteriorModule.bifunctor k U V)
      (ComplexShape.down ℕ)).ExactAt (n + 1) :=
  (exteriorProjectiveResolution (k := k) P Q).complex_exactAt_succ n

end Motivic.TorComparison
