/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChangeTorComposition

/-!
# The identity law for canonical flat Tor base change

The identity-ring comparison is the canonical scalar-extension unitor on Tor,
with the same unitor on both module arguments.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TensorProduct

universe u

namespace ModuleCat.TorComparison

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- The scalar-extension unitor respects the actual tensorator. -/
theorem extendScalarsId_tensorator (M N : ModuleCat.{u} R) :
    Functor.OplaxMonoidal.δ (ModuleCat.extendScalars (RingHom.id R)) M N ≫
        ((ModuleCat.extendScalarsId R).hom.app M ⊗ₘ
          (ModuleCat.extendScalarsId R).hom.app N) =
      (ModuleCat.extendScalarsId R).hom.app (M ⊗ N) := by
  apply ((ModuleCat.extendRestrictScalarsAdj (RingHom.id R)).homEquiv _ _).injective
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  simp only [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply, ModuleCat.comp_apply]
  erw [ModuleCat.extendScalars_δ_tmul (RingHom.id R) M N m n,
    ModuleCat.MonoidalCategory.tensorHom_tmul]
  exact (congrArg₂ (fun (x : M) (y : N) => x ⊗ₜ[R] y)
    (ModuleCat.extendScalarsId_hom_app_one_tmul M m)
    (ModuleCat.extendScalarsId_hom_app_one_tmul N n)).trans
      (ModuleCat.extendScalarsId_hom_app_one_tmul (M ⊗ N) (m ⊗ₜ[R] n)).symm

/-- The actual tensor-complex morphism induced by the scalar-extension unitor. -/
noncomputable def extendTensorIdComparison (M : ModuleCat.{u} R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    ((tensorLeft ((ModuleCat.extendScalars (RingHom.id R)).obj M)).mapHomologicalComplex _).obj
        (((ModuleCat.extendScalars (RingHom.id R)).mapHomologicalComplex _).obj K) ⟶
      ((tensorLeft M).mapHomologicalComplex _).obj K :=
  (NatTrans.mapHomologicalComplex
      ((tensoringLeft (ModuleCat R)).map ((ModuleCat.extendScalarsId R).hom.app M)) _).app
        (((ModuleCat.extendScalars (RingHom.id R)).mapHomologicalComplex _).obj K) ≫
    ((tensorLeft M).mapHomologicalComplex _).map
      ((NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsId R).hom _).app K)

/-- The chain tensorator agrees with the scalar unitor. -/
theorem extendTensorComplexIso_id (M : ModuleCat.{u} R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    (extendTensorComplexIso (RingHom.id R) M K).hom ≫ extendTensorIdComparison M K =
      (NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsId R).hom _).app
        (((tensorLeft M).mapHomologicalComplex _).obj K) := by
  ext i : 1
  have h := extendScalarsId_tensorator M (K.X i)
  rw [tensorHom_def] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- The actual flat homology comparison satisfies the scalar identity law. -/
theorem flatExtendHomologyIso_id (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (flatExtendHomologyIso (RingHom.id R) (RingHom.Flat.id R) K n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsId R).hom _).app K) n =
      (ModuleCat.extendScalarsId R).hom.app (K.homology n) := by
  let := ModuleCat.preservesFiniteLimits_extendScalars_of_flat (RingHom.Flat.id R)
  have h := exactMapHomologyIso_natTrans (ModuleCat.extendScalars (RingHom.id R))
    (𝟭 (ModuleCat R)) (ModuleCat.extendScalarsId R).hom (K.sc n)
  have hi : (K.sc n).mapHomologyIso (𝟭 (ModuleCat R)) = Iso.refl _ :=
    Iso.ext (exactMapHomologyIso_id (K.sc n))
  rw [hi] at h
  erw [Category.comp_id] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- The actual flat tensor-homology comparison satisfies the scalar identity law. -/
theorem flatExtendTensorHomologyIso_id (M : ModuleCat.{u} R)
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    (flatExtendTensorHomologyIso (RingHom.id R) (RingHom.Flat.id R) M K n).hom ≫
        HomologicalComplex.homologyMap (extendTensorIdComparison M K) n =
      (ModuleCat.extendScalarsId R).hom.app
        ((((tensorLeft M).mapHomologicalComplex _).obj K).homology n) := by
  have hc := congrArg ((HomologicalComplex.homologyFunctor (ModuleCat R) _ n).map)
    (extendTensorComplexIso_id M K)
  simp only [Functor.map_comp] at hc
  simp only [flatExtendTensorHomologyIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  exact (congrArg ((flatExtendHomologyIso (RingHom.id R) (RingHom.Flat.id R)
    (((tensorLeft M).mapHomologicalComplex _).obj K) n).hom ≫ ·) hc).trans
      (flatExtendHomologyIso_id (((tensorLeft M).mapHomologicalComplex _).obj K) n)

/-- The scalar unitor is a map of the actual extended projective resolutions. -/
theorem flatExtendProjectiveResolution_id_commutes {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) :
    ((NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsId R).hom _).app
      P.complex).f 0 ≫ P.π.f 0 =
      (flatExtendProjectiveResolution (RingHom.id R) (RingHom.Flat.id R) P).π.f 0 ≫
        (ModuleCat.extendScalarsId R).hom.app N :=
  ((ModuleCat.extendScalarsId R).hom.naturality (P.π.f 0)).symm

set_option backward.isDefEq.respectTransparency false in
/-- The scalar unitor intertwines the actual Tor resolution comparisons. -/
theorem torResolutionIso_id (M : ModuleCat.{u} R) {N : ModuleCat.{u} R}
    (P : ProjectiveResolution N) (n : ℕ) :
    ((flatExtendProjectiveResolution (RingHom.id R) (RingHom.Flat.id R) P).isoLeftDerivedObj
        (tensorLeft ((ModuleCat.extendScalars (RingHom.id R)).obj M)) n).inv ≫
        ((Tor (ModuleCat R) n).map ((ModuleCat.extendScalarsId R).hom.app M)).app
          ((ModuleCat.extendScalars (RingHom.id R)).obj N) ≫
        ((Tor (ModuleCat R) n).obj M).map ((ModuleCat.extendScalarsId R).hom.app N) =
      HomologicalComplex.homologyMap (extendTensorIdComparison M P.complex) n ≫
        (P.isoLeftDerivedObj (tensorLeft M) n).inv := by
  erw [torResolutionIso_inv_naturality_left_assoc ((ModuleCat.extendScalarsId R).hom.app M)
    (flatExtendProjectiveResolution (RingHom.id R) (RingHom.Flat.id R) P) n]
  erw [ProjectiveResolution.isoLeftDerivedObj_inv_naturality
    ((ModuleCat.extendScalarsId R).hom.app N)
    (flatExtendProjectiveResolution (RingHom.id R) (RingHom.Flat.id R) P) P
    ((NatTrans.mapHomologicalComplex (ModuleCat.extendScalarsId R).hom _).app P.complex)
    (flatExtendProjectiveResolution_id_commutes P) (tensorLeft M) n]
  dsimp only [extendTensorIdComparison, Functor.comp_map, HomologicalComplex.homologyFunctor]
  rw [HomologicalComplex.homologyMap_comp, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Canonical flat Tor base change along the identity ring map is the scalar unitor. -/
theorem flatBaseChangeTorIso_hom_id (M N : ModuleCat.{u} R) (n : ℕ) :
    (flatBaseChangeTorIso (RingHom.id R) (RingHom.Flat.id R) M N n).hom ≫
        ((Tor (ModuleCat R) n).map ((ModuleCat.extendScalarsId R).hom.app M)).app
          ((ModuleCat.extendScalars (RingHom.id R)).obj N) ≫
        ((Tor (ModuleCat R) n).obj M).map ((ModuleCat.extendScalarsId R).hom.app N) =
      (ModuleCat.extendScalarsId R).hom.app (((Tor (ModuleCat R) n).obj M).obj N) := by
  let P := projectiveResolution N
  rw [← flatBaseChangeTorIsoOfResolution_eq_flatBaseChangeTorIso
    (RingHom.id R) (RingHom.Flat.id R) M P n]
  simp only [flatBaseChangeTorIsoOfResolution, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Category.assoc]
  erw [torResolutionIso_id M P n]
  have h := congrArg (· ≫ (P.isoLeftDerivedObj (tensorLeft M) n).inv)
    (flatExtendTensorHomologyIso_id M P.complex n)
  simp only [Category.assoc] at h
  erw [h]
  erw [(ModuleCat.extendScalarsId R).hom.naturality_assoc
    (P.isoLeftDerivedObj (tensorLeft M) n).hom]
  dsimp only [Functor.id_map]
  erw [Iso.hom_inv_id, Category.comp_id]
  rfl

end ModuleCat.TorComparison
