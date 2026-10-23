/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Semilocal
public import Motivic.Aglib.LinearAlgebra.InvertibleModule.PrescribedTrivialization
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-! # Prescribed boundary coordinates of actual affine line bundles -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- The actual global sections of an affine line bundle have rank one at every prime. -/
theorem rankAtStalk_globalSections_eq_one (R : CommRingCat.{u})
    (L : LineBundle (Spec R)) (p : PrimeSpectrum R) :
    Module.rankAtStalk (moduleSpecΓFunctor.obj L.val) p = 1 := by
  have : IsFiniteLocallyFree (Spec R) L.val :=
    finiteLocallyFree_of_isLocallyRankOne L.val L.property
  have : L.val.IsLocallyFree := lineBundle_isLocallyFree (Spec R) L
  have : Module.Finite R (moduleSpecΓFunctor.obj L.val) :=
    finite_globalSections_of_finiteLocallyFree R L.val
  have : Module.Projective R (moduleSpecΓFunctor.obj L.val) :=
    projective_globalSections_of_finiteLocallyFree R L.val
  rw [← Ideal.finrank_fiber_eq_rankAtStalk]
  exact finrank_baseChange_globalSections_eq_one R L.val L.property p.asIdeal.ResidueField

/-- Restrict a morphism into the structure module using the canonical unit comparison. -/
def pullbackUnitMap {X Y : Scheme.{u}} (f : X ⟶ Y) {M : Y.Modules}
    (a : M ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    (Scheme.Modules.pullback f).obj M ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (Scheme.Modules.pullback f).map a ≫ (pullbackUnitIso f).hom

/-- The actual restriction of a global functional respects composition,
including the original pullback-composition and structure-module maps. -/
theorem pullbackUnitMap_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (a : M ⟶ SheafOfModules.unit Z.ringCatSheaf) :
    ((Scheme.Modules.pullbackComp f g).app M).hom ≫ pullbackUnitMap (f ≫ g) a =
      pullbackUnitMap f (pullbackUnitMap g a) := by
  dsimp only [pullbackUnitMap]
  rw [Functor.map_comp, ← Category.assoc]
  erw [← (Scheme.Modules.pullbackComp f g).hom.naturality]
  simp only [Functor.comp_map, Category.assoc]
  rw [pullbackUnitIso_comp]

/-- The original affine pullback is identified with the tensor of its actual
sections. The counit and pullback comparisons are retained, rather than
replacing the line bundle by an unrelated isomorphic model. -/
def affinePullbackTensorIso (R S : CommRingCat.{u}) [Algebra R S]
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj M ≅
      tilde (ModuleCat.of S (S ⊗[R] moduleSpecΓFunctor.obj M)) :=
  (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapIso
      (asIso M.fromTildeΓ).symm ≪≫
    (tildePullbackIso (CommRingCat.ofHom (algebraMap R S))).app
      (moduleSpecΓFunctor.obj M) ≪≫
    (tilde.functor S).mapIso
      (ModuleCat.extendScalarsAlgebraIso R S (moduleSpecΓFunctor.obj M))

/-- Extract the exact prescribed boundary coordinate by full faithfulness of
the associated-sheaf functor. -/
def prescribedBoundaryCoordinate (R S : CommRingCat.{u}) [Algebra R S]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (e : (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj M ≅
      SheafOfModules.unit (Spec S).ringCatSheaf) :
    S ⊗[R] moduleSpecΓFunctor.obj M ≃ₗ[S] S :=
  ((tilde.functor S).preimageIso
    ((affinePullbackTensorIso R S M).symm ≪≫ e ≪≫ tildeSelf.symm)).toLinearEquiv

/-- Reconstruction is equality with the specified isomorphism itself,
not just existence of some boundary trivialization. -/
theorem prescribedBoundaryCoordinate_reconstruct (R S : CommRingCat.{u}) [Algebra R S]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (e : (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj M ≅
      SheafOfModules.unit (Spec S).ringCatSheaf) :
    affinePullbackTensorIso R S M ≪≫
        (tilde.functor S).mapIso (prescribedBoundaryCoordinate R S M e).toModuleIso ≪≫
        tildeSelf = e := by
  apply Iso.ext
  change (affinePullbackTensorIso R S M).hom ≫
    (tilde.functor S).map ((tilde.functor S).preimage
      ((affinePullbackTensorIso R S M).inv ≫ e.hom ≫ tildeSelf.inv)) ≫ tildeSelf.hom = e.hom
  have h := (tilde.functor S).map_preimage
    ((affinePullbackTensorIso R S M).inv ≫ e.hom ≫ tildeSelf.inv)
  erw [h]
  simp

/-- Scalar extension of a functional is determined by its values on the
original module elements, with the scalar-extension comparisons explicit. -/
theorem extendScalars_functional_eq (R S : CommRingCat.{u}) [Algebra R S]
    (N : ModuleCat.{u} R) (f : N ⟶ ModuleCat.of R R)
    (e : S ⊗[R] N ≃ₗ[S] S)
    (h : ∀ m : N, algebraMap R S (f m) = e (1 ⊗ₜ[R] m)) :
    (ModuleCat.extendScalars (algebraMap R S)).map f ≫
        (ModuleCat.extendScalarsAlgebraIso R S (ModuleCat.of R R)).hom ≫
        (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso.hom =
      (ModuleCat.extendScalarsAlgebraIso R S N).hom ≫ e.toModuleIso.hom := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (TensorProduct.AlgebraTensorModule.rid R S S)
      ((ModuleCat.extendScalarsAlgebraIso R S (ModuleCat.of R R)).hom
        (((ModuleCat.extendScalars (algebraMap R S)).map f)
          ((1 : S) ⊗ₜ[R,algebraMap R S] m))) =
    e ((ModuleCat.extendScalarsAlgebraIso R S N).hom ((1 : S) ⊗ₜ[R,algebraMap R S] m))
  rw [ModuleCat.ExtendScalars.map_tmul, ModuleCat.extendScalarsAlgebraIso_tmul,
    ModuleCat.extendScalarsAlgebraIso_tmul]
  rw [TensorProduct.AlgebraTensorModule.rid_tmul, Algebra.smul_def]
  simpa only [mul_one] using h m

/-- A functional which is invertible after principal localization gives an
actual isomorphism after categorical scalar extension. -/
theorem isIso_extendScalars_of_localized_coordinate (R : CommRingCat.{u})
    (N : ModuleCat.{u} R) (f : N ⟶ ModuleCat.of R R) (r : R)
    (d : LocalizedModule.Away r N ≃ₗ[Localization.Away r] Localization.Away r)
    (hd : ∀ m : N,
      d (LocalizedModule.mkLinearMap (Submonoid.powers r) N m) =
        algebraMap R (Localization.Away r) (f m)) :
    IsIso ((ModuleCat.extendScalars (algebraMap R (Localization.Away r))).map f) := by
  let e : Localization.Away r ⊗[R] N ≃ₗ[Localization.Away r] Localization.Away r :=
    (LocalizedModule.isBaseChange (Submonoid.powers r) N).equiv ≪≫ₗ d
  have he (m : N) : algebraMap R (Localization.Away r) (f m) = e (1 ⊗ₜ[R] m) := by
    simpa [e, IsBaseChange.equiv_tmul] using (hd m).symm
  have h := extendScalars_functional_eq R (.of (Localization.Away r)) N f e he
  have : IsIso ((ModuleCat.extendScalars (algebraMap R (Localization.Away r))).map f ≫
      (ModuleCat.extendScalarsAlgebraIso R (Localization.Away r) (ModuleCat.of R R)).hom ≫
      (TensorProduct.AlgebraTensorModule.rid R (Localization.Away r)
        (Localization.Away r)).toModuleIso.hom) := by
    rw [h]
    infer_instance
  simpa only [isIso_comp_right_iff] using this

/-- Lift a specified scalar-extended isomorphism to a global functional,
which becomes invertible on a principal neighborhood of the quotient. -/
theorem exists_functional_prescribed_scalarIso (R S : CommRingCat.{u}) [Algebra R S]
    (N : ModuleCat.{u} R) [Module.Finite R N] [Module.Projective R N]
    (hRank : ∀ p : PrimeSpectrum R, Module.rankAtStalk N p = 1)
    (h : Function.Surjective (algebraMap R S))
    (E : (ModuleCat.extendScalars (algebraMap R S)).obj N ≅
      (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R R)) :
    ∃ f : N ⟶ ModuleCat.of R R,
      (ModuleCat.extendScalars (algebraMap R S)).map f = E.hom ∧
      ∃ r : R, algebraMap R S r = 1 ∧
        IsIso ((ModuleCat.extendScalars (algebraMap R (Localization.Away r))).map f) := by
  let e : S ⊗[R] N ≃ₗ[S] S :=
    ((ModuleCat.extendScalarsAlgebraIso R S N).symm ≪≫ E ≪≫
      ModuleCat.extendScalarsAlgebraIso R S (ModuleCat.of R R)).toLinearEquiv ≪≫ₗ
        TensorProduct.AlgebraTensorModule.rid R S S
  obtain ⟨f, hf, r, hr, d, hd⟩ :=
    Module.exists_prescribed_principal_coordinate_lift hRank h e
  refine ⟨ModuleCat.ofHom f, ?_, r, hr, ?_⟩
  · apply (cancel_mono ((ModuleCat.extendScalarsAlgebraIso R S (ModuleCat.of R R)).hom ≫
      (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso.hom)).mp
    rw [extendScalars_functional_eq R S N (ModuleCat.ofHom f) e hf]
    change (ModuleCat.extendScalarsAlgebraIso R S N).hom ≫
        (ModuleCat.extendScalarsAlgebraIso R S N).inv ≫ E.hom ≫
        (ModuleCat.extendScalarsAlgebraIso R S (ModuleCat.of R R)).hom ≫
        (TensorProduct.AlgebraTensorModule.rid R S S).toModuleIso.hom = _
    simp
  · exact isIso_extendScalars_of_localized_coordinate R N (ModuleCat.ofHom f) r d hd

/-- Affine comparison before identifying categorical scalar extension with tensors. -/
def pullbackSectionsTildeIso (R S : CommRingCat.{u}) [Algebra R S]
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj M ≅
      tilde ((ModuleCat.extendScalars (algebraMap R S)).obj (moduleSpecΓFunctor.obj M)) :=
  (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))).mapIso
      (asIso M.fromTildeΓ).symm ≪≫
    (tildePullbackIso (CommRingCat.ofHom (algebraMap R S))).app
      (moduleSpecΓFunctor.obj M)

/-- The actual global sheaf functional supplied by a functional on its sections. -/
def globalFunctional (R : CommRingCat.{u}) (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : moduleSpecΓFunctor.obj M ⟶ ModuleCat.of R R) :
    M ⟶ SheafOfModules.unit (Spec R).ringCatSheaf :=
  (asIso M.fromTildeΓ).inv ≫ (tilde.functor R).map f ≫ tildeSelf.hom

/-- Naturality retains the precise geometric restriction of a global functional. -/
theorem pullback_globalFunctional_eq (R S : CommRingCat.{u}) [Algebra R S]
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    (f : moduleSpecΓFunctor.obj M ⟶ ModuleCat.of R R) :
    pullbackUnitMap (Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (globalFunctional R M f) =
      (pullbackSectionsTildeIso R S M).hom ≫
        (tilde.functor S).map ((ModuleCat.extendScalars (algebraMap R S)).map f) ≫
        ((tildePullbackIso (CommRingCat.ofHom (algebraMap R S))).app
          (ModuleCat.of R R)).inv ≫
        (pullbackUnitIso (Spec.map (CommRingCat.ofHom (algebraMap R S)))).hom := by
  let φ : R ⟶ S := CommRingCat.ofHom (algebraMap R S)
  have hn := (tildePullbackIso φ).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  have ht := congrArg (fun k ↦ k ≫
    ((tildePullbackIso φ).app (ModuleCat.of R R)).inv) hn
  simp only [Category.assoc, Iso.app_inv] at ht
  rw [Iso.hom_inv_id_app, Category.comp_id] at ht
  simp only [φ, CommRingCat.hom_ofHom] at ht
  dsimp only [pullbackUnitMap, globalFunctional, pullbackSectionsTildeIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  simp only [Functor.map_comp, tildeSelf, Iso.refl_hom, Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, ht]
  simp only [Category.assoc, Iso.app_hom, Iso.app_inv]

/-- A specified boundary trivialization of an actual affine line bundle lifts
to a global functional which is invertible on a principal neighborhood. Its
geometric boundary restriction is exactly the original isomorphism. -/
theorem exists_globalFunctional_prescribed_boundary (R S : CommRingCat.{u}) [Algebra R S]
    (h : Function.Surjective (algebraMap R S)) (L : LineBundle (Spec R))
    (e : (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj L.val ≅
      SheafOfModules.unit (Spec S).ringCatSheaf) :
    ∃ F : L.val ⟶ SheafOfModules.unit (Spec R).ringCatSheaf,
      pullbackUnitMap (Spec.map (CommRingCat.ofHom (algebraMap R S))) F = e.hom ∧
      ∃ r : R, algebraMap R S r = 1 ∧
        IsIso (pullbackUnitMap
          (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))) F) := by
  have : IsFiniteLocallyFree (Spec R) L.val :=
    finiteLocallyFree_of_isLocallyRankOne L.val L.property
  have : L.val.IsLocallyFree := lineBundle_isLocallyFree (Spec R) L
  let N := moduleSpecΓFunctor.obj L.val
  have : Module.Finite R N := finite_globalSections_of_finiteLocallyFree R L.val
  have : Module.Projective R N := projective_globalSections_of_finiteLocallyFree R L.val
  let φ : R ⟶ S := CommRingCat.ofHom (algebraMap R S)
  let c := pullbackSectionsTildeIso R S L.val
  let b := (tildePullbackIso φ).app (ModuleCat.of R R)
  let E := (tilde.functor S).preimageIso
    (c.symm ≪≫ e ≪≫ (pullbackUnitIso (Spec.map φ)).symm ≪≫ b)
  obtain ⟨f, hf, r, hr, hi⟩ := exists_functional_prescribed_scalarIso R S N
    (rankAtStalk_globalSections_eq_one R L) h E
  refine ⟨globalFunctional R L.val f, ?_, r, hr, ?_⟩
  · rw [pullback_globalFunctional_eq, hf]
    have hE := (tilde.functor S).map_preimage
      (c.inv ≫ e.hom ≫ (pullbackUnitIso (Spec.map φ)).inv ≫ b.hom)
    change (tilde.functor S).map E.hom = _ at hE
    dsimp only [c, b, φ] at hE
    erw [hE]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  · erw [pullback_globalFunctional_eq R (.of (Localization.Away r)) L.val f]
    have := hi
    infer_instance

/-- Equality of base maps retains the canonical pullback comparison. -/
theorem pullbackUnitMap_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {M : Y.Modules} (a : M ⟶ SheafOfModules.unit Y.ringCatSheaf) :
    ((Scheme.Modules.pullbackCongr h).app M).hom ≫ pullbackUnitMap g a =
      pullbackUnitMap f a := by
  subst g
  simp [Scheme.Modules.pullbackCongr]

/-- An invertible restriction of a global functional preserves its prescribed
further restriction, with the original pullback comparisons. -/
theorem exists_unitIso_of_globalFunctional {X Y Z : Scheme.{u}}
    (j : Y ⟶ Z) (q : X ⟶ Y) (k : X ⟶ Z) (hq : q ≫ j = k)
    (M : Z.Modules) (e : (Scheme.Modules.pullback k).obj M ≅
      SheafOfModules.unit X.ringCatSheaf)
    (F : M ⟶ SheafOfModules.unit Z.ringCatSheaf)
    (hF : pullbackUnitMap k F = e.hom) [IsIso (pullbackUnitMap j F)] :
    ∃ d : (Scheme.Modules.pullback j).obj M ≅ SheafOfModules.unit Y.ringCatSheaf,
      ((Scheme.Modules.pullbackCongr hq).app M).symm ≪≫
        ((Scheme.Modules.pullbackComp q j).app M).symm ≪≫
        (Scheme.Modules.pullback q).mapIso d ≪≫ pullbackUnitIso q = e := by
  let d := asIso (pullbackUnitMap j F)
  refine ⟨d, ?_⟩
  apply Iso.ext
  change ((Scheme.Modules.pullbackCongr hq).app M).inv ≫
    ((Scheme.Modules.pullbackComp q j).app M).inv ≫
    pullbackUnitMap q (pullbackUnitMap j F) = e.hom
  rw [← pullbackUnitMap_comp q j F]
  simp only [Iso.inv_hom_id_assoc]
  rw [← pullbackUnitMap_congr hq F]
  simpa only [Iso.inv_hom_id_assoc] using hF

/-- Extend the actual specified boundary isomorphism to a genuine principal
neighborhood. The final equality uses the original geometric pullback,
composition, equality and unit comparisons. No reducedness or connectedness
assumption is imposed on the closed boundary. -/
theorem exists_prescribed_principal_unitIso (R S : CommRingCat.{u}) [Algebra R S]
    (h : Function.Surjective (algebraMap R S)) (L : LineBundle (Spec R))
    (e : (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R S)))).obj L.val ≅
      SheafOfModules.unit (Spec S).ringCatSheaf) :
    ∃ (r : R), algebraMap R S r = 1 ∧
      ∃ (q : Spec S ⟶ Spec (.of (Localization.Away r)))
        (hq : q ≫ Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) =
          Spec.map (CommRingCat.ofHom (algebraMap R S)))
        (d : (Scheme.Modules.pullback
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).obj L.val ≅
          SheafOfModules.unit (Spec (.of (Localization.Away r))).ringCatSheaf),
        ((Scheme.Modules.pullbackCongr hq).app L.val).symm ≪≫
          ((Scheme.Modules.pullbackComp q
            (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))))).app L.val).symm ≪≫
          (Scheme.Modules.pullback q).mapIso d ≪≫ pullbackUnitIso q = e := by
  obtain ⟨F, hF, r, hr, hi⟩ := exists_globalFunctional_prescribed_boundary R S h L e
  let j := Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  let q : Spec S ⟶ Spec (.of (Localization.Away r)) :=
    Spec.map (CommRingCat.ofHom (IsLocalization.Away.lift r (hr ▸ isUnit_one)))
  have hq : q ≫ j = Spec.map (CommRingCat.ofHom (algebraMap R S)) := by
    dsimp only [q, j]
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact IsLocalization.Away.lift_eq r (hr ▸ isUnit_one) x
  have : IsIso (pullbackUnitMap j F) := hi
  obtain ⟨d, hd⟩ := exists_unitIso_of_globalFunctional j q
    (Spec.map (CommRingCat.ofHom (algebraMap R S))) hq L.val e F hF
  exact ⟨r, hr, q, hq, d, hd⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
