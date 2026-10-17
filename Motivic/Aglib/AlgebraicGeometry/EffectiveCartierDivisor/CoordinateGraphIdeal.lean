/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.DiagonalBoundary
public import Aglib.AlgebraicGeometry.IdealSheaf.Affine
public import Mathlib.RingTheory.Polynomial.Ideal
public import Aglib.Algebra.Polynomial.Laurent.BaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # The specified generator of the affine coordinate graph ideal -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open Polynomial Scheme.Modules

universe u
namespace AlgebraicGeometry.Scheme.Hom

variable (R : Type u) [CommRing R] (a : R)

/-- Multiplication by the original monic coordinate difference into the actual evaluation kernel. -/
def coordinateKernelMap : R[X] →ₗ[R[X]] RingHom.ker (Polynomial.evalRingHom a) where
  toFun f := ⟨f * (X - C a), by simp [RingHom.mem_ker]⟩
  map_add' f g := by ext; simp [add_mul]
  map_smul' f g := by ext; simp [mul_assoc]

/-- The coordinate difference generates the entire graph ideal even over a nonreduced ring. -/
def coordinateKernelEquiv : R[X] ≃ₗ[R[X]] RingHom.ker (Polynomial.evalRingHom a) :=
  LinearEquiv.ofBijective (coordinateKernelMap R a) ⟨by
    intro f g h
    exact (Polynomial.monic_X_sub_C a).isRegular.right (congrArg Subtype.val h), by
    intro f
    have hf : (f : R[X]) ∈ Ideal.span {X - C a} := by
      simpa only [Polynomial.ker_evalRingHom] using f.property
    obtain ⟨g, hg⟩ := Ideal.mem_span_singleton'.mp hf
    exact ⟨g, Subtype.ext hg⟩⟩

@[simp] theorem coordinateKernelEquiv_apply (f : R[X]) :
    (coordinateKernelEquiv R a f : R[X]) = f * (X - C a) := rfl

/-- The actual spectral coordinate-graph ideal, with its specified generator. -/
def coordinateGraphIdealIso :
    SheafOfModules.unit (Spec (.of R[X])).ringCatSheaf ≅
      idealModule (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) :=
  tildeSelf.symm ≪≫ (tilde.functor (.of R[X])).mapIso (coordinateKernelEquiv R a).toModuleIso ≪≫
    affineIdealIso (CommRingCat.ofHom (Polynomial.evalRingHom a))

/-- The trivialization identifies the actual ideal inclusion with multiplication
by the original coordinate difference, not merely an arbitrary generator. -/
@[reassoc] theorem coordinateGraphIdealIso_hom_inclusion :
    (coordinateGraphIdealIso R a).hom ≫
      idealInclusion (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))) =
    tildeSelf.inv ≫
      ((tilde.functor (.of R[X])).mapIso (coordinateKernelEquiv R a).toModuleIso).hom ≫
      tilde.map (ModuleCat.ofHom (RingHom.ker
        (CommRingCat.ofHom (Polynomial.evalRingHom a)).hom).subtype) := by
  have hi := affineIdealIso_hom_inclusion
    (CommRingCat.ofHom (Polynomial.evalRingHom a))
  have hw := congrArg (fun v ↦ tildeSelf.inv ≫
    ((tilde.functor (.of R[X])).mapIso (coordinateKernelEquiv R a).toModuleIso).hom ≫ v) hi
  simpa only [coordinateGraphIdealIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc] using hw

variable {B : Type u} [CommRing B]

/-- The native polynomial spectrum is the actual affine-line product over the base ring. -/
def coordinateProductIso (f : R →+* B) :
    Spec (.of B[X]) ≅ CategoryTheory.Limits.pullback
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
      (Spec.map (CommRingCat.ofHom f)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.PolynomialLaurent.polynomial_isPushout (CommRingCat.ofHom f))).flip.isoPullback

@[reassoc (attr := simp)] theorem coordinateProductIso_hom_fst (f : R →+* B) :
    (coordinateProductIso R f).hom ≫ CategoryTheory.Limits.pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.PolynomialLaurent.polynomial_isPushout
      (CommRingCat.ofHom f))).flip.isoPullback_hom_fst

@[reassoc (attr := simp)] theorem coordinateProductIso_hom_snd (f : R →+* B) :
    (coordinateProductIso R f).hom ≫ CategoryTheory.Limits.pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (Polynomial.C : B →+* B[X])) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.PolynomialLaurent.polynomial_isPushout
      (CommRingCat.ofHom f))).flip.isoPullback_hom_snd

/-- The original graph of an affine-boundary coordinate. -/
def affineCoordinateGraph (z : R[X] →+* B) :
    Spec (.of B) ⟶ CategoryTheory.Limits.pullback
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
      (Spec.map (CommRingCat.ofHom (z.comp Polynomial.C))) :=
  CategoryTheory.Limits.pullback.lift (Spec.map (CommRingCat.ofHom z)) (𝟙 _) (by
    simp only [Category.id_comp, ← Spec.map_comp]
    rfl)

/-- The polynomial evaluation zero scheme is the original affine coordinate graph. -/
@[reassoc] theorem evaluation_coordinateProductIso (z : R[X] →+* B) :
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (z X))) ≫
      (coordinateProductIso R (z.comp Polynomial.C)).hom = affineCoordinateGraph R z := by
  apply CategoryTheory.Limits.pullback.hom_ext
  · simp only [Category.assoc, coordinateProductIso_hom_fst, affineCoordinateGraph,
      CategoryTheory.Limits.pullback.lift_fst, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      simp
    · simp
  · simp only [Category.assoc, coordinateProductIso_hom_snd, affineCoordinateGraph,
      CategoryTheory.Limits.pullback.lift_snd, ← Spec.map_comp]
    rw [← Spec.map_id]
    congr 1
    ext r
    simp

/-- The actual affine coordinate graph ideal is globally trivial, with the
trivialization transported from the monic original coordinate difference. -/
def affineCoordinateGraphIdealIso (z : R[X] →+* B) :
    SheafOfModules.unit (CategoryTheory.Limits.pullback
      (Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* R[X])))
      (Spec.map (CommRingCat.ofHom (z.comp Polynomial.C)))).ringCatSheaf ≅
      idealModule (affineCoordinateGraph R z) := by
  let e := coordinateProductIso R (z.comp Polynomial.C)
  have h : 𝟙 (Spec (.of B)) ≫
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (z X))) =
        affineCoordinateGraph R z ≫ e.inv := by
    rw [← evaluation_coordinateProductIso R z]
    simp [e]
  let v := idealPullbackMap
    (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (z X))))
    (affineCoordinateGraph R z) e.inv (𝟙 _) h
  have : IsIso v := idealPullbackMap_isIso_of_iso_square _ _ _ _ _
  exact (pullbackUnitIso e.inv).symm ≪≫
    (Scheme.Modules.pullback e.inv).mapIso (coordinateGraphIdealIso B (z X)) ≪≫ asIso v

end AlgebraicGeometry.Scheme.Hom
