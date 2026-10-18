/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.FiniteFreeWeilRestrictionEtalePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual affine finite-free restriction neighborhoods

The base is the original affine scheme `Spec A`. Evaluation starts at its
actual scalar pullback, and whole test schemes retain their complete rings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Module

universe u

namespace AlgebraicGeometry.AffineWeilRestriction

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra.Etale B C]
variable {κ : Type u} [Fintype κ] (b : Basis κ A B)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual affine restriction scheme over the original affine base. -/
abbrev scheme : Scheme.{u} := Spec (.of (Algebra.WeilRestriction.Ring b C))

/-- The structure map retains the original base, not a restriction of its scalar extension. -/
abbrev projection : scheme (C := C) b ⟶ Spec (.of A) :=
  Spec.algebraMap A (Algebra.WeilRestriction.Ring b C)

instance : Etale (projection (C := C) b) :=
  HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr inferInstance)

/-- Literal evaluation from the genuine scalar pullback of the constructed scheme. -/
def scalarEvaluation :
    pullback (projection (C := C) b) (Spec.algebraMap A B) ⟶ Spec (.of C) :=
  (pullbackSpecIso A (Algebra.WeilRestriction.Ring b C) B).hom ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.WeilRestriction.evaluation b
        (Algebra.Presentation.ofFinitePresentation B C)).toRingHom)

/-- Evaluation is a morphism over the original scalar base. -/
theorem scalarEvaluation_over :
    scalarEvaluation (C := C) b ≫ Spec.algebraMap B C =
      pullback.snd (projection (C := C) b) (Spec.algebraMap A B) := by
  unfold scalarEvaluation
  rw [Category.assoc, ← Spec.map_comp]
  have he : CommRingCat.ofHom (algebraMap B C) ≫
      CommRingCat.ofHom
        (Algebra.WeilRestriction.evaluation b
          (Algebra.Presentation.ofFinitePresentation B C)).toRingHom =
      CommRingCat.ofHom (R := B) (S := Algebra.WeilRestriction.Ring b C ⊗[A] B)
        (Algebra.TensorProduct.includeRight
        (R := A) (A := Algebra.WeilRestriction.Ring b C) (B := B)).toRingHom := by
    ext z
    exact (Algebra.WeilRestriction.evaluation b
      (Algebra.Presentation.ofFinitePresentation B C)).commutes z
  rw [he]
  exact pullbackSpecIso_hom_snd A (Algebra.WeilRestriction.Ring b C) B

variable {T : Type u} [CommRing T] [Algebra A T]

/-- The lift of a whole scalar marking, including its nilpotents. -/
def mark (g : C →ₐ[B] T ⊗[A] B) : Spec (.of T) ⟶ scheme (C := C) b :=
  Spec.map (CommRingCat.ofHom
    ((Algebra.WeilRestriction.homEquiv b
      (Algebra.Presentation.ofFinitePresentation B C)).symm g).toRingHom)

/-- The lifted marking remains over the original affine base. -/
theorem mark_over (g : C →ₐ[B] T ⊗[A] B) :
    mark b g ≫ projection b = Spec.algebraMap A T := by
  unfold mark projection
  rw [← Spec.map_comp]
  congr 1
  ext a
  exact ((Algebra.WeilRestriction.homEquiv b
    (Algebra.Presentation.ofFinitePresentation B C)).symm g).commutes a

/-- The corresponding map between actual scalar pullbacks. -/
def scalarMark (g : C →ₐ[B] T ⊗[A] B) :
    pullback (Spec.algebraMap A T) (Spec.algebraMap A B) ⟶
      pullback (projection (C := C) b) (Spec.algebraMap A B) :=
  (pullbackSpecIso A T B).hom ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map
        ((Algebra.WeilRestriction.homEquiv b
          (Algebra.Presentation.ofFinitePresentation B C)).symm g)
        (AlgHom.id A B)).toRingHom) ≫
    (pullbackSpecIso A (Algebra.WeilRestriction.Ring b C) B).inv

/-- The scalar marking lies over the original lifted marking. -/
theorem scalarMark_fst (g : C →ₐ[B] T ⊗[A] B) :
    scalarMark b g ≫ pullback.fst (projection (C := C) b) (Spec.algebraMap A B) =
      pullback.fst (Spec.algebraMap A T) (Spec.algebraMap A B) ≫ mark b g := by
  unfold scalarMark mark
  rw [Category.assoc, Category.assoc, pullbackSpecIso_inv_fst']
  rw [← pullbackSpecIso_hom_fst' A T B]
  simp only [Category.assoc, ← Spec.map_comp]
  congr 2

/-- The scalar marking retains the scalar-base projection as well. -/
theorem scalarMark_snd (g : C →ₐ[B] T ⊗[A] B) :
    scalarMark b g ≫ pullback.snd (projection (C := C) b) (Spec.algebraMap A B) =
      pullback.snd (Spec.algebraMap A T) (Spec.algebraMap A B) := by
  unfold scalarMark
  rw [Category.assoc, Category.assoc, pullbackSpecIso_inv_snd]
  rw [← pullbackSpecIso_hom_snd A T B]
  rw [← Spec.map_comp]
  congr 2
  ext z
  simp

/-- The scalar lift preserves the entire prescribed marking under literal evaluation. -/
theorem scalarMark_evaluation (g : C →ₐ[B] T ⊗[A] B) :
    scalarMark b g ≫ scalarEvaluation b =
      (pullbackSpecIso A T B).hom ≫ Spec.map (CommRingCat.ofHom g.toRingHom) := by
  unfold scalarMark scalarEvaluation
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Spec.map_comp]
  congr 2
  ext c
  exact (Algebra.WeilRestriction.evaluation_map b
    (Algebra.Presentation.ofFinitePresentation B C)
    ((Algebra.WeilRestriction.homEquiv b
      (Algebra.Presentation.ofFinitePresentation B C)).symm g) c).trans
      (congrArg (fun h => h c) (Equiv.apply_symm_apply _ g))

end AlgebraicGeometry.AffineWeilRestriction
