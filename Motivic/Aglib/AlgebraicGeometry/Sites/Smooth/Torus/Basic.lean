/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.Torus
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Products
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# The actual smooth torus, its powers and identity-coordinate inclusions

The multiplicative torus is the Laurent spectrum over the specified ring.
Its zeroth power is the actual base scheme and higher powers are the literal
relative products. The identity-coordinate inclusions insert the actual
evaluation-at-one section, while retaining all other coordinates.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace AlgebraicGeometry.Scheme.SmoothSite

/-- The actual Laurent spectrum as a smooth separated finite-type object. -/
def torus (R : CommRingCat.{u}) : SmoothSite (Spec R) :=
  mk (laurentProjection R)

@[simp] theorem torus_left (R : CommRingCat.{u}) :
    (torus R).left = Spec (.of (LaurentPolynomial R)) := rfl

@[simp] theorem torus_hom (R : CommRingCat.{u}) :
    (torus R).hom = laurentProjection R := rfl

/-- The identity point is literally evaluation of the Laurent coordinate at one. -/
def torusOne (R : CommRingCat.{u}) : base (Spec R) ⟶ torus R :=
  homMk (laurentOneSection R) (laurentOneSection_projection R)

@[simp] theorem torusOne_left (R : CommRingCat.{u}) :
    (torusOne R).left = laurentOneSection R := rfl

/-- Finite torus powers, starting with the actual base scheme. -/
def torusPower (R : CommRingCat.{u}) : ℕ → SmoothSite (Spec R)
  | 0 => base (Spec R)
  | q + 1 => product (torus R) (torusPower R q)

@[simp] theorem torusPower_zero (R : CommRingCat.{u}) :
    torusPower R 0 = base (Spec R) := rfl

@[simp] theorem torusPower_succ (R : CommRingCat.{u}) (q : ℕ) :
    torusPower R (q + 1) = product (torus R) (torusPower R q) := rfl

/-- The structure morphism to the zeroth power. -/
def torusPowerToBase (R : CommRingCat.{u}) (q : ℕ) :
    torusPower R q ⟶ base (Spec R) :=
  homMk (torusPower R q).hom (Category.comp_id _)

@[simp] theorem torusPowerToBase_left (R : CommRingCat.{u}) (q : ℕ) :
    (torusPowerToBase R q).left = (torusPower R q).hom := rfl

@[simp] theorem torusPowerToBase_zero (R : CommRingCat.{u}) :
    torusPowerToBase R 0 = 𝟙 (base (Spec R)) :=
  MorphismProperty.Over.Hom.ext rfl

/-- The coordinate projections of the actual recursive relative product. -/
def torusCoordinate (R : CommRingCat.{u}) :
    (q : ℕ) → Fin q → (torusPower R q ⟶ torus R)
  | 0, i => Fin.elim0 i
  | q + 1, i => Fin.cases (productFst (torus R) (torusPower R q))
      (fun j => productSnd (torus R) (torusPower R q) ≫ torusCoordinate R q j) i

@[simp] theorem torusCoordinate_zero (R : CommRingCat.{u}) (q : ℕ) :
    torusCoordinate R (q + 1) 0 = productFst (torus R) (torusPower R q) := rfl

@[simp] theorem torusCoordinate_succ (R : CommRingCat.{u}) (q : ℕ) (i : Fin q) :
    torusCoordinate R (q + 1) i.succ =
      productSnd (torus R) (torusPower R q) ≫ torusCoordinate R q i := rfl

/-- Lift any tuple of actual maps into the relative torus power. -/
def torusPowerLift (R : CommRingCat.{u}) {X : SmoothSite (Spec R)} :
    (q : ℕ) → (Fin q → (X ⟶ torus R)) → (X ⟶ torusPower R q)
  | 0, _ => homMk X.hom (Category.comp_id _)
  | q + 1, f => productLift (f 0) (torusPowerLift R q (fun i => f i.succ))

@[reassoc (attr := simp)]
theorem torusPowerLift_coordinate (R : CommRingCat.{u}) {X : SmoothSite (Spec R)}
    (q : ℕ) (f : Fin q → (X ⟶ torus R)) (i : Fin q) :
    torusPowerLift R q f ≫ torusCoordinate R q i = f i := by
  induction q with
  | zero => exact Fin.elim0 i
  | succ q ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact productLift_fst _ _
    · simp only [torusCoordinate_succ, torusPowerLift, ← Category.assoc,
        productLift_snd, ih]

/-- Maps into a torus power are determined by their coordinate maps. -/
theorem torusPower_hom_ext (R : CommRingCat.{u}) {X : SmoothSite (Spec R)}
    (q : ℕ) {f g : X ⟶ torusPower R q}
    (h : ∀ i, f ≫ torusCoordinate R q i = g ≫ torusCoordinate R q i) : f = g := by
  induction q with
  | zero =>
    apply MorphismProperty.Over.Hom.ext
    have hf := MorphismProperty.Over.w f
    have hg := MorphismProperty.Over.w g
    change f.left ≫ 𝟙 (Spec R) = X.hom at hf
    change g.left ≫ 𝟙 (Spec R) = X.hom at hg
    exact (Category.comp_id f.left).symm.trans
      ((hf.trans hg.symm).trans (Category.comp_id g.left))
  | succ q ih =>
    apply product_hom_ext
    · exact h 0
    · apply ih
      intro i
      simpa only [torusCoordinate_succ, Category.assoc] using h i.succ

@[simp] theorem torusPowerLift_coordinates (R : CommRingCat.{u}) (q : ℕ) :
    torusPowerLift R q (torusCoordinate R q) = 𝟙 (torusPower R q) := by
  apply torusPower_hom_ext
  intro i
  simp

/-- Insert the literal identity section in the chosen coordinate. -/
def torusInsertOne (R : CommRingCat.{u}) (q : ℕ) (i : Fin (q + 1)) :
    torusPower R q ⟶ torusPower R (q + 1) :=
  torusPowerLift R (q + 1)
    (Fin.insertNth i (torusPowerToBase R q ≫ torusOne R) (torusCoordinate R q))

@[reassoc (attr := simp)]
theorem torusInsertOne_coordinate_self (R : CommRingCat.{u}) (q : ℕ)
    (i : Fin (q + 1)) :
    torusInsertOne R q i ≫ torusCoordinate R (q + 1) i =
      torusPowerToBase R q ≫ torusOne R := by
  simp [torusInsertOne]

@[reassoc (attr := simp)]
theorem torusInsertOne_coordinate_succAbove (R : CommRingCat.{u}) (q : ℕ)
    (i : Fin (q + 1)) (j : Fin q) :
    torusInsertOne R q i ≫ torusCoordinate R (q + 1) (i.succAbove j) =
      torusCoordinate R q j := by
  simp [torusInsertOne]

/-- On the underlying schemes, the inserted coordinate is the actual unit section. -/
@[reassoc]
theorem torusInsertOne_left_coordinate_self (R : CommRingCat.{u}) (q : ℕ)
    (i : Fin (q + 1)) :
    (torusInsertOne R q i).left ≫ (torusCoordinate R (q + 1) i).left =
      (torusPower R q).hom ≫ laurentOneSection R :=
  congrArg (fun f => f.left) (torusInsertOne_coordinate_self R q i)

/-- On the underlying schemes, every other coordinate is retained literally. -/
@[reassoc]
theorem torusInsertOne_left_coordinate_succAbove (R : CommRingCat.{u}) (q : ℕ)
    (i : Fin (q + 1)) (j : Fin q) :
    (torusInsertOne R q i).left ≫
      (torusCoordinate R (q + 1) (i.succAbove j)).left =
        (torusCoordinate R q j).left :=
  congrArg (fun f => f.left) (torusInsertOne_coordinate_succAbove R q i j)

/-- Forget one coordinate of a torus power. -/
def torusDeleteCoordinate (R : CommRingCat.{u}) (q : ℕ) (i : Fin (q + 1)) :
    torusPower R (q + 1) ⟶ torusPower R q :=
  torusPowerLift R q (fun j => torusCoordinate R (q + 1) (i.succAbove j))

@[reassoc (attr := simp)]
theorem torusDeleteCoordinate_coordinate (R : CommRingCat.{u}) (q : ℕ)
    (i : Fin (q + 1)) (j : Fin q) :
    torusDeleteCoordinate R q i ≫ torusCoordinate R q j =
      torusCoordinate R (q + 1) (i.succAbove j) := by
  simp [torusDeleteCoordinate]

@[reassoc (attr := simp)]
theorem torusInsertOne_deleteCoordinate (R : CommRingCat.{u}) (q : ℕ)
    (i : Fin (q + 1)) :
    torusInsertOne R q i ≫ torusDeleteCoordinate R q i = 𝟙 (torusPower R q) := by
  apply torusPower_hom_ext
  intro j
  simp

/-- Each identity-coordinate inclusion is a closed immersion of the actual schemes. -/
instance instIsClosedImmersionTorusInsertOne (R : CommRingCat.{u}) (q : ℕ)
    (i : Fin (q + 1)) : IsClosedImmersion (torusInsertOne R q i).left := by
  have : IsSeparated ((torusDeleteCoordinate R q i).left ≫ (torusPower R q).hom) := by
    rw [MorphismProperty.Over.w]
    infer_instance
  have : IsSeparated (torusDeleteCoordinate R q i).left :=
    IsSeparated.of_comp _ (torusPower R q).hom
  have h : (torusInsertOne R q i).left ≫ (torusDeleteCoordinate R q i).left =
      𝟙 (torusPower R q).left :=
    congrArg (fun f => f.left) (torusInsertOne_deleteCoordinate R q i)
  have : IsClosedImmersion
      ((torusInsertOne R q i).left ≫ (torusDeleteCoordinate R q i).left) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _ (torusDeleteCoordinate R q i).left

/-- The first recursive power is canonically the actual Laurent torus. -/
def torusPowerOneIso (R : CommRingCat.{u}) : torusPower R 1 ≅ torus R where
  hom := torusCoordinate R 1 0
  inv := torusPowerLift R 1 (fun _ => 𝟙 (torus R))
  hom_inv_id := by
    apply torusPower_hom_ext
    intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rw [Category.assoc, torusPowerLift_coordinate, Category.comp_id, Category.id_comp]
  inv_hom_id := torusPowerLift_coordinate R 1 _ 0

@[reassoc (attr := simp)]
theorem torusInsertOne_zero_powerOneIso (R : CommRingCat.{u}) :
    torusInsertOne R 0 0 ≫ (torusPowerOneIso R).hom = torusOne R := by
  change torusInsertOne R 0 0 ≫ torusCoordinate R 1 0 = _
  rw [torusInsertOne_coordinate_self, torusPowerToBase_zero]
  exact Category.id_comp _

end AlgebraicGeometry.Scheme.SmoothSite
