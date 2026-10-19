/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.Field.Point.InverseImage
public import Mathlib.CategoryTheory.Pi.Basic

/-! # The actual family inverse-image and product direct-image adjunction -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
variable {I : Type u} {X : Scheme.{u}} (S : I → Scheme.{u}) (b : ∀ i, S i ⟶ X)

/-- The category of ordinary coefficient sheaves on the specified source schemes. -/
abbrev ImageFamily := ∀ i, Sheaf (nisnevichTopology (S i)) AddCommGrpCat.{u + 1}

/-- The family consists of the genuine inverse images. -/
def familyInverseImage : Sheaf (nisnevichTopology X) AddCommGrpCat.{u + 1} ⥤ ImageFamily S where
  obj F i := (inverseImage (b i)).obj F
  map a i := (inverseImage (b i)).map a
  map_id F := by funext i; exact (inverseImage (b i)).map_id F
  map_comp f g := by funext i; exact (inverseImage (b i)).map_comp f g

/-- The right adjoint uses the actual product in the ordinary sheaf category. -/
def productDirectImage : ImageFamily S ⥤ Sheaf (nisnevichTopology X) AddCommGrpCat.{u + 1} where
  obj A := ∏ᶜ fun i => (directImage (b i)).obj (A i)
  map a := Limits.Pi.map fun i => (directImage (b i)).map (a i)
  map_id A := by
    change Limits.Pi.map (fun i => (directImage (b i)).map (𝟙 (A i))) = _
    have h : (fun i => (directImage (b i)).map (𝟙 (A i))) =
        (fun i => 𝟙 ((directImage (b i)).obj (A i))) :=
      funext fun i => (directImage (b i)).map_id (A i)
    rw [h, Limits.Pi.map_id]
  map_comp a c := by
    simp only [CategoryTheory.Pi.comp_apply, Functor.map_comp, Limits.Pi.map_comp_map]

/-- The adjunction is componentwise the original image adjunction. -/
def familyImageHomEquiv
    (F : Sheaf (nisnevichTopology X) AddCommGrpCat.{u + 1}) (A : ImageFamily S) :
    ((familyInverseImage S b).obj F ⟶ A) ≃ (F ⟶ (productDirectImage S b).obj A) where
  toFun a := Limits.Pi.lift fun i => (imageAdjunction (b i)).homEquiv F (A i) (a i)
  invFun a i := ((imageAdjunction (b i)).homEquiv F (A i)).symm
    (a ≫ Limits.Pi.π (fun j => (directImage (b j)).obj (A j)) i)
  left_inv a := by
    funext i
    simp only [Limits.Pi.lift_comp_π, Equiv.symm_apply_apply]
  right_inv a := by
    apply Limits.Pi.hom_ext
    intro i
    simp only [Limits.Pi.lift_comp_π, Equiv.apply_symm_apply]

/-- No acyclicity or exactness premise is used to construct this actual adjunction. -/
def familyImageAdjunction : familyInverseImage S b ⊣ productDirectImage S b :=
  Adjunction.mkOfHomEquiv
    { homEquiv := familyImageHomEquiv S b
      homEquiv_naturality_left_symm := by
        intro F G A f a
        funext i
        change ((imageAdjunction (b i)).homEquiv F (A i)).symm
          ((f ≫ a) ≫ Limits.Pi.π _ i) = _
        rw [Category.assoc]
        exact (imageAdjunction (b i)).homEquiv_naturality_left_symm f
          (a ≫ Limits.Pi.π _ i)
      homEquiv_naturality_right := by
        intro F A C a c
        apply Limits.Pi.hom_ext
        intro i
        dsimp [familyImageHomEquiv, productDirectImage]
        rw [Limits.Pi.lift_comp_π, Category.assoc, Limits.Pi.map_π,
          Limits.Pi.lift_comp_π_assoc]
        exact (imageAdjunction (b i)).homEquiv_naturality_right (a i) (c i) }

end AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType
