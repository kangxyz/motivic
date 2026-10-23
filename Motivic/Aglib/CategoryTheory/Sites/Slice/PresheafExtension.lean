/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-! Additive extension from a slice is a sum indexed by structure maps, not a
finite-limit-preserving functor of sites. -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

universe v u w z
namespace CategoryTheory.SlicePresheaf
variable {C : Type u} [Category.{v} C] (X : C)
  {A : Type z} [Category.{w} A] [HasCoproducts.{v} A]

/-- Restriction along the slice arrow `h`, followed by inclusion in the `g`-indexed coproduct
summand. -/
def summand (P : (Over X)ᵒᵖ ⥤ A) {Y Z : C} (h : Z ⟶ Y)
    (f : Y ⟶ X) (g : Z ⟶ X) (e : h ≫ f = g) :
    P.obj (op (Over.mk f)) ⟶ ∐ fun t : Z ⟶ X => P.obj (op (Over.mk t)) :=
  P.map (Over.homMk h e : Over.mk g ⟶ Over.mk f).op ≫
    Sigma.ι (fun t : Z ⟶ X => P.obj (op (Over.mk t))) g

lemma summand_eq (P : (Over X)ᵒᵖ ⥤ A) {Y Z : C} (h : Z ⟶ Y)
    (f : Y ⟶ X) (g : Z ⟶ X) (e : h ≫ f = g) :
    summand X P h f (h ≫ f) rfl = summand X P h f g e := by
  subst g
  rfl

/-- The value of extension at `Y` sums the coefficients over all maps `Y → X`. -/
def extensionObj (P : (Over X)ᵒᵖ ⥤ A) : Cᵒᵖ ⥤ A where
  obj Y := ∐ fun f : Y.unop ⟶ X => P.obj (op (Over.mk f))
  map {Y Z} h := Sigma.desc fun f => summand X P h.unop f (h.unop ≫ f) rfl
  map_id Y := by
    apply Sigma.hom_ext
    intro f
    simp only [Sigma.ι_comp_desc, Category.comp_id, unop_id]
    rw [summand_eq X P _ f f (Category.id_comp f)]
    change P.map (𝟙 _) ≫ _ = _
    simp
  map_comp h k := by
    apply Sigma.hom_ext
    intro f
    simp only [Sigma.ι_comp_desc, Sigma.ι_comp_desc_assoc, unop_comp]
    rw [summand_eq X P _ f _ (Category.assoc k.unop h.unop f)]
    dsimp [summand]
    simp only [Category.assoc, Sigma.ι_comp_desc]
    rw [← P.map_comp_assoc]
    congr 2

/-- Extension acts on each summand by the original morphism. -/
def extension : ((Over X)ᵒᵖ ⥤ A) ⥤ Cᵒᵖ ⥤ A where
  obj := extensionObj X
  map {P Q} η :=
    { app := fun Y => Sigma.desc fun f => η.app (op (Over.mk f)) ≫
        Sigma.ι (fun g : Y.unop ⟶ X => Q.obj (op (Over.mk g))) f
      naturality := by
        intro Y Z h
        apply Sigma.hom_ext
        intro f
        simp only [extensionObj, summand, Category.assoc, Sigma.ι_comp_desc,
          Sigma.ι_comp_desc_assoc]
        rw [← η.naturality_assoc] }
  map_id P := by
    ext Y
    apply Sigma.hom_ext
    intro f
    simp [extensionObj]
  map_comp η θ := by
    ext Y
    apply Sigma.hom_ext
    intro f
    simp

/-- Restriction along the genuine forgetful functor. -/
abbrev restriction : (Cᵒᵖ ⥤ A) ⥤ (Over X)ᵒᵖ ⥤ A :=
  (Functor.whiskeringLeft _ _ A).obj (Over.forget X).op

/-- A map out of a sum gives the component belonging to the structure morphism. -/
def homTo {P : (Over X)ᵒᵖ ⥤ A} {Q : Cᵒᵖ ⥤ A}
    (η : (extension X).obj P ⟶ Q) : P ⟶ (restriction X).obj Q where
  app Y := Sigma.ι (fun g : Y.unop.left ⟶ X => P.obj (op (Over.mk g))) Y.unop.hom ≫
    η.app (op Y.unop.left)
  naturality := by
    intro Y Z h
    rcases Y with ⟨⟨Y, ⟨⟨⟩⟩, f⟩⟩
    rcases Z with ⟨⟨Z, ⟨⟨⟩⟩, g⟩⟩
    let Y' : (Over X)ᵒᵖ := op (Over.mk f)
    let Z' : (Over X)ᵒᵖ := op (Over.mk g)
    have e := congrArg (fun k =>
      Sigma.ι (fun g : Y'.unop.left ⟶ X => P.obj (op (Over.mk g))) Y'.unop.hom ≫ k)
      (η.naturality h.unop.left.op)
    dsimp only [extension, extensionObj] at e
    rw [Sigma.ι_comp_desc_assoc] at e
    simp only [Quiver.Hom.unop_op] at e
    rw [summand_eq X P h.unop.left Y'.unop.hom Z'.unop.hom (Over.w h.unop)] at e
    simpa [summand, restriction, Y', Z', Category.assoc] using e

/-- A restricted map extends by the universal property of the actual sum. -/
def homFrom {P : (Over X)ᵒᵖ ⥤ A} {Q : Cᵒᵖ ⥤ A}
    (η : P ⟶ (restriction X).obj Q) : (extension X).obj P ⟶ Q where
  app Y := Sigma.desc fun f => η.app (op (Over.mk f))
  naturality := by
    intro Y Z h
    apply Sigma.hom_ext
    intro f
    simp [extension, extensionObj, summand, Category.assoc]

/-- The sum construction is the actual left adjoint of slice restriction. -/
def homEquiv (P : (Over X)ᵒᵖ ⥤ A) (Q : Cᵒᵖ ⥤ A) :
    ((extension X).obj P ⟶ Q) ≃ (P ⟶ (restriction X).obj Q) where
  toFun := homTo X
  invFun := homFrom X
  left_inv η := by
    ext Y
    apply Sigma.hom_ext
    intro f
    simp [homTo, homFrom]
  right_inv η := by
    ext Y
    rcases Y with ⟨⟨Y, ⟨⟨⟩⟩, f⟩⟩
    simp [homTo, homFrom]
    rfl

/-- The explicit sum functor is left adjoint to literal slice restriction. -/
def adjunction : extension X (A := A) ⊣ restriction X :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv X
      homEquiv_naturality_left_symm := by
        intro P' P Q f g
        ext Y
        apply Sigma.hom_ext
        intro h
        simp [homEquiv, homFrom, extension]
      homEquiv_naturality_right := by
        intro P Q Q' f g
        ext Y
        simp [homEquiv, homTo, Category.assoc] }

instance : (extension X (A := A)).IsLeftAdjoint := (adjunction X).isLeftAdjoint

/-- The discrete fiber over an object consists of its maps to the slicing object. -/
def fiber (Y : C) : Discrete (Y ⟶ X) ⥤ (Over X)ᵒᵖ :=
  Discrete.functor fun f => op (Over.mk f)

/-- Evaluation of extension is literally a coproduct of evaluations. -/
def evaluationIso (Y : C) :
    extension X (A := A) ⋙ (evaluation Cᵒᵖ A).obj (op Y) ≅
      (Functor.whiskeringLeft _ _ A).obj (fiber X Y) ⋙ colim :=
  NatIso.ofComponents (fun P =>
    HasColimit.isoOfNatIso (Discrete.natIso fun _ => Iso.refl _)) (by
    intro P Q f
    apply Sigma.hom_ext
    intro g
    simp [extension, fiber, Sigma.ι])

instance [HasFiniteLimits A] [AB4OfSize.{v} A] : PreservesFiniteLimits (extension X (A := A)) := by
  apply preservesFiniteLimits_of_evaluation
  intro Y
  exact preservesFiniteLimits_of_natIso (evaluationIso X Y.unop).symm

end CategoryTheory.SlicePresheaf

