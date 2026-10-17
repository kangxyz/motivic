/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.Basic

/-!
# A literal correspondence homotopy splitting a section difference map

Suppose an actual signed correspondence from `B × A¹` to `B` has endpoints
the identity and `Γ(B → Y) ≫ lam - Γ(B → A) ≫ ψ`. Homotopy-invariant transfer
coefficients then give a right inverse to the restriction difference map
`F(A) × F(Y) → F(B)`: it sends `d` to `(-F(ψ)d, -F(lam)d)`.

The actual correspondence and its two endpoint identities are inputs. This
lemma neither constructs the geometric moving family nor assumes a
cohomological vanishing statement.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe v u

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The signed transfer pair is a right inverse to the literal `A` minus `Y`
restriction map, using the endpoints of the displayed cylinder correspondence. -/
theorem restriction_difference_rightInverse_of_homotopy
    (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P)
    {B A Y : SmoothSite (Spec (.of k))} (p : B ⟶ A) (i : B ⟶ Y)
    (lam : Cor.mk Y ⟶ Cor.mk B) (ψ : Cor.mk A ⟶ Cor.mk B)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of k) B) ⟶ Cor.mk B)
    (h₀ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B 0) ≫ α = 𝟙 _)
    (h₁ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B 1) ≫ α =
      (Cor.graphFunctor k).map i ≫ lam - (Cor.graphFunctor k).map p ≫ ψ)
    (d : sections P (Cor.mk B)) :
    ((toPresheaf k).obj P).map p.op (-transfer P ψ d) -
      ((toPresheaf k).obj P).map i.op (-transfer P lam d) = d := by
  have hmap := transfer_homotopy_endpoints P hP B (Cor.mk B) α 0 1
  erw [h₀, h₁, transfer_id, transfer_sub, transfer_comp, transfer_comp] at hmap
  have h := ConcreteCategory.congr_hom hmap d
  change d = transfer P ((Cor.graphFunctor k).map i) (transfer P lam d) -
    transfer P ((Cor.graphFunctor k).map p) (transfer P ψ d) at h
  erw [map_neg, map_neg, neg_sub_neg]
  exact h.symm

/-- A genuine endpoint splitting implies surjectivity of the ordinary
restriction difference for HI presheaves with transfers. -/
theorem restriction_difference_surjective_of_homotopy
    (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P)
    {B A Y : SmoothSite (Spec (.of k))} (p : B ⟶ A) (i : B ⟶ Y)
    (lam : Cor.mk Y ⟶ Cor.mk B) (ψ : Cor.mk A ⟶ Cor.mk B)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of k) B) ⟶ Cor.mk B)
    (h₀ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B 0) ≫ α = 𝟙 _)
    (h₁ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B 1) ≫ α =
      (Cor.graphFunctor k).map i ≫ lam - (Cor.graphFunctor k).map p ≫ ψ) :
    Function.Surjective (fun a : sections P (Cor.mk A) × sections P (Cor.mk Y) =>
      ((toPresheaf k).obj P).map p.op a.1 - ((toPresheaf k).obj P).map i.op a.2) := by
  intro d
  exact ⟨⟨-transfer P ψ d, -transfer P lam d⟩,
    restriction_difference_rightInverse_of_homotopy P hP p i lam ψ α h₀ h₁ d⟩

/-- A graph endpoint over a smaller source lifts the restriction of each
original section through the signed difference. This does not assert
surjectivity onto all sections of the smaller source. -/
theorem restriction_difference_eq_restriction_of_homotopy
    (P : PresheafWithTransfers.{v} k) (hP : IsA1Invariant P)
    {B B' A' Y' : SmoothSite (Spec (.of k))}
    (jB : B' ⟶ B) (p : B' ⟶ A') (i : B' ⟶ Y')
    (lam : Cor.mk Y' ⟶ Cor.mk B) (ψ : Cor.mk A' ⟶ Cor.mk B)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of k) B') ⟶ Cor.mk B)
    (h₀ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B' 0) ≫ α =
      (Cor.graphFunctor k).map jB)
    (h₁ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B' 1) ≫ α =
      (Cor.graphFunctor k).map i ≫ lam - (Cor.graphFunctor k).map p ≫ ψ)
    (d : sections P (Cor.mk B)) :
    ((toPresheaf k).obj P).map p.op (-transfer P ψ d) -
      ((toPresheaf k).obj P).map i.op (-transfer P lam d) =
        ((toPresheaf k).obj P).map jB.op d := by
  have hmap := transfer_homotopy_endpoints P hP B' (Cor.mk B) α 0 1
  erw [h₀, h₁, transfer_sub, transfer_comp, transfer_comp] at hmap
  have h := ConcreteCategory.congr_hom hmap d
  change transfer P ((Cor.graphFunctor k).map jB) d =
    transfer P ((Cor.graphFunctor k).map i) (transfer P lam d) -
      transfer P ((Cor.graphFunctor k).map p) (transfer P ψ d) at h
  erw [map_neg, map_neg, neg_sub_neg]
  exact h.symm

end Motivic.PresheafWithTransfers

namespace Motivic.SheafWithTransfers

variable {k : Type u} [Field k]

/-- The same splitting uses the original ordinary sheaf restrictions and
retains the original transfer coefficient universe. -/
theorem restriction_difference_surjective_of_homotopy
    (F : SheafWithTransfers.{u + 1} k) (hF : PresheafWithTransfers.IsA1Invariant F.obj)
    {B A Y : SmoothSite (Spec (.of k))} (p : B ⟶ A) (i : B ⟶ Y)
    (lam : Cor.mk Y ⟶ Cor.mk B) (ψ : Cor.mk A ⟶ Cor.mk B)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of k) B) ⟶ Cor.mk B)
    (h₀ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B 0) ≫ α = 𝟙 _)
    (h₁ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B 1) ≫ α =
      (Cor.graphFunctor k).map i ≫ lam - (Cor.graphFunctor k).map p ≫ ψ) :
    Function.Surjective (fun a :
        ((toSheaf k).obj F).obj.obj (op A) × ((toSheaf k).obj F).obj.obj (op Y) =>
      ((toSheaf k).obj F).obj.map p.op a.1 - ((toSheaf k).obj F).obj.map i.op a.2) :=
  F.obj.restriction_difference_surjective_of_homotopy hF p i lam ψ α h₀ h₁

/-- The graph-endpoint lifting retains the original ordinary sheaf maps;
only sections restricted from `B` are asserted to lie in the difference image. -/
theorem restriction_difference_eq_restriction_of_homotopy
    (F : SheafWithTransfers.{u + 1} k) (hF : PresheafWithTransfers.IsA1Invariant F.obj)
    {B B' A' Y' : SmoothSite (Spec (.of k))}
    (jB : B' ⟶ B) (p : B' ⟶ A') (i : B' ⟶ Y')
    (lam : Cor.mk Y' ⟶ Cor.mk B) (ψ : Cor.mk A' ⟶ Cor.mk B)
    (α : Cor.mk (SmoothSite.a1Cylinder (.of k) B') ⟶ Cor.mk B)
    (h₀ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B' 0) ≫ α =
      (Cor.graphFunctor k).map jB)
    (h₁ : (Cor.graphFunctor k).map (SmoothSite.a1Section (.of k) B' 1) ≫ α =
      (Cor.graphFunctor k).map i ≫ lam - (Cor.graphFunctor k).map p ≫ ψ)
    (d : ((toSheaf k).obj F).obj.obj (op B)) :
    ((toSheaf k).obj F).obj.map p.op (-F.obj.transfer ψ d) -
      ((toSheaf k).obj F).obj.map i.op (-F.obj.transfer lam d) =
        ((toSheaf k).obj F).obj.map jB.op d :=
  F.obj.restriction_difference_eq_restriction_of_homotopy hF jB p i lam ψ α h₀ h₁ d

end Motivic.SheafWithTransfers
