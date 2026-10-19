module

public import Motivic.Aglib.CategoryTheory.Sites.Hypercohomology.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! # Free abelian sheaf pushouts from section descent -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t v u

namespace CategoryTheory.Sheaf.Hypercohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]

set_option backward.isDefEq.respectTransparency false in
/-- The actual section-representing equivalence respects restriction in the site. -/
theorem sectionsEquiv_restriction {X Y : C} (f : X ⟶ Y)
    (F : Sheaf J AddCommGrpCat.{max v t}) (g : freeAbelianSheaf J Y ⟶ F) :
    sectionsEquiv J X F ((freeAbelianSheafFunctor J).map f ≫ g) =
      F.obj.map f.op (sectionsEquiv J Y F g) := by
  simp only [sectionsEquiv, Equiv.trans_apply]
  change uliftYonedaEquiv (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _)
    (((sheafificationAdjunction J AddCommGrpCat).homEquiv _ _)
      ((presheafToSheaf J AddCommGrpCat).map _ ≫ g))) = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ f.op).symm

set_option backward.isDefEq.respectTransparency false in
/-- A square which every abelian sheaf takes to a pullback gives an actual
pushout of free abelian sheaves. -/
theorem freeAbelianSheaf_isPushout (sq : Square C)
    (h : ∀ F : Sheaf J AddCommGrpCat.{max v t}, (sq.op.map F.obj).IsPullback) :
    (sq.map (freeAbelianSheafFunctor J)).IsPushout := by
  apply IsPushout.mk' (sq.map (freeAbelianSheafFunctor J)).fac
  · intro F a b h₁ h₂
    apply (sectionsEquiv J sq.X₄ F).injective
    apply Types.ext_of_isPullback ((forget AddCommGrpCat).map_isPullback (h F))
    · exact (sectionsEquiv_restriction J sq.f₂₄ F a).symm.trans
        ((congrArg (sectionsEquiv J sq.X₂ F) h₁).trans
          (sectionsEquiv_restriction J sq.f₂₄ F b))
    · exact (sectionsEquiv_restriction J sq.f₃₄ F a).symm.trans
        ((congrArg (sectionsEquiv J sq.X₃ F) h₂).trans
          (sectionsEquiv_restriction J sq.f₃₄ F b))
  · intro F a b hab
    have he : F.obj.map sq.f₁₂.op (sectionsEquiv J sq.X₂ F a) =
        F.obj.map sq.f₁₃.op (sectionsEquiv J sq.X₃ F b) := by
      rw [← sectionsEquiv_restriction, ← sectionsEquiv_restriction]
      exact congrArg (sectionsEquiv J sq.X₁ F) hab
    obtain ⟨x, h₁, h₂⟩ := Types.exists_of_isPullback
      ((forget AddCommGrpCat).map_isPullback (h F))
      (sectionsEquiv J sq.X₂ F a) (sectionsEquiv J sq.X₃ F b) he
    refine ⟨(sectionsEquiv J sq.X₄ F).symm x, ?_, ?_⟩
    · apply (sectionsEquiv J sq.X₂ F).injective
      exact (sectionsEquiv_restriction J sq.f₂₄ F _).trans
        ((congrArg (fun y ↦ F.obj.map sq.f₂₄.op y)
          ((sectionsEquiv J sq.X₄ F).apply_symm_apply x)).trans h₁)
    · apply (sectionsEquiv J sq.X₃ F).injective
      exact (sectionsEquiv_restriction J sq.f₃₄ F _).trans
        ((congrArg (fun y ↦ F.obj.map sq.f₃₄.op y)
          ((sectionsEquiv J sq.X₄ F).apply_symm_apply x)).trans h₂)

end CategoryTheory.Sheaf.Hypercohomology
