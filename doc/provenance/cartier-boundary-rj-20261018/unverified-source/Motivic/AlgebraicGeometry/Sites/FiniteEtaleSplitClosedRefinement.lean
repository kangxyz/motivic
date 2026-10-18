/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleSplitClosedNeighborhood

/-! # Literal base refinements of a split closed pair

A marked etale refinement of the closed scheme extends by the specified
retraction. The ambient refinement is the actual scheme pullback, and its
closed section, retraction and complete closed fiber are retained. No
refinement of an auxiliary homotopy parameter occurs here.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace Motivic.FiniteEtaleSite

variable {Z Y : Scheme.{u}} (i : Z ⟶ Y) (p : Y ⟶ Z) (hip : i ≫ p = 𝟙 Z)
  (V : FiniteEtaleSite Z)

/-- The original closed section after the literal base refinement along the
retraction. Its ambient scheme is exactly `pullback V.hom p`. -/
def splitClosedRefinementSection : V.left ⟶ ((baseChange p).obj V).left :=
  pullback.lift (𝟙 V.left) (V.hom ≫ i) (by
    rw [Category.assoc, hip, Category.comp_id, Category.id_comp])

/-- The refined closed section has the literal first projection as retraction. -/
@[reassoc (attr := simp)]
theorem splitClosedRefinementSection_fst :
    splitClosedRefinementSection i p hip V ≫ pullback.fst V.hom p = 𝟙 V.left :=
  pullback.lift_fst _ _ _

/-- The refined closed section maps to the original section over the original
closed refinement map, not just to the same closed support. -/
@[reassoc (attr := simp)]
theorem splitClosedRefinementSection_snd :
    splitClosedRefinementSection i p hip V ≫ pullback.snd V.hom p = V.hom ≫ i :=
  pullback.lift_snd _ _ _

/-- The entire closed fiber of the refined ambient neighborhood is the given
closed neighborhood. -/
theorem splitClosedRefinementSection_isPullback :
    IsPullback (splitClosedRefinementSection i p hip V) V.hom
      (pullback.snd V.hom p) i := by
  have hleft (c : PullbackCone (pullback.snd V.hom p) i) :
      (c.fst ≫ pullback.fst V.hom p) ≫ V.hom = c.snd := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, c.condition,
      Category.assoc, hip, Category.comp_id]
  apply IsPullback.of_isLimit' ⟨splitClosedRefinementSection_snd i p hip V⟩
  refine PullbackCone.IsLimit.mk _ (fun c => c.fst ≫ pullback.fst V.hom p) ?_ ?_ ?_
  · intro c
    apply pullback.hom_ext
    · simp only [Category.assoc, splitClosedRefinementSection_fst, Category.comp_id]
    · rw [Category.assoc, splitClosedRefinementSection_snd,
        ← Category.assoc, hleft c]
      exact c.condition.symm
  · intro c
    exact hleft c
  · intro c m hm _
    exact (Category.comp_id m).symm.trans
      ((congrArg (fun t => m ≫ t) (splitClosedRefinementSection_fst i p hip V).symm).trans
        ((Category.assoc _ _ _).symm.trans
          (congrArg (fun t => t ≫ pullback.fst V.hom p) hm)))

/-- Base refinement retains the actual closed immersion. -/
instance splitClosedRefinementSection_isClosedImmersion [IsClosedImmersion i] :
    IsClosedImmersion (splitClosedRefinementSection i p hip V) :=
  MorphismProperty.of_isPullback
    (splitClosedRefinementSection_isPullback i p hip V).flip inferInstance

variable (K : Type u) [Field K] (c : Spec (.of K) ⟶ Z)
  (N : FieldValuedNeighborhood c K (𝟙 _))

/-- The marked closed refinement extends to the actual ambient pullback with
the same field-valued map. -/
def splitClosedFieldRefinement : FieldValuedNeighborhood (c ≫ i) K (𝟙 _) :=
  Functor.elementsMk _ ((baseChange p).obj N.obj)
    (Over.homMk (N.val.left ≫ splitClosedRefinementSection i p hip N.obj) (by
      have hn : N.val.left ≫ N.obj.hom = c :=
        (Over.w N.val).trans (Category.id_comp c)
      change (N.val.left ≫ splitClosedRefinementSection i p hip N.obj) ≫
        pullback.snd N.obj.hom p = 𝟙 _ ≫ (c ≫ i)
      rw [Category.assoc, splitClosedRefinementSection_snd, ← Category.assoc,
        hn, Category.id_comp]))

/-- The ambient mark lies on the actual refined closed section. -/
theorem splitClosedFieldRefinement_mark :
    (splitClosedFieldRefinement i p hip K c N).val.left =
      N.val.left ≫ splitClosedRefinementSection i p hip N.obj := rfl

/-- Retraction returns the complete original closed mark. -/
@[reassoc]
theorem splitClosedFieldRefinement_mark_fst :
    (splitClosedFieldRefinement i p hip K c N).val.left ≫
      pullback.fst N.obj.hom p = N.val.left := by
  rw [splitClosedFieldRefinement_mark, Category.assoc,
    splitClosedRefinementSection_fst, Category.comp_id]

end Motivic.FiniteEtaleSite
