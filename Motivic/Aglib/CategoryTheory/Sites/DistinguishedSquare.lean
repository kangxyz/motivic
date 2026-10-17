/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Square

/-!
# Sheaf descent for distinguished squares

A pullback square with a monomorphic left covering arrow satisfies two-arrow
sheaf descent if the self-overlap of the other arrow is covered by its diagonal
and the self-overlap over the first object. Only the first covering arrow is
required to be a monomorphism. The coefficient category and its hom universe are
arbitrary; in particular the result applies to universe-lifted abelian sheaves.
-/

@[expose] public noncomputable section

universe u v u' v'

namespace CategoryTheory

open Limits Opposite

namespace Square

variable {C : Type u} [Category.{v} C] (sq : Square C)

/-- The map between the two self-overlaps in a commutative square. -/
def overlapMap [HasPullback sq.f₁₂ sq.f₁₂] [HasPullback sq.f₃₄ sq.f₃₄] :
    pullback sq.f₁₂ sq.f₁₂ ⟶ pullback sq.f₃₄ sq.f₃₄ :=
  pullback.map _ _ _ _ sq.f₁₃ sq.f₁₃ sq.f₂₄ sq.fac sq.fac

@[reassoc (attr := simp)]
lemma overlapMap_fst [HasPullback sq.f₁₂ sq.f₁₂] [HasPullback sq.f₃₄ sq.f₃₄] :
    sq.overlapMap ≫ pullback.fst _ _ = pullback.fst _ _ ≫ sq.f₁₃ := by
  exact pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma overlapMap_snd [HasPullback sq.f₁₂ sq.f₁₂] [HasPullback sq.f₃₄ sq.f₃₄] :
    sq.overlapMap ≫ pullback.snd _ _ = pullback.snd _ _ ≫ sq.f₁₃ := by
  exact pullback.lift_snd _ _ _

variable {J : GrothendieckTopology C} {A : Type u'} [Category.{v'} A]

set_option backward.isDefEq.respectTransparency false in
/-- A genuine two-arrow gluing theorem for a distinguished square. The cover of
its right self-overlap supplies precisely the matching condition not implied by
monicity of the first covering arrow. No monicity of the second is assumed. -/
theorem isPullback_op_map_of_diagonal_cover
    [Mono sq.f₂₄] [HasPullback sq.f₁₂ sq.f₁₂] [HasPullback sq.f₃₄ sq.f₃₄]
    (hpb : sq.IsPullback)
    (hcover : Sieve.ofTwoArrows sq.f₂₄ sq.f₃₄ ∈ J sq.X₄)
    (hdiag : Sieve.ofTwoArrows (pullback.diagonal sq.f₃₄) sq.overlapMap ∈
      J (pullback sq.f₃₄ sq.f₃₄))
    (F : Sheaf J A) : (sq.op.map F.obj).IsPullback := by
  apply Square.IsPullback.mk
  refine PullbackCone.IsLimit.mk _
    (fun s ↦ F.property.amalgamateOfArrows _ hcover
      (fun j ↦ WalkingPair.casesOn j s.fst s.snd)
      (fun W ↦ by
        rintro (_ | _) (_ | _) a b fac
        · obtain rfl : a = b := by simpa only [← cancel_mono sq.f₂₄] using fac
          rfl
        · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hpb.isLimit _ _ fac
          simpa using s.condition =≫ F.obj.map φ.op
        · obtain ⟨φ, rfl, rfl⟩ := PullbackCone.IsLimit.lift' hpb.isLimit _ _ fac.symm
          simpa using s.condition.symm =≫ F.obj.map φ.op
        · have hself :
              s.snd ≫ F.obj.map (pullback.fst sq.f₃₄ sq.f₃₄).op =
                s.snd ≫ F.obj.map (pullback.snd sq.f₃₄ sq.f₃₄).op := by
            apply F.property.hom_ext_ofArrows _ hdiag
            rintro (_ | _)
            · simp [← Functor.map_comp, ← op_comp]
            · simp only [Category.assoc, ← Functor.map_comp, ← op_comp,
                overlapMap_fst, overlapMap_snd]
              have hs : s.fst ≫ F.obj.map sq.f₁₂.op =
                  s.snd ≫ F.obj.map sq.f₁₃.op := s.condition
              rw [op_comp, op_comp, F.obj.map_comp, F.obj.map_comp,
                ← Category.assoc, ← Category.assoc, ← hs]
              simp only [Category.assoc, ← Functor.map_comp, ← op_comp,
                pullback.condition]
          simpa only [Category.assoc, ← Functor.map_comp, ← op_comp,
            pullback.lift_fst, pullback.lift_snd] using
            hself =≫ F.obj.map (pullback.lift a b fac).op))
    (fun _ ↦ ?_) (fun _ ↦ ?_) (fun s m hm₁ hm₂ ↦ ?_)
  · exact F.property.amalgamateOfArrows_map _ _ _ _ WalkingPair.left
  · exact F.property.amalgamateOfArrows_map _ _ _ _ WalkingPair.right
  · apply F.property.hom_ext_ofArrows _ hcover
    rintro (_ | _)
    · rw [F.property.amalgamateOfArrows_map _ _ _ _ WalkingPair.left]
      exact hm₁
    · rw [F.property.amalgamateOfArrows_map _ _ _ _ WalkingPair.right]
      exact hm₂

end Square

end CategoryTheory
