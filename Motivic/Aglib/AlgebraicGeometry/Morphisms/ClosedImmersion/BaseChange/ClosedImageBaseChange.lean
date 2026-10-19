/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Base-changing a closed support inside a relative product

The literal base change of a support over its source maps into the base-changed
ambient product by a Cartesian square. Closed immersions are consequently
preserved, with no flatness or reducedness assumption on the base change.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ClosedImageBaseChange

variable {S X Y U C : Scheme.{u}} (x : X ⟶ S) (y : Y ⟶ S) (u : U ⟶ S)
  (g : U ⟶ X) (hg : g ≫ x = u) (j : C ⟶ pullback x y)

/-- The actual map between the two ambient products. -/
def ambientMap : pullback u y ⟶ pullback x y :=
  pullback.map u y x y g (𝟙 Y) (𝟙 S) (by simpa using hg.symm) (by simp)

@[reassoc (attr := simp)]
theorem ambientMap_fst : ambientMap x y u g hg ≫ pullback.fst x y =
    pullback.fst u y ≫ g := by simp only [ambientMap, pullback.map, pullback.lift_fst]

@[reassoc (attr := simp)]
theorem ambientMap_snd : ambientMap x y u g hg ≫ pullback.snd x y =
    pullback.snd u y := by simp only [ambientMap, pullback.map, pullback.lift_snd, Category.comp_id]

/-- The actual inclusion of the whole source-base-changed support. -/
def inclusion : pullback (j ≫ pullback.fst x y) g ⟶ pullback u y :=
  pullback.lift (pullback.snd (j ≫ pullback.fst x y) g)
    (pullback.fst (j ≫ pullback.fst x y) g ≫ j ≫ pullback.snd x y) (by
      calc
        _ = pullback.snd (j ≫ pullback.fst x y) g ≫ g ≫ x := by rw [hg]
        _ = pullback.fst (j ≫ pullback.fst x y) g ≫ j ≫
            pullback.fst x y ≫ x := by
          simpa only [Category.assoc] using
            (pullback.condition_assoc (f := j ≫ pullback.fst x y) (g := g) x).symm
        _ = _ := by simp only [pullback.condition, Category.assoc])

@[reassoc (attr := simp)]
theorem inclusion_fst : inclusion x y u g hg j ≫ pullback.fst u y =
    pullback.snd (j ≫ pullback.fst x y) g := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem inclusion_snd : inclusion x y u g hg j ≫ pullback.snd u y =
    pullback.fst (j ≫ pullback.fst x y) g ≫ j ≫ pullback.snd x y :=
  pullback.lift_snd _ _ _

/-- The literal support inclusion is the actual base change of the old inclusion. -/
theorem inclusion_isPullback :
    IsPullback (pullback.fst (j ≫ pullback.fst x y) g)
      (inclusion x y u g hg j) j (ambientMap x y u g hg) := by
  have hw : pullback.fst (j ≫ pullback.fst x y) g ≫ j =
      inclusion x y u g hg j ≫ ambientMap x y u g hg := by
    apply pullback.hom_ext
    · simp only [Category.assoc, ambientMap_fst, inclusion_fst_assoc]
      exact pullback.condition
    · simp
  refine IsPullback.of_isLimit' ⟨hw⟩ (PullbackCone.IsLimit.mk _ (fun c ↦
    pullback.lift c.fst (c.snd ≫ pullback.fst u y) (by
      have h := congrArg (fun f ↦ f ≫ pullback.fst x y) c.condition
      simpa only [Category.assoc, ambientMap_fst] using h)) ?_ ?_ ?_)
  · intro c
    exact pullback.lift_fst _ _ _
  · intro c
    apply pullback.hom_ext
    · simp only [Category.assoc, inclusion_fst, pullback.lift_snd]
    · have h := congrArg (fun f ↦ f ≫ pullback.snd x y) c.condition
      simpa only [Category.assoc, inclusion_snd, pullback.lift_fst_assoc,
        ambientMap_snd] using h
  · intro c m h₁ h₂
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using h₁
    · have h := congrArg (fun f ↦ f ≫ pullback.fst u y) h₂
      simpa only [Category.assoc, inclusion_fst, pullback.lift_snd] using h

/-- Closed supports remain closed in the actual new ambient product. -/
instance inclusion_isClosedImmersion [IsClosedImmersion j] :
    IsClosedImmersion (inclusion x y u g hg j) :=
  MorphismProperty.of_isPullback (inclusion_isPullback x y u g hg j) inferInstance

end AlgebraicGeometry.ClosedImageBaseChange
