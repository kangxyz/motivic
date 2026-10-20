/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# The canonical lift between pullbacks of a composite

The native lift from the pullback of `b ≫ f` to the pullback of `f` is
itself the base change of `b`. No comparison isomorphism or new pullback
object is introduced.

Intended upstream module:
`Aglib.CategoryTheory.Limits.Shapes.Pullback.CompLift`.
Current consumer: `ProjectiveLine.BaseChange.TwoLocalizationBoundaryFactors`.
The complete category, universe, and pullback hypotheses are explicit below.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Limits.pullback

variable {C : Type u} [Category.{v} C] {B X T S : C}

/-- The literal lift between the two displayed pullbacks is a pullback of `b`. -/
theorem isPullback_lift_comp (b : B ⟶ X) (f : X ⟶ S) (m : T ⟶ S)
    [HasPullback (b ≫ f) m] [HasPullback f m] :
    let b₁ : pullback (b ≫ f) m ⟶ pullback f m :=
      pullback.lift (pullback.fst (b ≫ f) m ≫ b) (pullback.snd (b ≫ f) m)
        (by simp [Category.assoc, pullback.condition])
    IsPullback (pullback.fst (b ≫ f) m) b₁ b (pullback.fst f m) := by
  dsimp only
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback f m)
  · simpa only [pullback.lift_snd] using (IsPullback.of_hasPullback (b ≫ f) m)
  · simp only [pullback.lift_fst]

end CategoryTheory.Limits.pullback
