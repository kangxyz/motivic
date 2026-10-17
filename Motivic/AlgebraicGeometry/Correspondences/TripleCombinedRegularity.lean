/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleDiagonalRegularity
public import Motivic.RingTheory.RegularSequence.SurjectiveComposition

/-!
# A genuine regular kernel for the combined two-diagonal inclusion

The second diagonal is the flat pullback of the smooth Z diagonal after
imposing the first middle diagonal. Its regular equations therefore live in
the actual first-diagonal quotient stalk. The first closed-stalk surjection
lifts them and appends them to a regular first kernel list. This proves joint
regularity of the combined inclusion in the original six-factor ambient.
Separate regularity of two lists in the ambient is never used as a substitute.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence

universe u

namespace Motivic

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

/-- After the first diagonal, the remaining middle-coordinate projection to Z
is flat when the original X and Y structure maps are flat. -/
instance [Flat f] [Flat g] : Flat (correspondenceTripleTarget f g h) := by
  unfold correspondenceTripleTarget
  infer_instance

/-- The actual second inclusion has regular kernel in the first-diagonal
stalk, by flat Cartesian pullback of the smooth Z diagonal. -/
theorem exists_regular_kernel_correspondenceSecondDiagonal [Flat f] [Flat g]
    [Smooth h] [IsSeparated h] [Flat i] (q : correspondenceFourfoldProduct f g h i) :
    ∃ s : List ((correspondenceFirstDiagonal f g h i).presheaf.stalk
        (correspondenceSecondDiagonalInclusion f g h i q)),
      IsRegular ((correspondenceFirstDiagonal f g h i).presheaf.stalk
        (correspondenceSecondDiagonalInclusion f g h i q)) s ∧
      RingHom.ker ((correspondenceSecondDiagonalInclusion f g h i).stalkMap q).hom =
        Ideal.ofList s := by
  let p : correspondenceFirstDiagonal f g h i ⟶ pullback h h :=
    pullback.map _ _ h h (correspondenceTripleTarget f g h) (pullback.fst h i) (𝟙 S)
      (by simp) (by simp)
  have : Flat p := by
    exact MorphismProperty.pullbackMap (P := @Flat)
      (inferInstanceAs (Flat (correspondenceTripleTarget f g h)))
      (inferInstanceAs (Flat (pullback.fst h i))) rfl rfl
  exact Diagonal.exists_regular_kernel_of_flat_isPullback
    (q := p)
    (pullback_map_diagonal_isPullback (correspondenceTripleTarget f g h) (pullback.fst h i) h)
    q (Diagonal.exists_regular_kernel_of_smooth h _)

set_option backward.isDefEq.respectTransparency false in
/-- The actual combined two-diagonal inclusion admits a regular kernel list
in its original six-factor stalk. Regularity of the second list is proved in
the first quotient before lifting, so this is genuine joint regularity. -/
theorem exists_regular_kernel_correspondenceFourfoldDiagonal [Flat f] [Smooth g]
    [IsSeparated g] [Smooth h] [IsSeparated h] [Flat i]
    (q : correspondenceFourfoldProduct f g h i) :
    ∃ r : List ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i) q)),
      IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
        ((correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i) q)) r ∧
      RingHom.ker ((correspondenceSecondDiagonalInclusion f g h i ≫
        correspondenceFirstDiagonalInclusion f g h i).stalkMap q).hom = Ideal.ofList r := by
  obtain ⟨r, hr, hker⟩ := RegularSequence.exists_regular_kernel_comp_of_surjective
    ((correspondenceFirstDiagonalInclusion f g h i).stalkMap
      (correspondenceSecondDiagonalInclusion f g h i q)).hom
    ((correspondenceSecondDiagonalInclusion f g h i).stalkMap q).hom
    ((correspondenceFirstDiagonalInclusion f g h i).stalkMap_surjective _)
    (exists_regular_kernel_correspondenceFirstDiagonal f g h i
      (correspondenceSecondDiagonalInclusion f g h i q))
    (exists_regular_kernel_correspondenceSecondDiagonal f g h i q)
  refine ⟨r, hr, ?_⟩
  rw [Scheme.Hom.stalkMap_comp]
  exact hker

end Motivic
