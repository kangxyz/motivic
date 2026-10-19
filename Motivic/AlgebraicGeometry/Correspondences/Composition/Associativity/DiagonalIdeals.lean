/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Products.Diagonal.TripleIdeals

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.DiagonalAmbient
public import Motivic.Aglib.AlgebraicGeometry.Diagonal.FlatBaseChange

/-!
# The two actual middle-diagonal ideals in one six-factor ambient

Both middle self-product maps are constructed on the original six-factor
scheme. Their genuine diagonal pullbacks have the fourfold product as their
Cartesian intersection. Consequently the combined diagonal kernel and the
full triple-incidence kernel are literal sums of the two middle-diagonal
ideals, retaining all nilpotents.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

variable {S X Y Z W : Scheme.{u}}
  (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)

namespace FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme.Products

variable {f g h i}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- Actual triple incidence is cut out by the two literal middle-diagonal
ideals plus the original exterior coefficient ideal in one ambient scheme. -/
theorem ker_tripleIncidenceSixfold_eq_threeIdeals [IsSeparated g] [IsSeparated h] :
    (F.tripleIncidenceSixfoldInclusion G H).ker =
      (correspondenceFirstDiagonalInclusion f g h i).ker ⊔
        ((correspondenceSecondAmbientInclusion f g h i).ker ⊔
          (F.tripleSupportProductInclusion G H).ker) := by
  rw [F.ker_tripleIncidenceSixfoldInclusion G H, ker_correspondenceFourfoldDiagonal, sup_assoc]

/-- All three actual support ideals are viewed in the same literal six-factor
stalk, and their sum is the full triple-incidence stalk-map kernel. -/
theorem stalkKernel_tripleIncidenceSixfold_eq_threeIdeals [IsSeparated g] [IsSeparated h]
    (w : F.tripleIncidence G H) :
    let p := F.tripleIncidenceSixfoldInclusion G H w
    RingHom.ker ((F.tripleIncidenceSixfoldInclusion G H).stalkMap w).hom =
      (correspondenceFirstDiagonalInclusion f g h i).ker.stalk p ⊔
        ((correspondenceSecondAmbientInclusion f g h i).ker.stalk p ⊔
          (F.tripleSupportProductInclusion G H).ker.stalk p) := by
  rw [← (F.tripleIncidenceSixfoldInclusion G H).ker_stalk w,
    F.ker_tripleIncidenceSixfold_eq_threeIdeals G H, Scheme.IdealSheafData.stalk_sup,
    Scheme.IdealSheafData.stalk_sup]

end FiniteCorrespondenceGenerator

end Motivic
