/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleDiagonalAmbient
public import Motivic.AlgebraicGeometry.Correspondences.TripleGenericDominance
public import Motivic.AlgebraicGeometry.Intersection.GenericTor

/-!
# Actual successive-intersection stalk consumers

The genuine first-stage kernel equals its diagonal ideal plus the literal
coefficient annihilator. At a genuine generic point of full triple incidence,
the actual final ambient kernel quotient and the actual diagonal/support sum
quotient are Artinian, with no assumption that the ambient stalk is Artinian.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.TripleDiagonalAmbient

open Intersection

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g)
  (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The actual first-stage stalk ideal is the first diagonal plus the
annihilator of the genuine exterior coefficient stalk. -/
theorem actualFirstStageKernel [IsSeparated g] (w : F.leftIntermediateSupportProduct G H) :
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let d := correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let hp := point_eq a b d j (F.leftIntermediate_ambient_isPullback G H) w
    RingHom.ker ((a ≫ d).stalkMap w).hom =
      RingHom.ker (d.stalkMap (a w)).hom ⊔
        Module.annihilator (ambientStalk d (a w))
          (coefficientStalkModule d (a w) j (b w) hp) := by
  dsimp only
  rw [coefficientStalkModule_annihilator]
  exact stalkMap_kernel_eq_sup _ _ _ _ (F.leftIntermediate_ambient_isPullback G H) w

/-- Every actual first-stage Koszul homology module is annihilated by the
literal first-stage stalk ideal; the ambient chain terms need not descend. -/
theorem actualFirstStageHomologySupport [IsSeparated g]
    (w : F.leftIntermediateSupportProduct G H) :
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let d := correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let hp := point_eq a b d j (F.leftIntermediate_ambient_isPullback G H) w
    let M := coefficientStalkModule d (a w) j (b w) hp
    ∀ (t : List (ambientStalk d (a w))), RingHom.ker (d.stalkMap (a w)).hom = Ideal.ofList t →
      ∀ n : ℕ, RingHom.ker ((a ≫ d).stalkMap w).hom ≤
        Module.annihilator (ambientStalk d (a w)) ((Koszul.coefficientComplex M t).homology n) := by
  dsimp only
  intro t ht n
  rw [actualFirstStageKernel F G H w, ht]
  exact Koszul.support_le_annihilator_coefficient_homology _ t n

section Smooth

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The full actual triple-incidence ambient kernel cuts out an Artinian ring
at each genuine generic point, retaining all source nilpotents. -/
theorem actualFinalKernelQuotient (w : genericPoints (F.tripleIncidence G H)) :
    IsArtinianRing
      ((correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom).presheaf.stalk
          (F.tripleIncidenceSixfoldInclusion G H w.1) ⧸
        RingHom.ker ((F.tripleIncidenceSixfoldInclusion G H).stalkMap w.1).hom) := by
  have : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsLocallyNoetherian X.left)
  have := LocallyOfFiniteType.isLocallyNoetherian (F.tripleIncidenceSource G H)
  exact stalk_quotient_ker_isArtinian _ w.1 w.2

/-- The literal combined-diagonal ideal plus the exterior coefficient
annihilator gives the same actual Artinian generic triple stalk. -/
theorem actualFinalSumQuotient (w : genericPoints (F.tripleIncidence G H)) :
    let a := F.tripleIncidenceFourfoldInclusion G H
    let b := F.tripleIncidenceToLeftSupportProduct G H ≫ F.leftIntermediateToTripleSupport G H
    let d := correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
      correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom
    let j := F.tripleSupportProductInclusion G H
    let hp := point_eq a b d j (F.tripleIncidence_sixfold_isPullback G H) w.1
    IsArtinianRing ((ambientStalk d (a w.1)) ⧸
      (RingHom.ker (d.stalkMap (a w.1)).hom ⊔
        Module.annihilator (ambientStalk d (a w.1))
          (coefficientStalkModule d (a w.1) j (b w.1) hp))) := by
  dsimp only
  have : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsLocallyNoetherian X.left)
  have := LocallyOfFiniteType.isLocallyNoetherian (F.tripleIncidenceSource G H)
  rw [coefficientStalkModule_annihilator]
  exact stalk_sum_quotient_isArtinian _ _ _ _ (F.tripleIncidence_sixfold_isPullback G H) w.1 w.2

end Smooth

end Motivic.MotivicTest.TripleDiagonalAmbient
