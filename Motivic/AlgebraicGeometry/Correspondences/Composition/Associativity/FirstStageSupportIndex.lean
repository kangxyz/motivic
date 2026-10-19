/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.IncidenceTor
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Diagonal.IntermediateLists
public import Motivic.Aglib.AlgebraicGeometry.Stalk.KernelMinimalPrimes

/-!
# Literal first-stage support kernels and their actual generic indices

At an original triple-incidence point, first-middle equations plus the
annihilator of the original triple exterior stalk cut out the full first-stage
support stalk. The actual closed stalk map is aligned by the proved equality
of ambient points. Its minimal primes correspond exactly to global first-stage
support generics specializing to the chosen point. This retains nilpotents in
the support stalk and does not replace the index by every global component or
by generic points of a finite image.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

section

namespace AlgebraicGeometry.Scheme.Intersection

variable {D T P : Scheme.{u}} (i : D ⟶ P) (d : D) (j : T ⟶ P) (t : T)
  (hp : i d = j t) [IsClosedImmersion j]

/-- The equality-aligned actual closed stalk map has the literal ideal-sheaf
kernel at the original ambient point. -/
theorem coefficientStalkMap_kernel_eq_stalk :
    RingHom.ker (coefficientStalkMap i d j t hp).hom = j.ker.stalk (i d) := by
  rw [coefficientStalkMap, CommRingCat.hom_comp, ← RingHom.comap_ker,
    ← j.ker_stalk t, j.ker.stalk_congr_comap hp]

/-- Actual generic support indexing for the same closed stalk map after its
necessary ambient-point equality transport. -/
def coefficientStalkKernelGenericEquiv :
    (RingHom.ker (coefficientStalkMap i d j t hp).hom).minimalPrimes ≃
      {y : genericPoints T // y.1 ⤳ t} :=
  (kernelMinimalPrimeEquiv (coefficientStalkMap i d j t hp).hom
    (coefficientStalkMap_surjective i d j t hp)).symm |>.trans
      ((specGenericMinimalPrimeEquiv (T.presheaf.stalk t)).symm.trans
        (stalkGenericPointEquiv T t))

/-- The inverse still contracts the actual stalk prime through the literal
aligned map; no independently selected prime is introduced. -/
theorem coefficientStalkKernelGenericEquiv_symm_val
    (y : {y : genericPoints T // y.1 ⤳ t}) :
    ((coefficientStalkKernelGenericEquiv i d j t hp).symm y).1 =
      (((stalkGenericPointEquiv T t).symm y).1.asIdeal).comap
        (coefficientStalkMap i d j t hp).hom := rfl

end AlgebraicGeometry.Scheme.Intersection

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The first-stage support point has exactly the original six-factor ambient
image of the triple point. -/
theorem tripleFirstStage_ambient_point (w : F.tripleIncidence G H) :
    F.tripleIncidenceSixfoldInclusion G H w =
      F.leftIntermediateAmbientInclusion G H (F.tripleIncidenceToLeftSupportProduct G H w) :=
  (congrArg (fun m => m w) (F.tripleToLeftSupport_ambient G H)).symm

/-- The genuine closed first-stage stalk map, aligned to the original ambient
ring used by the canonical triple coefficient. -/
def tripleFirstStageStalkMap (w : F.tripleIncidence G H) :
    F.tripleIncidenceAmbientStalk G H w ⟶
      (F.leftIntermediateSupportProduct G H).presheaf.stalk
        (F.tripleIncidenceToLeftSupportProduct G H w) :=
  Intersection.coefficientStalkMap
    (correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleIncidenceFourfoldInclusion G H w) (F.leftIntermediateAmbientInclusion G H)
    (F.tripleIncidenceToLeftSupportProduct G H w) (F.tripleFirstStage_ambient_point G H w)

variable [IsSeparated g]

/-- The aligned actual first-stage stalk map is surjective, including on its
full nonreduced target stalk. -/
theorem tripleFirstStageStalkMap_surjective (w : F.tripleIncidence G H) :
    Function.Surjective (F.tripleFirstStageStalkMap G H w) :=
  Intersection.coefficientStalkMap_surjective
    (correspondenceSecondDiagonalInclusion f g h i ≫ correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleIncidenceFourfoldInclusion G H w) (F.leftIntermediateAmbientInclusion G H)
    (F.tripleIncidenceToLeftSupportProduct G H w) (F.tripleFirstStage_ambient_point G H w)

set_option backward.isDefEq.respectTransparency false in
/-- First-middle equations plus the original exterior annihilator are the
literal kernel of the genuine closed first-stage support stalk map. -/
theorem tripleFirstStage_support_ideal_eq_kernel (w : F.tripleIncidence G H)
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (ht : (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t) :
    Ideal.ofList t ⊔ Module.annihilator (F.tripleIncidenceAmbientStalk G H w)
        (F.tripleIncidenceSupportStalkModule G H w) =
      RingHom.ker (F.tripleFirstStageStalkMap G H w).hom := by
  rw [Intersection.coefficientStalkModule_annihilator,
    Intersection.coefficientStalkMap_kernel_eq_stalk, tripleFirstStageStalkMap,
    Intersection.coefficientStalkMap_kernel_eq_stalk,
    F.ker_leftIntermediateAmbientInclusion G H, Scheme.IdealSheafData.stalk_sup]
  exact congrArg (fun J => J ⊔ (F.tripleSupportProductInclusion G H).ker.stalk
    (F.tripleIncidenceSixfoldInclusion G H w)) ht.symm

/-- The exact equation-plus-annihilator quotient is the original full support
stalk, so the kernel identification has not passed to a reduction. -/
def tripleFirstStageSupportQuotientEquiv (w : F.tripleIncidence G H)
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (ht : (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t) :
    (F.tripleIncidenceAmbientStalk G H w) ⧸
      (Ideal.ofList t ⊔ Module.annihilator (F.tripleIncidenceAmbientStalk G H w)
        (F.tripleIncidenceSupportStalkModule G H w)) ≃+*
      (F.leftIntermediateSupportProduct G H).presheaf.stalk
        (F.tripleIncidenceToLeftSupportProduct G H w) :=
  (Ideal.quotEquivOfEq (F.tripleFirstStage_support_ideal_eq_kernel G H w t ht)).trans
    ((F.tripleFirstStageStalkMap G H w).hom.quotientKerEquivOfSurjective
      (F.tripleFirstStageStalkMap_surjective G H w))

/-- The fixed-support prime index is exactly the specialization subtype of
genuine global first-stage source generics at the chosen triple point. -/
def tripleFirstStageSupportGenericEquiv (w : F.tripleIncidence G H)
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (ht : (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t) :
    (Ideal.ofList t ⊔ Module.annihilator (F.tripleIncidenceAmbientStalk G H w)
      (F.tripleIncidenceSupportStalkModule G H w)).minimalPrimes ≃
        {y : genericPoints (F.leftIntermediateSupportProduct G H) //
          y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w} :=
  (Set.equivOfEq (congrArg Ideal.minimalPrimes
    (F.tripleFirstStage_support_ideal_eq_kernel G H w t ht))).trans
      (Intersection.coefficientStalkKernelGenericEquiv
        (correspondenceSecondDiagonalInclusion f g h i ≫
          correspondenceFirstDiagonalInclusion f g h i)
        (F.tripleIncidenceFourfoldInclusion G H w) (F.leftIntermediateAmbientInclusion G H)
        (F.tripleIncidenceToLeftSupportProduct G H w) (F.tripleFirstStage_ambient_point G H w))

/-- The geometric inverse index is the literal contraction of the actual
stalk-spectrum generic prime through the aligned closed immersion. -/
theorem tripleFirstStageSupportGenericEquiv_symm_val (w : F.tripleIncidence G H)
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (ht : (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
      y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w}) :
    ((F.tripleFirstStageSupportGenericEquiv G H w t ht).symm y).1 =
      (((stalkGenericPointEquiv (F.leftIntermediateSupportProduct G H)
        (F.tripleIncidenceToLeftSupportProduct G H w)).symm y).1.asIdeal).comap
          (F.tripleFirstStageStalkMap G H w).hom := rfl

/-- Reindexing uses only support components specializing to the actual
first-stage point. It does not sum over unrelated global components. -/
theorem tripleFirstStageSupport_finsum (w : F.tripleIncidence G H)
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (ht : (correspondenceFirstDiagonalInclusion f g h i).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (c : (Ideal.ofList t ⊔ Module.annihilator (F.tripleIncidenceAmbientStalk G H w)
      (F.tripleIncidenceSupportStalkModule G H w)).minimalPrimes → ℤ) :
    (∑ᶠ p, c p) =
      ∑ᶠ y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
        y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w},
        c ((F.tripleFirstStageSupportGenericEquiv G H w t ht).symm y) :=
  (finsum_comp_equiv (F.tripleFirstStageSupportGenericEquiv G H w t ht).symm
    (f := c)).symm

end Motivic.FiniteCorrespondenceGenerator

end
