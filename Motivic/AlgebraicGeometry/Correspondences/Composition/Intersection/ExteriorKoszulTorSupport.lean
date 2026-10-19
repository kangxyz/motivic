/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.Tor.Support

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FiniteGeneration
public import Motivic.Aglib.AlgebraicGeometry.Intersection.TransverseTor
public import Motivic.Aglib.AlgebraicGeometry.Intersection.Triple.DiagonalRegularity
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.IntermediateModules
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.DiagonalAmbient

/-!
# Actual pair and exterior stalks with canonical Tor support actions

The two literal closed-stalk kernels present the actual source and coefficient
modules. Their categorical Tor is therefore the canonical torSupportModule
after the actual quotient scalar restriction. A genuine regular diagonal list
identifies actual Koszul homology with that same module. The comparison itself
is lifted over the full sum quotient, and finite generation follows from actual
Noetherian Tor. No affine support chart or global sheaf existence is assumed.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence


namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated g]

/-- The original pair incidence Tor is the canonical support Tor for its two
literal ambient stalk kernels, with exactly its original ambient action. -/
def incidenceTorCanonicalSupportIso (w : F.incidence G) (n : ℕ) :
    let d := correspondenceTripleInclusion f g h
    let a := F.incidenceInclusion G
    let j := F.supportProductInclusion G
    let b := F.incidenceToSupportProduct G
    let hp := point_eq a b d j (F.incidence_ambient_isPullback G) w
    F.incidenceTor G w n ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk
        (RingHom.ker (d.stalkMap (a w)).hom ⊔
          RingHom.ker (coefficientStalkMap d (a w) j (b w) hp).hom))).obj
        (_root_.ModuleCat.TorComparison.torSupportModule (RingHom.ker (d.stalkMap (a w)).hom)
          (RingHom.ker (coefficientStalkMap d (a w) j (b w) hp).hom) n) :=
  torSupportStalkRestrictIso _ _ _ _ _ n

/-- At an actual exterior first-stage point, the canonical Tor support quotient
is cut out by the genuine first-diagonal plus exterior coefficient kernels. -/
theorem exteriorTorSupportIdeal_eq (w : F.leftIntermediateSupportProduct G H) :
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let d := correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let hp := point_eq a b d j (F.leftIntermediate_ambient_isPullback G H) w
    RingHom.ker (d.stalkMap (a w)).hom ⊔
        RingHom.ker (coefficientStalkMap d (a w) j (b w) hp).hom =
      RingHom.ker ((F.leftIntermediateAmbientInclusion G H).stalkMap w).hom :=
  (stalkMap_kernel_eq_sup _ _ _ _ (F.leftIntermediate_ambient_isPullback G H) w).symm

/-- The genuine first middle list is constructed on the actual six-factor
stalk. Every degree of its original exterior-coefficient homology is the
restriction of the canonical quotient-supported Tor, with no comparison premise. -/
theorem exists_exteriorKoszulCanonicalSupport [Flat f] [Smooth g] [Flat h] [Flat i]
    (w : F.leftIntermediateSupportProduct G H) :
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let d := correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let hp := point_eq a b d j (F.leftIntermediate_ambient_isPullback G H) w
    let M := coefficientStalkModule d (a w) j (b w) hp
    ∃ s : List (ambientStalk d (a w)),
      IsRegular (ambientStalk d (a w)) s ∧
      RingHom.ker (d.stalkMap (a w)).hom = Ideal.ofList s ∧
      ∀ n : ℕ, Nonempty
        ((_root_.ChainComplex.Koszul.coefficientComplex M s).homology n ≅
          (ModuleCat.restrictScalars (Ideal.Quotient.mk
            (RingHom.ker (d.stalkMap (a w)).hom ⊔
              RingHom.ker (coefficientStalkMap d (a w) j (b w) hp).hom))).obj
            (_root_.ModuleCat.TorComparison.torSupportModule (RingHom.ker (d.stalkMap (a w)).hom)
              (RingHom.ker (coefficientStalkMap d (a w) j (b w) hp).hom) n)) := by
  dsimp only
  obtain ⟨s, hs, hker⟩ := exists_regular_kernel_correspondenceFirstDiagonal f g h i
    (F.leftIntermediateSupportInclusion G H w)
  exact ⟨s, hs, hker, fun n => ⟨homologyStalkSupportRestrictIso _ _ _ _ _ s hker hs n⟩⟩

/-- The actual exterior comparison is linear over the canonical first-stage
support quotient, not only over the six-factor ambient stalk. Its regular
list is constructed from the original smooth middle diagonal. -/
theorem exists_exteriorKoszulSupportLinear [Flat f] [Smooth g] [Flat h] [Flat i]
    (w : F.leftIntermediateSupportProduct G H) :
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let d := correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let hp := point_eq a b d j (F.leftIntermediate_ambient_isPullback G H) w
    let M := coefficientStalkModule d (a w) j (b w) hp
    ∃ s : List (ambientStalk d (a w)),
      ∃ hs : IsRegular (ambientStalk d (a w)) s,
      ∃ hker : RingHom.ker (d.stalkMap (a w)).hom = Ideal.ofList s,
      ∀ n : ℕ, Nonempty
        (_root_.ModuleCat.TorComparison.torSupportModule (RingHom.ker (d.stalkMap (a w)).hom)
          (RingHom.ker (coefficientStalkMap d (a w) j (b w) hp).hom) n ≅
        _root_.ModuleCat.TorComparison.quotientModule
          (RingHom.ker (d.stalkMap (a w)).hom ⊔
            RingHom.ker (coefficientStalkMap d (a w) j (b w) hp).hom)
          ((_root_.ChainComplex.Koszul.coefficientComplex M s).homology n)
          (stalkSupport_annihilates_homology d (a w) j (b w) hp s hker hs n)) := by
  dsimp only
  obtain ⟨s, hs, hker⟩ := exists_regular_kernel_correspondenceFirstDiagonal f g h i
    (F.leftIntermediateSupportInclusion G H w)
  exact ⟨s, hs, hker, fun n => ⟨torSupportHomologyStalkIso _ _ _ _ _ s hker hs n⟩⟩

end Motivic.FiniteCorrespondenceGenerator
