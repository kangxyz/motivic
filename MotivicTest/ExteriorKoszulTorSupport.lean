/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Intersection.ExteriorKoszulTorSupport

/-!
# Actual pair and exterior support-Tor consumers

The pair consumer identifies the canonical quotient support action with the
existing incidenceTorOnIncidence module. The exterior consumers use the genuine
first-stage Cartesian square and derive Noetherian finite support homology from
the four structure maps and the constructed regular diagonal equations.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry RingTheory.Sequence
open Motivic Motivic.Intersection

namespace MotivicTest.ExteriorKoszulTorSupport

variable {S X Y Z W : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i) [IsSeparated g]

/-- The existing actual pair Tor carries precisely the canonical quotient support action. -/
def actualPairCanonicalSupport (w : F.incidence G) (n : ℕ) :=
  F.incidenceTorCanonicalSupportIso G w n

/-- The canonical support module matches the existing actual incidence-stalk
module, along the quotient equivalence forced by the original stalk map. -/
def actualPairSupportStalkAction [Flat f] [Smooth g] [Flat h] (w : F.incidence G) (n : ℕ) :
    let a := F.incidenceInclusion G
    let b := F.incidenceToSupportProduct G
    let d := correspondenceTripleInclusion f g h
    let j := F.supportProductInclusion G
    let hp := point_eq a b d j (F.incidence_ambient_isPullback G) w
    let I := RingHom.ker (d.stalkMap (a w)).hom ⊔
      RingHom.ker (coefficientStalkMap d (a w) j (b w) hp).hom
    let μ := F.incidenceAmbientStalkMap G w
    let hI : I = RingHom.ker μ :=
      (stalkMap_kernel_eq_sup a b d j (F.incidence_ambient_isPullback G) w).symm
    TorComparison.torSupportModule (RingHom.ker (d.stalkMap (a w)).hom)
      (RingHom.ker (coefficientStalkMap d (a w) j (b w) hp).hom) n ≅
      (ModuleCat.restrictScalars
        ((Ideal.quotEquivOfEq hI).trans
          (μ.quotientKerEquivOfSurjective
            (F.incidenceAmbientStalkMap_surjective G w))).toRingHom).obj
        (F.incidenceTorOnIncidence G w n) :=
  torSupportActualStalkIso (F.incidenceInclusion G) (F.incidenceToSupportProduct G)
    (correspondenceTripleInclusion f g h) (F.supportProductInclusion G)
    (F.incidence_ambient_isPullback G) w n

/-- Actual Noetherian geometry and finite categorical Tor give finite generation
of the already-defined pair incidence-stalk module, without finite-length assumptions. -/
theorem actualPairFinite [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType h] [Flat f] [Smooth g] [Flat h]
    (w : F.incidence G) (n : ℕ) :
    Module.Finite ((F.incidence G).presheaf.stalk w) (F.incidenceTorOnIncidence G w n) := by
  have := isLocallyNoetherian_correspondenceIntersectionAmbient f g h
  have : IsNoetherianRing (F.incidenceAmbientStalk G w) := inferInstance
  have : Module.Finite (F.incidenceAmbientStalk G w) (F.incidenceTripleStalkModule G w) :=
    sourceStalkModule_finite _ _
  have : Module.Finite (F.incidenceAmbientStalk G w) (F.incidenceTor G w n) :=
    TorComparison.finite_actual_tor (F.incidenceSupportStalkModule G w)
      (F.incidenceTripleStalkModule G w) n
  exact StalkDescent.descendedModule_finite _ _ _ _

/-- The actual exterior first-stage stalk action comes from its original
six-factor intersection, with no affine presentation supplied as a premise. -/
def actualExteriorSupportStalkAction (w : F.leftIntermediateSupportProduct G H) (n : ℕ) :=
  torSupportActualStalkIso (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (correspondenceFirstDiagonalInclusion f g h i)
    (F.tripleSupportProductInclusion G H) (F.leftIntermediate_ambient_isPullback G H) w n

/-- The canonical quotient uses the full actual first-stage stalk-map kernel. -/
theorem actualExteriorIdeal (w : F.leftIntermediateSupportProduct G H) :
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let d := correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let hp := point_eq a b d j (F.leftIntermediate_ambient_isPullback G H) w
    RingHom.ker (d.stalkMap (a w)).hom ⊔
        RingHom.ker (coefficientStalkMap d (a w) j (b w) hp).hom =
      RingHom.ker ((F.leftIntermediateAmbientInclusion G H).stalkMap w).hom :=
  F.exteriorTorSupportIdeal_eq G H w

/-- Actual finite-type geometry supplies Noetherianity. The genuine middle
list and its quotient-linear Tor comparison then give finite support homology
in every degree, without any homology-finiteness input or coefficient regularity. -/
theorem actualExteriorFiniteSupport [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] [LocallyOfFiniteType h] [LocallyOfFiniteType i]
    [Flat f] [Smooth g] [Flat h] [Flat i] (w : F.leftIntermediateSupportProduct G H) :
    let a := F.leftIntermediateSupportInclusion G H
    let b := F.leftIntermediateToTripleSupport G H
    let d := correspondenceFirstDiagonalInclusion f g h i
    let j := F.tripleSupportProductInclusion G H
    let hp := point_eq a b d j (F.leftIntermediate_ambient_isPullback G H) w
    let R := ambientStalk d (a w)
    let M := coefficientStalkModule d (a w) j (b w) hp
    let I := RingHom.ker (d.stalkMap (a w)).hom ⊔
      RingHom.ker (coefficientStalkMap d (a w) j (b w) hp).hom
    ∃ s : List R, ∃ hs : IsRegular R s,
      ∃ hker : RingHom.ker (d.stalkMap (a w)).hom = Ideal.ofList s,
      ∀ n : ℕ,
        Module.Finite (R ⧸ I)
          (TorComparison.quotientModule I ((Koszul.coefficientComplex M s).homology n)
            (stalkSupport_annihilates_homology d (a w) j (b w) hp s hker hs n)) ∧
        Nonempty
          (TorComparison.torSupportModule (RingHom.ker (d.stalkMap (a w)).hom)
            (RingHom.ker (coefficientStalkMap d (a w) j (b w) hp).hom) n ≅
          TorComparison.quotientModule I ((Koszul.coefficientComplex M s).homology n)
            (stalkSupport_annihilates_homology d (a w) j (b w) hp s hker hs n)) := by
  have := isLocallyNoetherian_correspondenceSixfoldAmbient f g h i
  dsimp only
  obtain ⟨s, hs, hker, he⟩ := F.exists_exteriorKoszulSupportLinear G H w
  exact ⟨s, hs, hker, fun n => ⟨finite_stalkSupport_homology _ _ _ _ _ s hker hs n, he n⟩⟩

end MotivicTest.ExteriorKoszulTorSupport
