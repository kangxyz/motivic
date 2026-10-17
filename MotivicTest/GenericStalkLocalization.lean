/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.GenericStalkLocalization
public import Motivic.AlgebraicGeometry.Correspondences.IteratedIncidenceSupport
public import Motivic.AlgebraicGeometry.Correspondences.TripleGenericDominance

/-! # Actual triple kernel-prime, global stalk and scalar-action consumers -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Motivic

universe u

namespace Motivic.MotivicTest.GenericStalkLocalization

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- A global triple component through an actual point has its genuine stalk
identified with the literal local-ring localization, including nilpotents. -/
noncomputable def actualTripleGenericStalkIso (x : F.tripleIncidence G H)
    (y : {y : genericPoints (F.tripleIncidence G H) // y.1 ⤳ x}) :
    (F.tripleIncidence G H).presheaf.stalk y.1.1 ≅
      CommRingCat.of (Localization.AtPrime
        (genericStalkLocalizationPrime (F.tripleIncidence G H) x y).asIdeal) :=
  genericStalkLocalizationIso (F.tripleIncidence G H) x y

/-- The triple-stalk identification carries the actual specialization action
to the actual localization algebra map. -/
theorem actualTripleGenericScalarSquare (x : F.tripleIncidence G H)
    (y : {y : genericPoints (F.tripleIncidence G H) // y.1 ⤳ x}) :
    (F.tripleIncidence G H).presheaf.stalkSpecializes y.2 ≫
        (actualTripleGenericStalkIso k F G H x y).hom =
      CommRingCat.ofHom (algebraMap ((F.tripleIncidence G H).presheaf.stalk x)
        (Localization.AtPrime
          (genericStalkLocalizationPrime (F.tripleIncidence G H) x y).asIdeal)) :=
  stalkSpecializes_genericStalkLocalizationIso (F.tripleIncidence G H) x y

/-- The prime associated with an actual second-diagonal kernel contracts to
that same supplied kernel prime, rather than merely an unspecified component. -/
theorem actualTripleKernelPrimeContraction (x : F.tripleIncidence G H)
    (p : (RingHom.ker ((F.tripleIncidenceToLeftSupportProduct G H).stalkMap x).hom).minimalPrimes) :
    (genericStalkLocalizationPrime (F.tripleIncidence G H) x
      (stalkKernelGenericEquiv (F.tripleIncidenceToLeftSupportProduct G H) x p)).asIdeal.comap
        ((F.tripleIncidenceToLeftSupportProduct G H).stalkMap x).hom = p.1 :=
  genericStalkLocalizationPrime_kernel_comap (F.tripleIncidenceToLeftSupportProduct G H) x p

/-- The literal local ring at the kernel-indexed component prime is Artinian,
derived from actual generic geometry and transported by the proved stalk iso. -/
theorem actualTripleKernelPrimeLocalizationArtinian (x : F.tripleIncidence G H)
    (p : (RingHom.ker ((F.tripleIncidenceToLeftSupportProduct G H).stalkMap x).hom).minimalPrimes) :
    IsArtinianRing (Localization.AtPrime
      (genericStalkLocalizationPrime (F.tripleIncidence G H) x
        (stalkKernelGenericEquiv (F.tripleIncidenceToLeftSupportProduct G H) x p)).asIdeal) := by
  have : IsLocallyNoetherian ((𝟭 Scheme).obj X.left) :=
    inferInstanceAs (IsLocallyNoetherian X.left)
  have := LocallyOfFiniteType.isLocallyNoetherian (F.tripleIncidenceSource G H)
  let y := stalkKernelGenericEquiv (F.tripleIncidenceToLeftSupportProduct G H) x p
  have := isArtinianRing_stalk_of_mem_genericPoints y.1.1 y.1.2
  exact (genericStalkLocalizationIso (F.tripleIncidence G H) x y).commRingCatIsoToRingEquiv
    |>.isArtinianRing

end Motivic.MotivicTest.GenericStalkLocalization
