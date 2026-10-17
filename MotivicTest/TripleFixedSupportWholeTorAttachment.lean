/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.TripleFixedSupportWholeTorAttachment
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Original smooth-site generic sheaf weights on the exact local support index

These consumers retain the genuine whole inverse image, original triple point,
and precise specializing source-generic subtype. They do not supply an expected
coefficient equality or an assumed generic source/image bijection.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.LengthEuler
open scoped TensorProduct

universe u

namespace Motivic.MotivicTest.TripleFixedSupportWholeTorAttachment

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.leftIntermediateImageProduct G H).affineOpens)

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
    X.hom Y.hom Z.hom W.hom

/-- The original smooth diagonal constructs the list and attaches every actual
local generic coefficient to the original whole Tor sheaf. -/
theorem actualConstructedWholeGenericWeights
    (w : F.tripleIncidence G H)
    (hV : F.tripleIncidenceToLeftSupportProduct G H w ∈
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) :
    ∃ (t : List (F.tripleIncidenceAmbientStalk G H w))
      (ht : (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
        (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t),
      RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w) t ∧
        ∀ y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
          y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w},
          Koszul.twoListGenericEuler (F.tripleIncidenceSupportStalkModule G H w) t
              ((F.tripleFirstStageSupportGenericEquiv G H w t ht).symm y) =
            F.firstStageWholeTorGenericCoefficient G H V
              (F.tripleFirstStageWholeGeneric G H V w hV y) :=
  F.exists_firstStageWholeGeneric_attachment G H V w hV

/-- The local weight is the original pair coefficient times its actual exterior
closed-fiber multiplicity, preserving the exact source branch. -/
theorem actualOriginalPairWeightedSummand
    (w : F.tripleIncidence G H)
    (hV : F.tripleIncidenceToLeftSupportProduct G H w ∈
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ V)
    (t : List (F.tripleIncidenceAmbientStalk G H w))
    (ht : (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w) = Ideal.ofList t)
    (hr : RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w) t)
    (y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
      y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w}) :
    let z := F.tripleFirstStageWholeGeneric G H V w hV y
    Koszul.twoListGenericEuler (F.tripleIncidenceSupportStalkModule G H w) t
        ((F.tripleFirstStageSupportGenericEquiv G H w t ht).symm y) =
      F.incidenceTorCoefficient (S := Spec (.of k)) G (F.firstStageWholeGenericPair G H V z) *
        F.firstStageWholeGenericFiberMultiplicity G H V z :=
  F.twoListGenericEuler_eq_original_pair_mul G H V w hV t ht hr y

/-- All genuine generic whole-sheaf coefficients and the exact remaining local
prime factors give canonical triple Tor on the original specializing index. -/
theorem actualWholeGenericWeightedTripleCoefficient
    (w : genericPoints (F.tripleIncidence G H))
    (hV : F.tripleIncidenceToLeftSupportProduct G H w.1 ∈
      (F.leftIntermediateImageMap G H) ⁻¹ᵁ V)
    (t s : List (F.tripleIncidenceAmbientStalk G H w.1))
    (ht : (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).ker.stalk
      (F.tripleIncidenceSixfoldInclusion G H w.1) = Ideal.ofList t)
    (hrt : RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w.1) t)
    (hr : RingTheory.Sequence.IsRegular (F.tripleIncidenceAmbientStalk G H w.1) (t ++ s))
    (hker : RingHom.ker
      ((correspondenceSecondDiagonalInclusion X.hom Y.hom Z.hom W.hom ≫
        correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom).stalkMap
          (F.tripleIncidenceFourfoldInclusion G H w.1)).hom = Ideal.ofList (t ++ s)) :
    letI := F.tripleTwoList_support_isArtinian (S := Spec (.of k)) G H w t s hker
    let M := F.tripleIncidenceSupportStalkModule G H w.1
    (∑ᶠ y : {y : genericPoints (F.leftIntermediateSupportProduct G H) //
      y.1 ⤳ F.tripleIncidenceToLeftSupportProduct G H w.1},
      let p := (F.tripleFirstStageSupportGenericEquiv G H w.1 t ht).symm y
      F.firstStageWholeTorGenericCoefficient G H V
          (F.tripleFirstStageWholeGeneric G H V w.1 hV y) *
        chainEuler (Koszul.coefficientComplex
          (ModuleCat.of (F.tripleIncidenceAmbientStalk G H w.1)
            ((F.tripleIncidenceAmbientStalk G H w.1) ⧸ p.1)) s)
          (Koszul.fixedSupport_prime_finiteHomology s
            (Ideal.ofList t ⊔ Module.annihilator (F.tripleIncidenceAmbientStalk G H w.1) M)
            p.1 p.2.le)) = F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w :=
  F.triple_originalWholeTor_fixedSupport_sum_eq_coefficient G H V w hV t s ht hrt hr hker

end Motivic.MotivicTest.TripleFixedSupportWholeTorAttachment
