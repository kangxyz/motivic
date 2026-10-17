/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.RightExteriorPairStalks
public import Motivic.AlgebraicGeometry.Cycles.RightWholeFiberTorBounded
public import Motivic.AlgebraicGeometry.Correspondences.TorIncidenceCycle
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Actual right whole Tor generic coefficients and cycle

The sheaf is the restriction of the existing right-first whole ambient Tor
coefficient, constructed on the entire finite inverse image. Its original
stalk in every degree is compared to the original G,H pair Tor through the
actual exterior Cartesian squares. The first support is flat over Spec k;
no flatness over Y, normality, or smoothness of that support is used.

The genuine closed fiber retains nilpotents. Its finite length and the finite
support in Tor degrees are proved before any integer conversion. The cycle
uses every generic branch of the whole inverse image, including empty and
disconnected cases. Finite-image degree balance, collisions, remaining-diagonal
replacement, and identification with the iterated pairing are separate steps.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.LengthEuler

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {k : Type u} [Field k]
  {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)
  (V : (F.rightIntermediateImageProduct G H).affineOpens)

local instance rightGenericBaseIsSeparated :
    ((Functor.fromPUnit (Spec (.of k))).obj X.right).IsSeparated :=
  inferInstanceAs (Spec (.of k)).IsSeparated

local instance : (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated (S := Spec (.of k)) X.hom Y.hom Z.hom W.hom

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k)) X.hom Y.hom Z.hom W.hom

local instance : IsLocallyNoetherian (F.rightIntermediateSupportProduct G H) :=
  LocallyOfFiniteType.isLocallyNoetherian (F.rightIntermediateAmbientInclusion G H)

/-- The entire actual inverse-image open of the right finite image-product map. -/
abbrev rightFirstStageWholeOpen := ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).toScheme

/-- Finiteness of the original map makes the whole open affine; its original
locally Noetherian structure therefore makes it Noetherian. -/
instance rightFirstStageWholeOpen_isNoetherian :
    IsNoetherian (F.rightFirstStageWholeOpen G H V) where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace := by
    have : IsAffine (F.rightFirstStageWholeOpen G H V) :=
      V.2.preimage (F.rightIntermediateImageMap G H)
    infer_instance

/-- The existing right-first Tor construction restricted to its full finite
inverse image, before any generic-branch selection. -/
abbrev rightFirstStageWholeTorSheaf (n : ℕ) :=
  Intersection.wholeFiberTorCoefficient (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion X.hom Y.hom Z.hom W.hom)
    (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
    (F.rightIntermediate_ambient_isPullback G H) (F.rightIntermediateImageMap G H) V n

/-- This is literally the restriction of the already constructed right whole
ambient coefficient used in the original finite-pushforward calculation. -/
theorem rightFirstStageWholeTorSheaf_eq_restrict (n : ℕ) :
    F.rightFirstStageWholeTorSheaf G H V n =
      (Scheme.Modules.restrictFunctor ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).ι).obj
        (F.rightFirstStageWholeAmbientCoefficient G H V n) := rfl

/-- The original global first-stage generic associated to a whole-open generic. -/
def rightFirstStageWholeGenericOriginal
    (w : genericPoints (F.rightFirstStageWholeOpen G H V)) :
    genericPoints (F.rightIntermediateSupportProduct G H) :=
  ⟨w.1.1, mem_genericPoints_of_generalizing ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).ι
    (Flat.generalizingMap _) w.1 w.2⟩

/-- The direct exterior projection is flat over the base field, so the actual
whole generic maps to a genuine original G,H incidence generic point. -/
def rightFirstStageWholeGenericPair
    (w : genericPoints (F.rightFirstStageWholeOpen G H V)) : genericPoints (G.incidence H) :=
  ⟨F.rightExteriorPairProjection G H w.1.1,
    F.rightExteriorPairProjection_mem_genericPoints (S := Spec (.of k)) G H w.1.1
      (F.rightFirstStageWholeGenericOriginal G H V w).2⟩

/-- The actual sheaf-stalk family with its original whole-open structure action. -/
abbrev rightFirstStageWholeGenericStalk
    (w : genericPoints (F.rightFirstStageWholeOpen G H V)) (n : ℕ) :=
  (ModuleStalk.functor w.1).obj (F.rightFirstStageWholeTorSheaf G H V n)

/-- The exact original support-stalk attachment, through the actual open
inclusion's structure-stalk map, precedes the numerical length comparison. -/
def rightFirstStageWholeGenericStalkOriginalIso
    (w : genericPoints (F.rightFirstStageWholeOpen G H V)) (n : ℕ) :
    (ModuleCat.restrictScalars
      (((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).ι.stalkMap w.1).hom).obj
        (F.rightFirstStageWholeGenericStalk G H V w n) ≅
      Intersection.closedIntersectionSupportedStalkTor
        (correspondenceSecondAmbientInclusion X.hom Y.hom Z.hom W.hom)
        (F.tripleSupportProductInclusion G H)
        (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
        (F.rightIntermediate_ambient_isPullback G H) w.1.1 n :=
  Intersection.wholeFiberTorCoefficientOriginalStalkIso
    (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion X.hom Y.hom Z.hom W.hom)
    (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
    (F.rightIntermediate_ambient_isPullback G H) (F.rightIntermediateImageMap G H) V w.1 n

/-- Every actual right whole sheaf-stalk degree has the original G,H pair Tor
length times its actual exterior incidence local closed-fiber length. -/
theorem rightFirstStageWholeGeneric_length
    (w : genericPoints (F.rightFirstStageWholeOpen G H V)) (n : ℕ) :
    Module.length ((F.rightFirstStageWholeOpen G H V).presheaf.stalk w.1)
        (F.rightFirstStageWholeGenericStalk G H V w n) =
      Module.length (G.incidenceAmbientStalk H (F.rightFirstStageWholeGenericPair G H V w).1)
        (G.incidenceTor H (F.rightFirstStageWholeGenericPair G H V w).1 n) *
          Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk w.1.1)
            (F.rightExteriorClosedFiber G H w.1.1) := by
  have he := (F.rightFirstStageWholeGenericStalkOriginalIso G H V w n).toLinearEquiv.length_eq
  rw [TorComparison.length_restrictScalars_of_surjective _
    (((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).ι.stalkMap_surjective w.1)] at he
  exact he.trans (F.rightExteriorSupportedTor_length (S := Spec (.of k)) G H w.1.1 n)

/-- The local closed fiber is a quotient of the original Artinian generic
right-incidence-product stalk, so its length is finite without reduction. -/
theorem rightFirstStageWholeGenericFiber_length_ne_top
    (w : genericPoints (F.rightFirstStageWholeOpen G H V)) :
    Module.length ((F.rightIntermediateSupportProduct G H).presheaf.stalk w.1.1)
      (F.rightExteriorClosedFiber G H w.1.1) ≠ ⊤ := by
  have := isArtinianRing_stalk_of_mem_genericPoints w.1.1
    (F.rightFirstStageWholeGenericOriginal G H V w).2
  exact Module.length_ne_top

/-- All right whole generic stalk lengths are finite and vanish outside
finitely many degrees, by the proved original pair and closed-fiber formula. -/
theorem rightFirstStageWholeGeneric_finiteLengthSupport
    (w : genericPoints (F.rightFirstStageWholeOpen G H V)) :
    FiniteLengthSupport (F.rightFirstStageWholeGenericStalk G H V w) := by
  have hpair := G.incidenceTor_finiteLengthSupport (S := Spec (.of k)) H
    (F.rightFirstStageWholeGenericPair G H V w).1 (F.rightFirstStageWholeGenericPair G H V w).2
  refine ⟨fun n => ?_, ?_⟩
  · rw [F.rightFirstStageWholeGeneric_length G H V w n]
    exact WithTop.mul_ne_top (hpair.finite_length n)
      (F.rightFirstStageWholeGenericFiber_length_ne_top G H V w)
  · apply hpair.finite_support.subset
    intro n hn
    change Module.length _ (G.incidenceTor H (F.rightFirstStageWholeGenericPair G H V w).1 n) ≠ 0
    intro hz
    apply hn
    change Module.length _ (F.rightFirstStageWholeGenericStalk G H V w n) = 0
    rw [F.rightFirstStageWholeGeneric_length G H V w n, hz, zero_mul]

/-- The genuine right exterior closed-fiber multiplicity, converted to an
integer only after its finite length has been proved. -/
def rightFirstStageWholeGenericFiberMultiplicity
    (w : genericPoints (F.rightFirstStageWholeOpen G H V)) : ℤ :=
  integerLength (F.rightExteriorClosedFiber G H w.1.1)
    (F.rightFirstStageWholeGenericFiber_length_ne_top G H V w)

/-- The alternating sum of all actual right whole generic sheaf-stalk degrees. -/
def rightFirstStageWholeTorGenericCoefficient
    (w : genericPoints (F.rightFirstStageWholeOpen G H V)) : ℤ :=
  signedLengthSum (F.rightFirstStageWholeGenericStalk G H V w) (fun n => (-1 : ℤ) ^ n)
    (F.rightFirstStageWholeGeneric_finiteLengthSupport G H V w)

/-- The actual right whole coefficient is the original G,H incidence Tor
coefficient times the true exterior closed-fiber multiplicity. -/
theorem rightFirstStageWholeTorGenericCoefficient_eq_pair_mul
    (w : genericPoints (F.rightFirstStageWholeOpen G H V)) :
    F.rightFirstStageWholeTorGenericCoefficient G H V w =
      G.incidenceTorCoefficient (S := Spec (.of k)) H (F.rightFirstStageWholeGenericPair G H V w) *
        F.rightFirstStageWholeGenericFiberMultiplicity G H V w := by
  unfold rightFirstStageWholeTorGenericCoefficient incidenceTorCoefficient signedLengthSum
  rw [finsum_mul]
  apply finsum_congr
  intro n
  simp only [integerLength, F.rightFirstStageWholeGeneric_length G H V w n,
    ENat.toNat_mul, Nat.cast_mul, mul_assoc, rightFirstStageWholeGenericFiberMultiplicity]

/-- The actual integral cycle uses every generic branch of the whole finite
inverse image and the original all-degree sheaf-stalk coefficient. -/
def rightFirstStageWholeTorGenericCycle : IntegralCycle (F.rightFirstStageWholeOpen G H V) :=
  IntegralCycle.ofGenericCoefficients (F.rightFirstStageWholeOpen G H V)
    (F.rightFirstStageWholeTorGenericCoefficient G H V)

/-- The actual whole right Tor cycle has its original pair weights and genuine
exterior multiplicities, without image injectivity or constant residue degrees. -/
theorem rightFirstStageWholeTorGenericCycle_eq_pair_mul :
    F.rightFirstStageWholeTorGenericCycle G H V =
      IntegralCycle.ofGenericCoefficients (F.rightFirstStageWholeOpen G H V)
        (fun w => G.incidenceTorCoefficient (S := Spec (.of k)) H
          (F.rightFirstStageWholeGenericPair G H V w) *
          F.rightFirstStageWholeGenericFiberMultiplicity G H V w) := by
  unfold rightFirstStageWholeTorGenericCycle
  congr 1
  funext w
  exact F.rightFirstStageWholeTorGenericCoefficient_eq_pair_mul G H V w

end Motivic.FiniteCorrespondenceGenerator
