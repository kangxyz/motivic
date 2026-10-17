/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.ExteriorPairStalks
public import Motivic.AlgebraicGeometry.Intersection.WholeFiberTorStalk
public import Motivic.AlgebraicGeometry.Correspondences.TorIncidenceCycle
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Actual generic coefficients of the whole first-stage Tor sheaf

At a genuine generic point of the entire finite inverse image, the constructed
Tor sheaf has its original stalk. Its length in every degree is the original
pair-incidence Tor length times the actual exterior incidence closed-fiber
length. Flatness supplies the pair generic point, the closed-fiber quotient
retains nilpotents, and finiteness is proved before the alternating integer sum.
No component-image injectivity or residue degree is discarded. Finite-image
pushforward and collision regrouping remain separate from this coefficient
identity.
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
  (V : (F.leftIntermediateImageProduct G H).affineOpens)

local instance : (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated (S := Spec (.of k)) X.hom Y.hom Z.hom W.hom

local instance : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k)) X.hom Y.hom Z.hom W.hom

local instance : IsLocallyNoetherian (F.leftIntermediateSupportProduct G H) :=
  LocallyOfFiniteType.isLocallyNoetherian (F.leftIntermediateAmbientInclusion G H)

/-- The actual whole finite inverse image, retaining every source branch. -/
abbrev firstStageWholeOpen := ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V).toScheme

/-- The whole finite inverse image is affine and locally Noetherian, hence
Noetherian, without any assertion that the whole support is integral. -/
instance firstStageWholeOpen_isNoetherian : IsNoetherian (F.firstStageWholeOpen G H V) where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace := by
    have : IsAffine (F.firstStageWholeOpen G H V) := V.2.preimage (F.leftIntermediateImageMap G H)
    infer_instance

/-- The original constructed coefficient sheaf on the entire finite inverse image. -/
abbrev firstStageWholeTorSheaf (n : ℕ) :=
  Intersection.wholeFiberTorCoefficient (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) V n

/-- A genuine generic point of the actual whole open has its original global
first-stage generic point. Open restriction preserves component genericity. -/
def firstStageWholeGenericOriginal (w : genericPoints (F.firstStageWholeOpen G H V)) :
    genericPoints (F.leftIntermediateSupportProduct G H) :=
  ⟨w.1.1, mem_genericPoints_of_generalizing ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V).ι
    (Flat.generalizingMap _) w.1 w.2⟩

/-- Flat exterior projection attaches an actual whole-open generic point to a
true generic point of the original pair-incidence scheme. -/
def firstStageWholeGenericPair (w : genericPoints (F.firstStageWholeOpen G H V)) :
    genericPoints (F.incidence G) :=
  ⟨F.leftExteriorPairProjection G H w.1.1,
    F.leftExteriorPairProjection_mem_genericPoints (S := Spec (.of k)) G H w.1.1
      (F.firstStageWholeGenericOriginal G H V w).2⟩

/-- The genuine sheaf stalk family, with the original open structure-stalk action. -/
abbrev firstStageWholeGenericStalk
    (w : genericPoints (F.firstStageWholeOpen G H V)) (n : ℕ) :=
  (ModuleStalk.functor w.1).obj (F.firstStageWholeTorSheaf G H V n)

/-- The actual whole-open stalk length is the original pair Tor length times
the genuine exterior-incidence local closed fiber, in every degree. -/
theorem firstStageWholeGeneric_length
    (w : genericPoints (F.firstStageWholeOpen G H V)) (n : ℕ) :
    Module.length ((F.firstStageWholeOpen G H V).presheaf.stalk w.1)
        (F.firstStageWholeGenericStalk G H V w n) =
      Module.length (F.incidenceAmbientStalk G (F.firstStageWholeGenericPair G H V w).1)
        (F.incidenceTor G (F.firstStageWholeGenericPair G H V w).1 n) *
          Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk w.1.1)
            (F.leftExteriorClosedFiber G H w.1.1) := by
  have he := (Intersection.wholeFiberTorCoefficientOriginalStalkIso
    (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion X.hom Y.hom Z.hom W.hom)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (F.leftIntermediate_ambient_isPullback G H) (F.leftIntermediateImageMap G H) V
    w.1 n).toLinearEquiv.length_eq
  rw [TorComparison.length_restrictScalars_of_surjective _
    (((F.leftIntermediateImageMap G H) ⁻¹ᵁ V).ι.stalkMap_surjective w.1)] at he
  exact he.trans (F.leftExteriorSupportedTor_length (S := Spec (.of k)) G H w.1.1 n)

/-- The actual local closed fiber has finite length because it is a quotient
of the genuine Artinian generic incidence-product stalk. -/
theorem firstStageWholeGenericFiber_length_ne_top
    (w : genericPoints (F.firstStageWholeOpen G H V)) :
    Module.length ((F.leftIntermediateSupportProduct G H).presheaf.stalk w.1.1)
      (F.leftExteriorClosedFiber G H w.1.1) ≠ ⊤ := by
  have := isArtinianRing_stalk_of_mem_genericPoints w.1.1
    (F.firstStageWholeGenericOriginal G H V w).2
  exact Module.length_ne_top

/-- Every actual whole-coefficient generic stalk has finite length in finitely
many Tor degrees, derived from the original pair and the proved local fiber. -/
theorem firstStageWholeGeneric_finiteLengthSupport
    (w : genericPoints (F.firstStageWholeOpen G H V)) :
    FiniteLengthSupport (F.firstStageWholeGenericStalk G H V w) := by
  have hpair := F.incidenceTor_finiteLengthSupport (S := Spec (.of k)) G
    (F.firstStageWholeGenericPair G H V w).1 (F.firstStageWholeGenericPair G H V w).2
  refine ⟨fun n => ?_, ?_⟩
  · rw [F.firstStageWholeGeneric_length G H V w n]
    exact WithTop.mul_ne_top (hpair.finite_length n)
      (F.firstStageWholeGenericFiber_length_ne_top G H V w)
  · apply hpair.finite_support.subset
    intro n hn
    change Module.length _ (F.incidenceTor G (F.firstStageWholeGenericPair G H V w).1 n) ≠ 0
    intro hz
    apply hn
    change Module.length _ (F.firstStageWholeGenericStalk G H V w n) = 0
    rw [F.firstStageWholeGeneric_length G H V w n, hz, zero_mul]

/-- The actual exterior generic closed-fiber multiplicity is converted only
after finite length has been established; it is not replaced by one. -/
def firstStageWholeGenericFiberMultiplicity
    (w : genericPoints (F.firstStageWholeOpen G H V)) : ℤ :=
  integerLength (F.leftExteriorClosedFiber G H w.1.1)
    (F.firstStageWholeGenericFiber_length_ne_top G H V w)

/-- The original whole Tor sheaf's genuine all-degree generic coefficient. -/
def firstStageWholeTorGenericCoefficient
    (w : genericPoints (F.firstStageWholeOpen G H V)) : ℤ :=
  signedLengthSum (F.firstStageWholeGenericStalk G H V w) (fun n => (-1 : ℤ) ^ n)
    (F.firstStageWholeGeneric_finiteLengthSupport G H V w)

/-- The whole coefficient's actual generic multiplicity is the original
pair-incidence Tor coefficient times its actual exterior closed-fiber factor. -/
theorem firstStageWholeTorGenericCoefficient_eq_pair_mul
    (w : genericPoints (F.firstStageWholeOpen G H V)) :
    F.firstStageWholeTorGenericCoefficient G H V w =
      F.incidenceTorCoefficient (S := Spec (.of k)) G (F.firstStageWholeGenericPair G H V w) *
        F.firstStageWholeGenericFiberMultiplicity G H V w := by
  unfold firstStageWholeTorGenericCoefficient incidenceTorCoefficient signedLengthSum
  rw [finsum_mul]
  apply finsum_congr
  intro n
  simp only [integerLength, F.firstStageWholeGeneric_length G H V w n,
    ENat.toNat_mul, Nat.cast_mul, mul_assoc, firstStageWholeGenericFiberMultiplicity]

/-- The actual whole coefficient cycle uses every generic point of the
entire inverse image and the original all-degree sheaf-stalk lengths. -/
def firstStageWholeTorGenericCycle : IntegralCycle (F.firstStageWholeOpen G H V) :=
  IntegralCycle.ofGenericCoefficients (F.firstStageWholeOpen G H V)
    (F.firstStageWholeTorGenericCoefficient G H V)

/-- The actual whole first-stage cycle has the original pair Tor weights
multiplied by each genuine exterior generic closed-fiber multiplicity. -/
theorem firstStageWholeTorGenericCycle_eq_pair_mul :
    F.firstStageWholeTorGenericCycle G H V =
      IntegralCycle.ofGenericCoefficients (F.firstStageWholeOpen G H V)
        (fun w => F.incidenceTorCoefficient (S := Spec (.of k)) G
          (F.firstStageWholeGenericPair G H V w) *
          F.firstStageWholeGenericFiberMultiplicity G H V w) := by
  unfold firstStageWholeTorGenericCycle
  congr 1
  funext w
  exact F.firstStageWholeTorGenericCoefficient_eq_pair_mul G H V w

end Motivic.FiniteCorrespondenceGenerator
