/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorFinite
public import Motivic.AlgebraicGeometry.Correspondences.TripleDiagonalRegularity

/-!
# Actual whole first-stage Tor coefficients vanish in high degrees

The original smooth middle diagonal supplies a regular kernel list at every
actual first-stage source point. Genuine Tor vanishing above that list length
transports through the constructed whole-coefficient stalk isomorphism. The
actual finite source fiber then supplies a uniform bound for the entire whole
localized family. No pointwise or uniform Tor bound is assumed as input.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

open Intersection FiniteSchemeEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

/-- The actual first-stage compatible-sections equalizer on its original support scheme. -/
abbrev firstStageWholeAmbientCoefficient
    (V : (F.leftIntermediateImageProduct G H).affineOpens) (n : ℕ) :=
  closedIntersectionTorGlued (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
    (wholeFiberTorAmbientFamily (F.tripleSupportProductInclusion G H)
      (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
      (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
      (F.leftIntermediateImageMap G H) V) n

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

/-- The actual image-product map supplies the original whole coordinate algebra action. -/
local instance firstStageWholeCoordinateAlgebra :
    Algebra Γ(F.leftIntermediateImageProduct G H, V)
      Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.leftIntermediateImageMap G H).app V).hom.toAlgebra

/-- The actual section module of the constructed first-stage coefficient, localized
at the target prime before selecting any source branch. -/
abbrev firstStageWholeLocalizedCoefficient (n : ℕ) :=
  wholeFiberTorLocalizedSections (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
    (F.leftIntermediateImageMap G H) V p n

variable [Flat f] [Smooth g] [Flat h] [Flat i]

/-- Every actual original first-stage stalk has a Tor bound constructed from
its genuine regular diagonal kernel; no bound or equidimensionality is supplied. -/
theorem firstStageWholeStalk_exists_bound (w : F.leftIntermediateSupportProduct G H)
    (hw : w ∈ (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) :
    ∃ b : ℕ, ∀ n, b ≤ n →
      Subsingleton ((ModuleStalk.functor w).obj (F.firstStageWholeAmbientCoefficient G H V n)) := by
  obtain ⟨s, hs, hker⟩ := exists_regular_kernel_correspondenceFirstDiagonal f g h i
    (F.leftIntermediateSupportInclusion G H w)
  refine ⟨s.length + 1, ?_⟩
  intro n hn
  have hz := ModuleCat.subsingleton_of_isZero
    (isZero_tor_above_length (correspondenceFirstDiagonalInclusion f g h i)
      (F.leftIntermediateSupportInclusion G H w) (F.tripleSupportProductInclusion G H)
      (F.leftIntermediateToTripleSupport G H w)
      (point_eq (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
        (correspondenceFirstDiagonalInclusion f g h i) (F.tripleSupportProductInclusion G H)
        (F.leftIntermediate_ambient_isPullback G H) w)
      s hker hs n (Nat.lt_of_succ_le hn))
  have hq := (closedIntersectionSupportedStalkTorRestrictIso
    (correspondenceFirstDiagonalInclusion f g h i) (F.tripleSupportProductInclusion G H)
    (F.leftIntermediateSupportInclusion G H) (F.leftIntermediateToTripleSupport G H)
    (F.leftIntermediate_ambient_isPullback G H) w n).toLinearEquiv.toEquiv.subsingleton_congr.mpr hz
  exact (wholeFiberTorGluedStalkIso (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
    (F.leftIntermediateImageMap G H) V w hw n).toLinearEquiv.toEquiv.subsingleton_congr.mpr hq

/-- The complete original finite fiber supplies one actual bound for the whole
localized first-stage Tor coefficient, with every pointwise bound proved geometrically. -/
theorem firstStageWholeLocalized_exists_bound :
    ∃ b : ℕ, ∀ n, b ≤ n → Subsingleton (F.firstStageWholeLocalizedCoefficient G H V p n) := by
  have (n : ℕ) : ((Scheme.Modules.restrictFunctor
      ((F.leftIntermediateImageMap G H) ⁻¹ᵁ V).ι).obj
      (F.firstStageWholeAmbientCoefficient G H V n)).IsQuasicoherent :=
    wholeFiberTorGlued_relativeQuasicoherent _ _ _ _ _ _ _ n
  obtain ⟨b, hb⟩ := RelativeFiniteSchemeEuler.originalWholeFamily_exists_bound
    (F.leftIntermediateImageMap G H) V.2 p (F.firstStageWholeAmbientCoefficient G H V)
    (fun x => F.firstStageWholeStalk_exists_bound G H V x.1
      (wholeFiberTor_source_mem (F.leftIntermediateImageMap G H) V p x))
  refine ⟨b, fun n hn => ?_⟩
  exact (wholeFiberTorLocalizedSectionsIso (F.tripleSupportProductInclusion G H)
    (correspondenceFirstDiagonalInclusion f g h i) (F.leftIntermediateSupportInclusion G H)
    (F.leftIntermediateToTripleSupport G H) (F.leftIntermediate_ambient_isPullback G H)
    (F.leftIntermediateImageMap G H) V p n).toLinearEquiv.toEquiv.subsingleton_congr.mp (hb n hn)

/-- The actual whole first-stage Tor coefficient has finite outer nonzero support,
without a finite-length, rank or global uniform smooth-dimension hypothesis. -/
theorem firstStageWholeLocalized_nonzero_finite :
    {n : ℕ | ¬ Subsingleton (F.firstStageWholeLocalizedCoefficient G H V p n)}.Finite := by
  obtain ⟨b, hb⟩ := F.firstStageWholeLocalized_exists_bound G H V p
  apply (Set.finite_Iio b).subset
  intro n hn
  exact Nat.lt_of_not_ge (fun h => hn (hb n h))

end Motivic.FiniteCorrespondenceGenerator
