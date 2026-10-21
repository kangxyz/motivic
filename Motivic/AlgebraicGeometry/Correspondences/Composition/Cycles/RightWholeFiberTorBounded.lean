/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Intersection.Tor.WholeFiber.Finite
public import Motivic.Aglib.AlgebraicGeometry.Intersection.Triple.DiagonalRegularity
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.Right.DiagonalAmbient

/-!
# Actual right-first whole Tor coefficients vanish in high degrees

The original smooth Z diagonal supplies a regular kernel list at every
actual right-first-stage source point. Genuine Tor vanishing above that list length
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

namespace Motivic
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

/-- At every original second-diagonal point, the smooth Z diagonal and the
actual flat outer factors supply a regular kernel in the six-factor stalk. -/
theorem exists_regular_kernel_correspondenceSecondAmbient
    {S X Y Z W : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (h : Z ⟶ S) (i : W ⟶ S)
    [Flat f] [Flat g] [Smooth h] [IsSeparated h] [Flat i]
    (q : correspondenceSecondDiagonalAmbient f g h i) :
    ∃ s : List ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
        (correspondenceSecondAmbientInclusion f g h i q)),
      RingTheory.Sequence.IsRegular ((correspondenceSixfoldAmbient f g h i).presheaf.stalk
        (correspondenceSecondAmbientInclusion f g h i q)) s ∧
      RingHom.ker ((correspondenceSecondAmbientInclusion f g h i).stalkMap q).hom =
        Ideal.ofList s :=
  Diagonal.exists_regular_kernel_of_flat_isPullback
    (correspondenceSixfoldSecondDiagonal_isPullback f g h i) q
    (Diagonal.exists_regular_kernel_of_smooth h _)

end Motivic

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward
open _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The separatedness instance used in this module. -/
local instance cyclesRightWholeFiberTorBoundedSeparated
    : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

/-- The actual right-first-stage compatible-sections equalizer on its original support scheme. -/
abbrev rightFirstStageWholeAmbientCoefficient
    (V : (F.rightIntermediateImageProduct G H).affineOpens) (n : ℕ) :=
  closedIntersectionTorGlued (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
    (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
    (wholeFiberTorAmbientFamily (F.tripleSupportProductInclusion G H)
      (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
      (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
      (F.rightIntermediateImageMap G H) V) n

variable (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

/-- The actual image-product map supplies the original whole coordinate algebra action. -/
local instance rightFirstStageWholeCoordinateAlgebra :
    Algebra Γ(F.rightIntermediateImageProduct G H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.rightIntermediateImageMap G H).app V).hom.toAlgebra

/-- The actual section module of the constructed right-first-stage coefficient, localized
at the target prime before selecting any source branch. -/
abbrev rightFirstStageWholeLocalizedCoefficient (n : ℕ) :=
  wholeFiberTorLocalizedSections (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
    (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
    (F.rightIntermediateImageMap G H) V p n

variable [Flat f] [Flat g] [Smooth h] [Flat i]

/-- Every actual original right-first-stage stalk has a Tor bound constructed from
its genuine regular diagonal kernel; no bound or equidimensionality is supplied. -/
theorem rightFirstStageWholeStalk_exists_bound (w : F.rightIntermediateSupportProduct G H)
    (hw : w ∈ (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) :
    ∃ b : ℕ, ∀ n, b ≤ n →
      Subsingleton ((Stalk.functor w).obj
        (F.rightFirstStageWholeAmbientCoefficient G H V n)) := by
  obtain ⟨s, hs, hker⟩ := exists_regular_kernel_correspondenceSecondAmbient f g h i
    (F.rightIntermediateSupportInclusion G H w)
  refine ⟨s.length + 1, ?_⟩
  intro n hn
  have hz := ModuleCat.subsingleton_of_isZero
    (isZero_tor_above_length (correspondenceSecondAmbientInclusion f g h i)
      (F.rightIntermediateSupportInclusion G H w) (F.tripleSupportProductInclusion G H)
      (F.rightIntermediateToTripleSupport G H w)
      (point_eq (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
        (correspondenceSecondAmbientInclusion f g h i) (F.tripleSupportProductInclusion G H)
        (F.rightIntermediate_ambient_isPullback G H) w)
      s hker hs n (Nat.lt_of_succ_le hn))
  have hq := ((closedIntersectionSupportedStalkTorRestrictIso
    (correspondenceSecondAmbientInclusion f g h i) (F.tripleSupportProductInclusion G H)
    (F.rightIntermediateSupportInclusion G H) (F.rightIntermediateToTripleSupport G H)
    (F.rightIntermediate_ambient_isPullback G H) w n).toLinearEquiv.toEquiv.subsingleton_congr).mpr
      hz
  exact (wholeFiberTorGluedStalkIso (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
    (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
    (F.rightIntermediateImageMap G H) V w hw n).toLinearEquiv.toEquiv.subsingleton_congr.mpr hq

/-- The complete original finite fiber supplies one actual bound for the whole
localized right-first-stage Tor coefficient, with every pointwise bound proved geometrically. -/
theorem rightFirstStageWholeLocalized_exists_bound :
    ∃ b : ℕ, ∀ n, b ≤ n → Subsingleton (F.rightFirstStageWholeLocalizedCoefficient G H V p n) := by
  have (n : ℕ) : ((Scheme.Modules.restrictFunctor
      ((F.rightIntermediateImageMap G H) ⁻¹ᵁ V).ι).obj
      (F.rightFirstStageWholeAmbientCoefficient G H V n)).IsQuasicoherent :=
    wholeFiberTorGlued_relativeQuasicoherent _ _ _ _ _ _ _ n
  obtain ⟨b, hb⟩ := RelativeFiniteEuler.originalWholeFamily_exists_bound
    (F.rightIntermediateImageMap G H) V.2 p (F.rightFirstStageWholeAmbientCoefficient G H V)
    (fun x => F.rightFirstStageWholeStalk_exists_bound G H V x.1
      (wholeFiberTor_source_mem (F.rightIntermediateImageMap G H) V p x))
  refine ⟨b, fun n hn => ?_⟩
  exact (wholeFiberTorLocalizedSectionsIso (F.tripleSupportProductInclusion G H)
    (correspondenceSecondAmbientInclusion f g h i) (F.rightIntermediateSupportInclusion G H)
    (F.rightIntermediateToTripleSupport G H) (F.rightIntermediate_ambient_isPullback G H)
    (F.rightIntermediateImageMap G H) V p n).toLinearEquiv.toEquiv.subsingleton_congr.mp (hb n hn)

/-- The actual whole right-first-stage Tor coefficient has finite outer nonzero support,
without a finite-length, rank or global uniform smooth-dimension hypothesis. -/
theorem rightFirstStageWholeLocalized_nonzero_finite :
    {n : ℕ | ¬ Subsingleton (F.rightFirstStageWholeLocalizedCoefficient G H V p n)}.Finite := by
  obtain ⟨b, hb⟩ := F.rightFirstStageWholeLocalized_exists_bound G H V p
  apply (Set.finite_Iio b).subset
  intro n hn
  exact Nat.lt_of_not_ge (fun h => hn (hb n h))

end Motivic.FiniteCorrespondenceGenerator
