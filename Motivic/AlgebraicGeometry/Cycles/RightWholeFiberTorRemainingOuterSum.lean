/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.RightWholeFiberTorRemainingProjection
public import Motivic.Algebra.Homology.KoszulDimensionZeroHead

/-!
# Finite outer Euler summation for the actual right remaining projection

The genuine whole-coefficient Tor bound forces both the original pushforward
and every original source remaining Euler characteristic to vanish in high
outer degrees. The per-degree projection formula can therefore be summed with
its actual outer signs. This graded homology sum is not identified here with
the true iterated complex.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator

open Intersection FiniteSchemeEuler LengthEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (V : (F.rightIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.rightIntermediateImageProduct G H, V))

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

/-- The original section map gives the whole localized coefficient action. -/
local instance rightOuterCoordinateAlgebra :
    Algebra Γ(F.rightIntermediateImageProduct G H, V)
      Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.rightIntermediateImageMap G H).app V).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Canonical commutative localization structures for actual scalar extension. -/
local instance rightOuterLocalizationRing {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Ring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toRing

/-- Canonical semiring structure for the same actual localization algebra map. -/
local instance rightOuterLocalizationSemiring {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Semiring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toSemiring

variable (s : List ((pullback g g).presheaf.stalk
  (F.rightImageMiddlePair G H (V.2.fromSpec p)))) (n : ℕ)

/-- A genuinely zero whole coefficient gives a zero original pushforward Euler term. -/
theorem rightFirstStagePushforwardRemaining_chainEuler_zero
    [Subsingleton (F.rightFirstStageWholeLocalizedCoefficient G H V p n)]
    (hpush : FiniteHomology (F.rightFirstStagePushforwardRemainingKoszul G H V p s n)) :
    chainEuler (F.rightFirstStagePushforwardRemainingKoszul G H V p s n) hpush = 0 := by
  have hres : Subsingleton
      ((ModuleCat.restrictScalars (algebraMap (Localization.AtPrime p.asIdeal)
        (FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
          Γ(F.rightIntermediateSupportProduct G H,
            (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p))).obj
        (F.rightFirstStageWholeLocalizedCoefficient G H V p n)) := by
    change Subsingleton (F.rightFirstStageWholeLocalizedCoefficient G H V p n)
    infer_instance
  have : Subsingleton (F.rightFirstStagePushforwardCoefficient G H V p n) := by
    let e := F.rightFirstStageWholePushforwardModuleIso G H V p n
    have hr := e.toLinearEquiv.toEquiv.subsingleton_congr.mp hres
    change Subsingleton (F.rightFirstStagePushforwardCoefficient G H V p n) at hr
    exact hr
  exact Koszul.koszulDimension_chainEuler_zero_of_subsingleton _ _ hpush

/-- The same zero whole coefficient vanishes on every original source branch,
through the actual maximal-localization-to-supported-Tor module isomorphism. -/
theorem rightFirstStageSourceRemaining_chainEuler_zero
    [Subsingleton (F.rightFirstStageWholeLocalizedCoefficient G H V p n)]
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p})
    (hx : FiniteHomology (F.rightFirstStageSourceRemainingKoszul G H V p s x n)) :
    chainEuler (F.rightFirstStageSourceRemainingKoszul G H V p s x n) hx = 0 := by
  obtain ⟨q, rfl⟩ :=
    (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p).surjective x
  let T := FiniteFiber.localAlgebra Γ(F.rightIntermediateImageProduct G H, V)
    Γ(F.rightIntermediateSupportProduct G H, (F.rightIntermediateImageMap G H) ⁻¹ᵁ V) p
  have hz := Functor.map_isZero
    (ModuleCat.extendScalars (S := Localization.AtPrime q.asIdeal)
      (algebraMap T (Localization.AtPrime q.asIdeal)))
    (ModuleCat.isZero_of_subsingleton (F.rightFirstStageWholeLocalizedCoefficient G H V p n))
  have : Subsingleton (F.rightFirstStageSupportedStalkTor G H
      (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q).1 n) :=
    by
      have hr := ModuleCat.subsingleton_of_isZero
        (hz.of_iso (F.rightFirstStageWholeMaximalCoefficientIso G H V p q n).symm)
      change Subsingleton (F.rightFirstStageSupportedStalkTor G H
        (wholeAlgebraFiberEquiv (F.rightIntermediateImageMap G H) V.2 p q).1 n) at hr
      exact hr
  exact Koszul.koszulDimension_chainEuler_zero_of_subsingleton _ _ hx

variable [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  [IsNoetherianRing ((F.rightIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))]
  (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
  (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
  (hs : (pullback.diagonal g).ker.stalk
    (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s)

/-- The original pushforward remaining Euler term, with geometric finite-homology evidence. -/
abbrev rightFirstStagePushforwardRemainingEuler (r : ℕ) : ℤ :=
  chainEuler (F.rightFirstStagePushforwardRemainingKoszul G H V p s r)
    (F.rightFirstStagePushforwardRemaining_finiteHomology G H V p s r
      (F.rightFirstStageWholeRemaining_finiteHomology G H V p y hy hp s hs r))

/-- The original supported-Tor remaining Euler term at a full-fiber point. -/
abbrev rightFirstStageSourceRemainingEuler
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p}) (r : ℕ) : ℤ :=
  chainEuler (F.rightFirstStageSourceRemainingKoszul G H V p s x r)
    (F.rightFirstStageSourceRemaining_finiteHomology G H V p s r
      (F.rightFirstStageWholeRemaining_finiteHomology G H V p y hy hp s hs r) x)

variable [Flat f] [Flat g] [Smooth h] [Flat i]

/-- The genuine whole-fiber Tor bound kills all original pushforward and source
Euler terms simultaneously in high outer degrees; no numerical bound is supplied. -/
theorem rightFirstStageRemainingEuler_exists_bound :
    ∃ b : ℕ, ∀ r, b ≤ r →
      F.rightFirstStagePushforwardRemainingEuler G H V p s y hy hp hs r = 0 ∧
      ∀ x, F.rightFirstStageSourceRemainingEuler G H V p s y hy hp hs x r = 0 := by
  obtain ⟨b, hb⟩ := F.rightFirstStageWholeLocalized_exists_bound G H V p
  refine ⟨b, fun r hr => ?_⟩
  have := hb r hr
  exact ⟨F.rightFirstStagePushforwardRemaining_chainEuler_zero G H V p s r _,
    fun x => F.rightFirstStageSourceRemaining_chainEuler_zero G H V p s r x _⟩

/-- The actual outer pushforward Euler family has finite support. -/
theorem rightFirstStagePushforwardRemainingEuler_finiteSupport :
    Function.HasFiniteSupport
      (F.rightFirstStagePushforwardRemainingEuler G H V p s y hy hp hs) := by
  obtain ⟨b, hb⟩ := F.rightFirstStageRemainingEuler_exists_bound G H V p s y hy hp hs
  apply (Set.finite_Iio b).subset
  intro r hr
  exact Nat.lt_of_not_ge (fun h => hr (hb r h).1)

/-- Every actual original source Euler family has finite support with the same whole-fiber bound. -/
theorem rightFirstStageSourceRemainingEuler_finiteSupport
    (x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p}) :
    Function.HasFiniteSupport (F.rightFirstStageSourceRemainingEuler G H V p s y hy hp hs x) := by
  obtain ⟨b, hb⟩ := F.rightFirstStageRemainingEuler_exists_bound G H V p s y hy hp hs
  apply (Set.finite_Iio b).subset
  intro r hr
  exact Nat.lt_of_not_ge (fun h => hr ((hb r h).2 x))

/-- Summing the genuine per-degree projection over its derived finite outer support
preserves the original full fiber and actual scheme residue degrees. -/
theorem rightFirstStageRemainingOuterProjectionEuler :
    (∑ᶠ r : ℕ, (-1 : ℤ) ^ r *
      F.rightFirstStagePushforwardRemainingEuler G H V p s y hy hp hs r) =
    ∑ᶠ x : {w : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H w = V.2.fromSpec p},
      ((F.rightIntermediateImageMap G H).residueDegree x.1 : ℤ) *
        ∑ᶠ r : ℕ, (-1 : ℤ) ^ r *
          F.rightFirstStageSourceRemainingEuler G H V p s y hy hp hs x r := by
  classical
  let P := F.rightFirstStagePushforwardRemainingEuler G H V p s y hy hp hs
  let Q := F.rightFirstStageSourceRemainingEuler G H V p s y hy hp hs
  let A := {w : F.rightIntermediateSupportProduct G H //
    F.rightIntermediateImageMap G H w = V.2.fromSpec p}
  let weight : A → ℤ := fun x => (F.rightIntermediateImageMap G H).residueDegree x.1
  have : Finite A := originalSourceFiber_finite (F.rightIntermediateImageMap G H) V.2 p
  let : Fintype A := Fintype.ofFinite A
  obtain ⟨b, hb⟩ := F.rightFirstStageRemainingEuler_exists_bound G H V p s y hy hp hs
  have hP : (∑ᶠ r : ℕ, (-1 : ℤ) ^ r * P r) =
      ∑ r ∈ Finset.range b, (-1 : ℤ) ^ r * P r := by
    apply finsum_eq_sum_of_support_subset
    intro r hr
    apply Finset.mem_range.mpr
    exact Nat.lt_of_not_ge (fun h => hr (by
      have hz : P r = 0 := (hb r h).1
      exact (congrArg (fun v : ℤ => (-1 : ℤ) ^ r * v) hz).trans (mul_zero _)))
  have hQ (x : A) : (∑ᶠ r : ℕ, (-1 : ℤ) ^ r * Q x r) =
      ∑ r ∈ Finset.range b, (-1 : ℤ) ^ r * Q x r := by
    apply finsum_eq_sum_of_support_subset
    intro r hr
    apply Finset.mem_range.mpr
    exact Nat.lt_of_not_ge (fun h => hr (by
      have hz : Q x r = 0 := (hb r h).2 x
      exact (congrArg (fun v : ℤ => (-1 : ℤ) ^ r * v) hz).trans (mul_zero _)))
  have hproj (r : ℕ) : P r = ∑ᶠ x : A, weight x * Q x r :=
    F.rightFirstStageRemainingProjectionEuler G H V p y hy hp s hs r
  change (∑ᶠ r : ℕ, (-1 : ℤ) ^ r * P r) =
    ∑ᶠ x : A, weight x * ∑ᶠ r : ℕ, (-1 : ℤ) ^ r * Q x r
  calc
    _ = ∑ r ∈ Finset.range b, (-1 : ℤ) ^ r * P r := hP
    _ = ∑ r ∈ Finset.range b, ∑ x : A, (-1 : ℤ) ^ r * (weight x * Q x r) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [hproj, finsum_eq_sum_of_fintype, Finset.mul_sum]
    _ = ∑ x : A, weight x * ∑ r ∈ Finset.range b, (-1 : ℤ) ^ r * Q x r := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      rw [finsum_eq_sum_of_fintype]
      apply Finset.sum_congr rfl
      intro x _
      rw [hQ]

end Motivic.FiniteCorrespondenceGenerator
