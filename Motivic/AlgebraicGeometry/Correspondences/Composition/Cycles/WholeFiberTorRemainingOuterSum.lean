/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.WholeFiberTorRemainingProjection
public import Motivic.Aglib.Algebra.Homology.Koszul.DimensionZeroHead

/-!
# Finite outer Euler summation for the actual remaining projection

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
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection
open _root_.AlgebraicGeometry.Scheme.Modules.Pushforward.FiniteEuler
open _root_.HomologicalComplex.ModuleLengthEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)
  (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

/-- The original section map gives the whole localized coefficient action. -/
local instance outerCoordinateAlgebra :
    Algebra Γ(F.leftIntermediateImageProduct G H, V)
      Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) :=
  ((F.leftIntermediateImageMap G H).app V).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Canonical commutative localization structures for actual scalar extension. -/
local instance outerLocalizationRing {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Ring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toRing

/-- Canonical semiring structure for the same actual localization algebra map. -/
local instance outerLocalizationSemiring {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Semiring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toSemiring

variable (s : List ((pullback h h).presheaf.stalk
  (F.leftImageMiddlePair G H (V.2.fromSpec p)))) (n : ℕ)

/-- A genuinely zero whole coefficient gives a zero original pushforward Euler term. -/
theorem firstStagePushforwardRemaining_chainEuler_zero
    [Subsingleton (F.firstStageWholeLocalizedCoefficient G H V p n)]
    (hpush : FiniteHomology (F.firstStagePushforwardRemainingKoszul G H V p s n)) :
    chainEuler (F.firstStagePushforwardRemainingKoszul G H V p s n) hpush = 0 := by
  have hres : Subsingleton
      ((ModuleCat.restrictScalars (algebraMap (Localization.AtPrime p.asIdeal)
        (_root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
          Γ(F.leftIntermediateSupportProduct G H,
            (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p))).obj
        (F.firstStageWholeLocalizedCoefficient G H V p n)) := by
    change Subsingleton (F.firstStageWholeLocalizedCoefficient G H V p n)
    infer_instance
  have : Subsingleton (F.firstStagePushforwardCoefficient G H V p n) := by
    let e := F.firstStageWholePushforwardModuleIso G H V p n
    have hr := e.toLinearEquiv.toEquiv.subsingleton_congr.mp hres
    change Subsingleton (F.firstStagePushforwardCoefficient G H V p n) at hr
    exact hr
  exact _root_.ChainComplex.Koszul.koszulDimension_chainEuler_zero_of_subsingleton _ _ hpush

/-- The same zero whole coefficient vanishes on every original source branch,
through the actual maximal-localization-to-supported-Tor module isomorphism. -/
theorem firstStageSourceRemaining_chainEuler_zero
    [Subsingleton (F.firstStageWholeLocalizedCoefficient G H V p n)]
    (x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = V.2.fromSpec p})
    (hx : FiniteHomology (F.firstStageSourceRemainingKoszul G H V p s x n)) :
    chainEuler (F.firstStageSourceRemainingKoszul G H V p s x n) hx = 0 := by
  obtain ⟨q, rfl⟩ :=
    (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p).surjective x
  let T := _root_.PrimeSpectrum.FiniteFiber.localAlgebra Γ(F.leftIntermediateImageProduct G H, V)
    Γ(F.leftIntermediateSupportProduct G H, (F.leftIntermediateImageMap G H) ⁻¹ᵁ V) p
  have hz := Functor.map_isZero
    (ModuleCat.extendScalars (S := Localization.AtPrime q.asIdeal)
      (algebraMap T (Localization.AtPrime q.asIdeal)))
    (ModuleCat.isZero_of_subsingleton (F.firstStageWholeLocalizedCoefficient G H V p n))
  have : Subsingleton (F.firstStageSupportedStalkTor G H
      (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p q).1 n) :=
    by
      have hr := ModuleCat.subsingleton_of_isZero
        (hz.of_iso (F.firstStageWholeMaximalCoefficientIso G H V p q n).symm)
      change Subsingleton (F.firstStageSupportedStalkTor G H
        (wholeAlgebraFiberEquiv (F.leftIntermediateImageMap G H) V.2 p q).1 n) at hr
      exact hr
  exact _root_.ChainComplex.Koszul.koszulDimension_chainEuler_zero_of_subsingleton _ _ hx

variable [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  [IsNoetherianRing ((F.leftIntermediateImageProduct G H).presheaf.stalk (V.2.fromSpec p))]
  (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
  (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
  (hs : (pullback.diagonal h).ker.stalk
    (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s)

/-- The original pushforward remaining Euler term, with geometric finite-homology evidence. -/
abbrev firstStagePushforwardRemainingEuler (r : ℕ) : ℤ :=
  chainEuler (F.firstStagePushforwardRemainingKoszul G H V p s r)
    (F.firstStagePushforwardRemaining_finiteHomology G H V p s r
      (F.firstStageWholeRemaining_finiteHomology G H V p y hy hp s hs r))

/-- The original supported-Tor remaining Euler term at a full-fiber point. -/
abbrev firstStageSourceRemainingEuler
    (x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = V.2.fromSpec p}) (r : ℕ) : ℤ :=
  chainEuler (F.firstStageSourceRemainingKoszul G H V p s x r)
    (F.firstStageSourceRemaining_finiteHomology G H V p s r
      (F.firstStageWholeRemaining_finiteHomology G H V p y hy hp s hs r) x)

variable [Flat f] [Smooth g] [Flat h] [Flat i]

/-- The genuine whole-fiber Tor bound kills all original pushforward and source
Euler terms simultaneously in high outer degrees; no numerical bound is supplied. -/
theorem firstStageRemainingEuler_exists_bound :
    ∃ b : ℕ, ∀ r, b ≤ r →
      F.firstStagePushforwardRemainingEuler G H V p s y hy hp hs r = 0 ∧
      ∀ x, F.firstStageSourceRemainingEuler G H V p s y hy hp hs x r = 0 := by
  obtain ⟨b, hb⟩ := F.firstStageWholeLocalized_exists_bound G H V p
  refine ⟨b, fun r hr => ?_⟩
  have := hb r hr
  exact ⟨F.firstStagePushforwardRemaining_chainEuler_zero G H V p s r _,
    fun x => F.firstStageSourceRemaining_chainEuler_zero G H V p s r x _⟩

/-- The actual outer pushforward Euler family has finite support. -/
theorem firstStagePushforwardRemainingEuler_finiteSupport :
    Function.HasFiniteSupport (F.firstStagePushforwardRemainingEuler G H V p s y hy hp hs) := by
  obtain ⟨b, hb⟩ := F.firstStageRemainingEuler_exists_bound G H V p s y hy hp hs
  apply (Set.finite_Iio b).subset
  intro r hr
  exact Nat.lt_of_not_ge (fun h => hr (hb r h).1)

/-- Every actual original source Euler family has finite support with the same whole-fiber bound. -/
theorem firstStageSourceRemainingEuler_finiteSupport
    (x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = V.2.fromSpec p}) :
    Function.HasFiniteSupport (F.firstStageSourceRemainingEuler G H V p s y hy hp hs x) := by
  obtain ⟨b, hb⟩ := F.firstStageRemainingEuler_exists_bound G H V p s y hy hp hs
  apply (Set.finite_Iio b).subset
  intro r hr
  exact Nat.lt_of_not_ge (fun h => hr ((hb r h).2 x))

/-- Summing the genuine per-degree projection over its derived finite outer support
preserves the original full fiber and actual scheme residue degrees. -/
theorem firstStageRemainingOuterProjectionEuler :
    (∑ᶠ r : ℕ, (-1 : ℤ) ^ r *
      F.firstStagePushforwardRemainingEuler G H V p s y hy hp hs r) =
    ∑ᶠ x : {w : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H w = V.2.fromSpec p},
      ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) *
        ∑ᶠ r : ℕ, (-1 : ℤ) ^ r *
          F.firstStageSourceRemainingEuler G H V p s y hy hp hs x r := by
  classical
  let P := F.firstStagePushforwardRemainingEuler G H V p s y hy hp hs
  let Q := F.firstStageSourceRemainingEuler G H V p s y hy hp hs
  let A := {w : F.leftIntermediateSupportProduct G H //
    F.leftIntermediateImageMap G H w = V.2.fromSpec p}
  let weight : A → ℤ := fun x => (F.leftIntermediateImageMap G H).residueDegree x.1
  have : Finite A := originalSourceFiber_finite (F.leftIntermediateImageMap G H) V.2 p
  let : Fintype A := Fintype.ofFinite A
  obtain ⟨b, hb⟩ := F.firstStageRemainingEuler_exists_bound G H V p s y hy hp hs
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
    F.firstStageRemainingProjectionEuler G H V p y hy hp s hs r
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
