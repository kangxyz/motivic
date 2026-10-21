/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.RightWholeFiberTorSourceTotal
public import Motivic.Aglib.AlgebraicGeometry.Cycles.GenericFinitePushforward
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.TorCycle
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Noetherian
public import Motivic.AlgebraicGeometry.Correspondences.Noetherian

/-!
# Right whole-fiber Euler sums as actual finite-pushforward cycle coefficients

The genuine Cartesian finite map from triple incidence to right image incidence
has the same residue degree as the original image-product map at the corresponding
point. Its whole fiber over a generic target point is reindexed by actual generic
triple points. The signed remaining Euler sum is then the point coefficient of
the actual pushforward of the canonical triple-incidence Tor cycle.

Every colliding source generic point retains its own signed coefficient and
literal residue degree. Genericity is only reflected along the finite map; there
is no assertion that every source generic point maps to a generic target point.
No off-generic vanishing, global generic-cycle replacement, iterated composition
identification, or correspondence associativity is concluded.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

section Schemes

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The actual commuting square and the two genuine closed immersions identify
residue degrees, with no replacement by a pair-projection degree. -/
theorem tripleToRightImageIncidence_residueDegree [IsSeparated g]
    (w : F.tripleIncidence G H) :
    (F.tripleToRightImageIncidence G H).residueDegree w =
      (F.rightIntermediateImageMap G H).residueDegree
        (F.tripleIncidenceToRightSupportProduct G H w) := by
  have he := congrArg (fun m => m.residueDegree w)
    (F.tripleToRightImageIncidence_square G H)
  simpa only [residueDegree_comp, residueDegree_of_surjectiveOnStalks,
    one_mul, mul_one] using he

/-- The entire original image-product fiber over a generic final incidence point
is exactly the generic triple-incidence fiber of the genuine finite map. -/
def rightImageIncidenceGenericFiberEquiv [IsSeparated g] [IsSeparated i]
    (y : genericPoints (F.rightImageIncidence G H)) :
    {x : F.rightIntermediateSupportProduct G H //
      F.rightIntermediateImageMap G H x = F.rightImageIncidenceInclusion G H y.1} ≃
      {w : genericPoints (F.tripleIncidence G H) //
        F.tripleToRightImageIncidence G H w.1 = y.1} :=
  (F.rightImageIncidenceFiberEquiv G H y.1).symm.trans
    (genericFiberEquiv (F.tripleToRightImageIncidence G H) y)

/-- Reindexing a generic triple branch retains its literal original support point. -/
@[simp] theorem rightImageIncidenceGenericFiberEquiv_symm_apply_val
    [IsSeparated g] [IsSeparated i]
    (y : genericPoints (F.rightImageIncidence G H))
    (w : {w : genericPoints (F.tripleIncidence G H) //
      F.tripleToRightImageIncidence G H w.1 = y.1}) :
    ((F.rightImageIncidenceGenericFiberEquiv G H y).symm w).1 =
      F.tripleIncidenceToRightSupportProduct G H w.1.1 := rfl

end Schemes

section SmoothSite

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The actual pushed triple Tor cycle sums every source generic point mapping to
the specified target, without any generic-preservation hypothesis on the map. -/
theorem rightImageIncidenceTorCycleCoefficient_eq_finsum
    (y : F.rightImageIncidence G H) :
    IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
          (F.tripleIncidenceTorCycle k G H)) y =
      ∑ᶠ w : {w : genericPoints (F.tripleIncidence G H) //
        F.tripleToRightImageIncidence G H w.1 = y},
        F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w.1 *
          ((F.tripleToRightImageIncidence G H).residueDegree w.1.1 : ℤ) := by
  classical
  let := IntegralCycle.genericPointFintype (F.tripleIncidence G H)
  rw [tripleIncidenceTorCycle,
    IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  unfold IntegralCycle.genericPushforwardCoefficient
  rw [finsum_subtype_eq_finsum_cond
    (f := fun w : genericPoints (F.tripleIncidence G H) =>
      F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w *
        ((F.tripleToRightImageIncidence G H).residueDegree w.1 : ℤ))
    (fun w => F.tripleToRightImageIncidence G H w.1 = y)]
  simp only [finsum_eq_if, finsum_eq_sum_of_fintype]

/-- The local Noetherian instance used in this module. -/
local instance cyclesRightWholeFiberTorCycleCoefficientLocallyNoetherian : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
    X.hom Y.hom Z.hom W.hom

/-- The local Noetherian instance used in this module. -/
local instance cyclesRightWholeFiberTorCycleCoefficientRightImageLocallyNoetherian
    : IsLocallyNoetherian (F.rightIntermediateImageProduct G H) := by
  have : IsLocallyNoetherian Y.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) Y.hom
  have : IsLocallyNoetherian (pullback Y.hom W.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Y.left) (pullback.fst Y.hom W.hom)
  have : IsLocallyNoetherian (G.incidenceMap H).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback Y.hom W.hom)
      (G.incidenceMap H).imageι
  exact LocallyOfFiniteType.isLocallyNoetherian (Y := (G.incidenceMap H).image)
    (pullback.snd (F.targetProjection ≫ Y.hom)
      ((G.incidenceMap H).imageι ≫ pullback.fst Y.hom W.hom ≫ Y.hom))

/-- At a generic right final-incidence point, the signed whole-fiber remaining
Euler sum is the coefficient of the actual finite-pushforward triple Tor cycle.
The fixed image list, every source collision, and all residue degrees are retained. -/
theorem rightFirstStageRemainingEuler_eq_finitePushforward_tripleTorCycle
    (V : (F.rightIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H))
    (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))))
    (hs : RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal Y.hom).ker.stalk
      (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.rightFirstStagePushforwardRemainingEuler
        (S := Spec (.of k)) G H V p s y hy hp hker n) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
          (F.tripleIncidenceTorCycle k G H)) y := by
  classical
  let A := {x : F.rightIntermediateSupportProduct G H //
    F.rightIntermediateImageMap G H x = V.2.fromSpec p}
  let B := {w : genericPoints (F.tripleIncidence G H) //
    F.tripleToRightImageIncidence G H w.1 = y}
  let e : B ≃ A :=
    (F.rightImageIncidenceGenericFiberEquiv G H ⟨y, hy⟩).symm.trans
      (Equiv.subtypeEquivRight (fun _ => by rw [hp]))
  have he (w : B) : (e w).1 = F.tripleIncidenceToRightSupportProduct G H w.1.1 := rfl
  let a : A → ℤ := fun x => ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
    F.rightFirstStageSourceRemainingEuler (S := Spec (.of k)) G H V p s y hy hp hker x n
  have hcoeff (w : B) : a (e w) =
      F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w.1 := by
    have hw : F.rightIntermediateImageMap G H
        (F.tripleIncidenceToRightSupportProduct G H w.1.1) = V.2.fromSpec p :=
      (congrArg (F.rightIntermediateImageMap G H) (he w)).symm.trans (e w).2
    have he' : e w = ⟨_, hw⟩ := Subtype.ext (he w)
    rw [he']
    exact F.rightFirstStageSourceRemainingEuler_eq_tripleCoefficient
      (S := Spec (.of k)) G H w.1.1 V p y hy hp hw w.1.2 s hs hker
  calc
    _ = ∑ᶠ x : A, ((F.rightIntermediateImageMap G H).residueDegree x.1 : ℤ) * a x :=
      F.rightFirstStageRemainingOuterProjectionEuler
        (S := Spec (.of k)) G H V p s y hy hp hker
    _ = ∑ᶠ w : B,
        ((F.rightIntermediateImageMap G H).residueDegree (e w).1 : ℤ) * a (e w) :=
      (finsum_comp_equiv e (f := fun x =>
        ((F.rightIntermediateImageMap G H).residueDegree x.1 : ℤ) * a x)).symm
    _ = ∑ᶠ w : B, F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w.1 *
        ((F.tripleToRightImageIncidence G H).residueDegree w.1.1 : ℤ) := by
      apply finsum_congr
      intro w
      rw [hcoeff w, he w, ← F.tripleToRightImageIncidence_residueDegree G H w.1.1]
      exact mul_comm _ _
    _ = _ := (F.rightImageIncidenceTorCycleCoefficient_eq_finsum k G H y).symm

/-- A generic final-incidence point supplies its own chart and one regular list
for the actual finite-pushforward cycle coefficient formula. -/
theorem exists_rightFirstStageRemainingEuler_finitePushforward_chart
    (y : F.rightImageIncidence G H) (hy : y ∈ genericPoints (F.rightImageIncidence G H)) :
    ∃ (V : (F.rightIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.rightIntermediateImageProduct G H, V))
      (hp : V.2.fromSpec p = F.rightImageIncidenceInclusion G H y)
      (s : List ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))))
      (_hs : RingTheory.Sequence.IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p))) s)
      (hker : (pullback.diagonal Y.hom).ker.stalk
        (F.rightImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s),
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        F.rightFirstStagePushforwardRemainingEuler
          (S := Spec (.of k)) G H V p s y hy hp hker n) =
        IntegralCycle.toPoints
          (IntegralCycle.finitePushforward (F.tripleToRightImageIncidence G H)
            (F.tripleIncidenceTorCycle k G H)) y := by
  obtain ⟨V, p, hp, s, hs, hker, _⟩ :=
    F.exists_rightFirstStageWholeRemaining_chart (S := Spec (.of k)) G H y hy
  exact ⟨V, p, hp, s, hs, hker,
    F.rightFirstStageRemainingEuler_eq_finitePushforward_tripleTorCycle
      k G H V p y hy hp s hs hker⟩

end SmoothSite

end Motivic.FiniteCorrespondenceGenerator
