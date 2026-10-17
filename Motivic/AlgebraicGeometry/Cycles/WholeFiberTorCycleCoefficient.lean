/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.WholeFiberTorSourceTotal
public import Motivic.AlgebraicGeometry.Cycles.GenericFinitePushforward
public import Motivic.AlgebraicGeometry.Correspondences.TripleTorCycle
public import Motivic.AlgebraicGeometry.SmoothSiteNoetherian

/-!
# Left whole-fiber Euler sums as actual finite-pushforward cycle coefficients

The genuine Cartesian finite map from triple incidence to left image incidence
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

section Schemes

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

/-- The actual commuting square and the two genuine closed immersions identify
residue degrees, with no replacement by a pair-projection degree. -/
theorem tripleToLeftImageIncidence_residueDegree [IsSeparated h]
    (w : F.tripleIncidence G H) :
    (F.tripleToLeftImageIncidence G H).residueDegree w =
      (F.leftIntermediateImageMap G H).residueDegree
        (F.tripleIncidenceToLeftSupportProduct G H w) := by
  have he := congrArg (fun m => m.residueDegree w)
    (F.tripleToLeftImageIncidence_square G H)
  have hleft := residueDegree_comp (F.tripleToLeftImageIncidence G H)
    (F.leftImageIncidenceInclusion G H) w
  have hright := residueDegree_comp (F.tripleIncidenceToLeftSupportProduct G H)
    (F.leftIntermediateImageMap G H) w
  have htarget := residueDegree_of_surjectiveOnStalks (F.leftImageIncidenceInclusion G H)
    (F.tripleToLeftImageIncidence G H w)
  have hsource := residueDegree_of_surjectiveOnStalks
    (F.tripleIncidenceToLeftSupportProduct G H) w
  rw [hleft, hright, htarget, hsource, one_mul, mul_one] at he
  exact he

/-- The entire original image-product fiber over a generic final incidence point
is exactly the generic triple-incidence fiber of the genuine finite map. -/
def leftImageIncidenceGenericFiberEquiv [IsSeparated h]
    (y : genericPoints (F.leftImageIncidence G H)) :
    {x : F.leftIntermediateSupportProduct G H //
      F.leftIntermediateImageMap G H x = F.leftImageIncidenceInclusion G H y.1} ≃
      {w : genericPoints (F.tripleIncidence G H) //
        F.tripleToLeftImageIncidence G H w.1 = y.1} :=
  (F.leftImageIncidenceFiberEquiv G H y.1).symm.trans
    (genericFiberEquiv (F.tripleToLeftImageIncidence G H) y)

/-- Reindexing a generic triple branch retains its literal original support point. -/
@[simp] theorem leftImageIncidenceGenericFiberEquiv_symm_apply_val
    [IsSeparated h]
    (y : genericPoints (F.leftImageIncidence G H))
    (w : {w : genericPoints (F.tripleIncidence G H) //
      F.tripleToLeftImageIncidence G H w.1 = y.1}) :
    ((F.leftImageIncidenceGenericFiberEquiv G H y).symm w).1 =
      F.tripleIncidenceToLeftSupportProduct G H w.1.1 := rfl

end Schemes

section SmoothSite

variable (k : Type u) [Field k] {X Y Z W : SmoothSite (Spec (.of k))}
  (F : FiniteCorrespondenceGenerator X.hom Y.hom)
  (G : FiniteCorrespondenceGenerator Y.hom Z.hom)
  (H : FiniteCorrespondenceGenerator Z.hom W.hom)

/-- The actual pushed triple Tor cycle sums every source generic point mapping to
the specified target, without any generic-preservation hypothesis on the map. -/
theorem leftImageIncidenceTorCycleCoefficient_eq_finsum
    (y : F.leftImageIncidence G H) :
    IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.tripleToLeftImageIncidence G H)
          (F.tripleIncidenceTorCycle k G H)) y =
      ∑ᶠ w : {w : genericPoints (F.tripleIncidence G H) //
        F.tripleToLeftImageIncidence G H w.1 = y},
        F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w.1 *
          ((F.tripleToLeftImageIncidence G H).residueDegree w.1.1 : ℤ) := by
  classical
  let instWholeFiberCoefficientGenerics :=
    IntegralCycle.genericPointFintype (F.tripleIncidence G H)
  rw [tripleIncidenceTorCycle,
    IntegralCycle.toPoints_finitePushforward_ofGenericCoefficients_apply]
  unfold IntegralCycle.genericPushforwardCoefficient
  rw [finsum_subtype_eq_finsum_cond
    (f := fun w : genericPoints (F.tripleIncidence G H) =>
      F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w *
        ((F.tripleToLeftImageIncidence G H).residueDegree w.1 : ℤ))
    (fun w => F.tripleToLeftImageIncidence G H w.1 = y)]
  simp only [finsum_eq_if, finsum_eq_sum_of_fintype]

local instance wholeFiberCoefficientSixfoldNoetherian : IsLocallyNoetherian
    (correspondenceSixfoldAmbient X.hom Y.hom Z.hom W.hom) :=
  isLocallyNoetherian_correspondenceSixfoldAmbient (S := Spec (.of k))
    X.hom Y.hom Z.hom W.hom

local instance wholeFiberCoefficientImageNoetherian :
    IsLocallyNoetherian (F.leftIntermediateImageProduct G H) := by
  let instWholeFiberCoefficientSourceNoetherian : IsLocallyNoetherian X.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := Spec (.of k)) X.hom
  let instWholeFiberCoefficientPairNoetherian :
      IsLocallyNoetherian (pullback X.hom Z.hom) :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := X.left) (pullback.fst X.hom Z.hom)
  let instWholeFiberCoefficientImageNoetherian :
      IsLocallyNoetherian (F.incidenceMap G).image :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := pullback X.hom Z.hom)
      (F.incidenceMap G).imageι
  exact LocallyOfFiniteType.isLocallyNoetherian (Y := (F.incidenceMap G).image)
    (pullback.fst ((F.incidenceMap G).imageι ≫ pullback.snd X.hom Z.hom ≫ Z.hom)
      (H.projection ≫ Z.hom))

/-- At a generic left final-incidence point, the signed whole-fiber remaining
Euler sum is the coefficient of the actual finite-pushforward triple Tor cycle.
The fixed image list, every source collision, and all residue degrees are retained. -/
theorem firstStageRemainingEuler_eq_finitePushforward_tripleTorCycle
    (V : (F.leftIntermediateImageProduct G H).affineOpens)
    (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H))
    (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
    (s : List ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (hs : RingTheory.Sequence.IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))) s)
    (hker : (pullback.diagonal Z.hom).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) :
    (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
      F.firstStagePushforwardRemainingEuler
        (S := Spec (.of k)) G H V p s y hy hp hker n) =
      IntegralCycle.toPoints
        (IntegralCycle.finitePushforward (F.tripleToLeftImageIncidence G H)
          (F.tripleIncidenceTorCycle k G H)) y := by
  classical
  let A := {x : F.leftIntermediateSupportProduct G H //
    F.leftIntermediateImageMap G H x = V.2.fromSpec p}
  let B := {w : genericPoints (F.tripleIncidence G H) //
    F.tripleToLeftImageIncidence G H w.1 = y}
  let e : B ≃ A :=
    (F.leftImageIncidenceGenericFiberEquiv G H ⟨y, hy⟩).symm.trans
      (Equiv.subtypeEquivRight (fun _ => by rw [hp]))
  have he (w : B) : (e w).1 = F.tripleIncidenceToLeftSupportProduct G H w.1.1 := rfl
  let a : A → ℤ := fun x => ∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
    F.firstStageSourceRemainingEuler (S := Spec (.of k)) G H V p s y hy hp hker x n
  have hcoeff (w : B) : a (e w) =
      F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w.1 := by
    have hw : F.leftIntermediateImageMap G H
        (F.tripleIncidenceToLeftSupportProduct G H w.1.1) = V.2.fromSpec p :=
      (congrArg (F.leftIntermediateImageMap G H) (he w)).symm.trans (e w).2
    have he' : e w = ⟨_, hw⟩ := Subtype.ext (he w)
    rw [he']
    exact F.firstStageSourceRemainingEuler_eq_tripleCoefficient
      (S := Spec (.of k)) G H w.1.1 V p y hy hp hw w.1.2 s hs hker
  calc
    _ = ∑ᶠ x : A, ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) * a x :=
      F.firstStageRemainingOuterProjectionEuler
        (S := Spec (.of k)) G H V p s y hy hp hker
    _ = ∑ᶠ w : B,
        ((F.leftIntermediateImageMap G H).residueDegree (e w).1 : ℤ) * a (e w) :=
      (finsum_comp_equiv e (f := fun x =>
        ((F.leftIntermediateImageMap G H).residueDegree x.1 : ℤ) * a x)).symm
    _ = ∑ᶠ w : B, F.tripleIncidenceTorCoefficient (S := Spec (.of k)) G H w.1 *
        ((F.tripleToLeftImageIncidence G H).residueDegree w.1.1 : ℤ) := by
      apply finsum_congr
      intro w
      rw [hcoeff w, he w, ← F.tripleToLeftImageIncidence_residueDegree G H w.1.1]
      exact mul_comm _ _
    _ = _ := (F.leftImageIncidenceTorCycleCoefficient_eq_finsum k G H y).symm

/-- A generic final-incidence point supplies its own chart and one regular list
for the actual finite-pushforward cycle coefficient formula. -/
theorem exists_firstStageRemainingEuler_finitePushforward_chart
    (y : F.leftImageIncidence G H) (hy : y ∈ genericPoints (F.leftImageIncidence G H)) :
    ∃ (V : (F.leftIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
      (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)
      (s : List ((pullback Z.hom Z.hom).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))))
      (_hs : RingTheory.Sequence.IsRegular ((pullback Z.hom Z.hom).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))) s)
      (hker : (pullback.diagonal Z.hom).ker.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s),
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n *
        F.firstStagePushforwardRemainingEuler
          (S := Spec (.of k)) G H V p s y hy hp hker n) =
        IntegralCycle.toPoints
          (IntegralCycle.finitePushforward (F.tripleToLeftImageIncidence G H)
            (F.tripleIncidenceTorCycle k G H)) y := by
  obtain ⟨V, p, hp, s, hs, hker, _⟩ :=
    F.exists_firstStageWholeRemaining_chart (S := Spec (.of k)) G H y hy
  exact ⟨V, p, hp, s, hs, hker,
    F.firstStageRemainingEuler_eq_finitePushforward_tripleTorCycle
      k G H V p y hy hp s hs hker⟩

end SmoothSite

end Motivic.FiniteCorrespondenceGenerator
