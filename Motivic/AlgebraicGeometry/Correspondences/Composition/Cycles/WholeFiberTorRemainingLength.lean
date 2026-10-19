/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.FinitePushforwardLengthDescent
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Intersection.WholeFiberTorRemainingFiber

/-!
# Actual whole remaining-Koszul finite homology at final image generic points

The actual final image-incidence generic point lifts to generic points on every
branch of the original finite fiber. Its one middle-diagonal list therefore
has finite Koszul homology on every actual supported-Tor stalk. The proved
semilocal criterion descends those lengths to the original whole localized Tor
coefficient. No local-length, uniform-bound or whole finite-homology premise is
supplied. Comparing with the true iterated complex remains a separate step.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

open _root_.AlgebraicGeometry.Scheme.Intersection _root_.HomologicalComplex.ModuleLengthEuler

variable {S X Y Z W : Scheme.{u}}
  {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S} {i : W ⟶ S}
  [S.IsSeparated] [IsSeparated f] [IsSeparated g] [IsSeparated h] [IsSeparated i]
  [IsLocallyNoetherian (correspondenceSixfoldAmbient f g h i)]
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)
  (H : FiniteCorrespondenceGenerator h i)

local instance : (correspondenceSixfoldAmbient f g h i).IsSeparated :=
  correspondenceSixfoldAmbient_isSeparated f g h i

variable (V : (F.leftIntermediateImageProduct G H).affineOpens)
  (p : Spec Γ(F.leftIntermediateImageProduct G H, V))
  (y : F.leftImageIncidence G H)
  (hy : y ∈ genericPoints (F.leftImageIncidence G H))
  (hp : V.2.fromSpec p = F.leftImageIncidenceInclusion G H y)

include hy hp in
/-- Genuine generic-point support proves finite homology of the actual whole
localized remaining Koszul complex, in every first-stage Tor degree. -/
theorem firstStageWholeRemaining_finiteHomology
    (s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))))
    (hs : (pullback.diagonal h).ker.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s) (n : ℕ) :
    FiniteHomology (F.firstStageWholeRemainingKoszul G H V p s n) := by
  have hyV : F.leftImageIncidenceInclusion G H y ∈ V.1 := by
    rw [← hp]
    exact V.2.range_fromSpec.subset (Set.mem_range_self p)
  let P : F.leftIntermediateImageProduct G H → Prop := fun z =>
    ∀ (t : List ((pullback h h).presheaf.stalk (F.leftImageMiddlePair G H z))),
      (pullback.diagonal h).ker.stalk (F.leftImageMiddlePair G H z) = Ideal.ofList t →
      ∀ (x : {w : F.leftIntermediateSupportProduct G H //
        F.leftIntermediateImageMap G H w = z}) (m : ℕ),
        FiniteHomology (_root_.ChainComplex.Koszul.coefficientComplex (F.firstStageSupportedStalkTor
            G H x.1 m)
          ((F.leftFiberMiddleList G H z t x).map
            ((F.leftSupportMiddlePair G H).stalkMap x.1).hom))
  have hP : P (F.leftImageIncidenceInclusion G H y) := by
    intro t ht x m
    exact F.leftSupportedTorRemainingFiber_finiteHomology G H V y hy hyV t ht x m
  have hQ : P (V.2.fromSpec p) := (congrArg P hp).mpr hP
  exact F.firstStageWholeRemaining_finiteHomology_of_source G H V p s n
    (fun x => hQ s hs x n)

include hy hp in
/-- Smoothness constructs the one original diagonal list and proves actual whole
remaining finite homology simultaneously in every first-stage Tor degree. -/
theorem exists_firstStageWholeRemaining_finiteHomology [Smooth h] :
    ∃ s : List ((pullback h h).presheaf.stalk
      (F.leftImageMiddlePair G H (V.2.fromSpec p))),
      RingTheory.Sequence.IsRegular ((pullback h h).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))) s ∧
      (pullback.diagonal h).ker.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s ∧
      ∀ n, FiniteHomology (F.firstStageWholeRemainingKoszul G H V p s n) := by
  have hr : F.leftImageMiddlePair G H (V.2.fromSpec p) ∈
      Set.range (pullback.diagonal h) := by
    rw [hp]
    exact F.leftImageIncidence_middle_mem_diagonal G H y
  obtain ⟨s, hs, hker⟩ := F.exists_leftTargetRemainingList G H (V.2.fromSpec p) hr
  exact ⟨s, hs, hker,
    F.firstStageWholeRemaining_finiteHomology G H V p y hy hp s hker⟩

include hy in
/-- For every original final image generic point, an actual affine chart and one
smooth middle list give whole remaining finite homology; no coordinate lift is assumed. -/
theorem exists_firstStageWholeRemaining_chart [Smooth h] :
    ∃ (V : (F.leftIntermediateImageProduct G H).affineOpens)
      (p : Spec Γ(F.leftIntermediateImageProduct G H, V)),
      V.2.fromSpec p = F.leftImageIncidenceInclusion G H y ∧
      ∃ s : List ((pullback h h).presheaf.stalk
        (F.leftImageMiddlePair G H (V.2.fromSpec p))),
        RingTheory.Sequence.IsRegular ((pullback h h).presheaf.stalk
          (F.leftImageMiddlePair G H (V.2.fromSpec p))) s ∧
        (pullback.diagonal h).ker.stalk
          (F.leftImageMiddlePair G H (V.2.fromSpec p)) = Ideal.ofList s ∧
        ∀ n, FiniteHomology (F.firstStageWholeRemainingKoszul G H V p s n) := by
  obtain ⟨U, hU, p, hp⟩ :=
    FiniteAffineChart.exists_targetChart (F.leftImageIncidenceInclusion G H y)
  exact ⟨⟨U, hU⟩, p, hp,
    F.exists_firstStageWholeRemaining_finiteHomology G H ⟨U, hU⟩ p y hy hp⟩

end Motivic.FiniteCorrespondenceGenerator
