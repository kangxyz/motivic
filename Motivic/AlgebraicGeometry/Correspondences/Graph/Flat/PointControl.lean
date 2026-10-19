/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.ComponentPullback

/-!
# Actual support-point control under flat graph precomposition

Every point of every surviving generator of a signed graph pullback comes
from an original support point, with both projections unchanged. The proof
uses the whole scheme-theoretic pullback cycle and actual finite images.
In particular designated target fibers survive pointed étale refinement;
neither positive coefficients nor integral source schemes are assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators

universe u

section

namespace AlgebraicGeometry.Scheme.IntegralCycle
open _root_.AlgebraicGeometry.Scheme.Hom

/-- A surviving finite-image component has all its points in the actual
finite map's range, even for signed cycles with cancellation. -/
theorem range_subschemeι_subset_of_mem_finitePushforward
    {D W : Scheme.{u}} (m : D ⟶ W) [IsFinite m] (c : IntegralCycle D)
    (A : IntegralClosedSubscheme W) (hA : A ∈ (finitePushforward m c).support) :
    Set.range A.val.subschemeι ⊆ Set.range m := by
  classical
  have hsum : finitePushforward m c =
      ∑ B ∈ c.support, Finsupp.single (B.finiteImage m)
        (c B * (m.residueDegree B.point : ℤ)) := by
    conv_lhs => rw [← c.sum_single]
    rw [map_finsuppSum]
    simp only [Finsupp.sum, finitePushforward_single]
  rw [hsum] at hA
  obtain ⟨B, _, hB⟩ := Finsupp.mem_support_finsetSum A hA
  have hAB : A = B.finiteImage m :=
    Finset.mem_singleton.mp (Finsupp.support_single_subset hB)
  subst A
  rw [Scheme.IdealSheafData.range_subschemeι]
  change ((B.val.subschemeι ≫ m).ker.support : Set W) ⊆ Set.range m
  rw [support_finiteImage]
  rintro _ ⟨z, rfl⟩
  exact ⟨B.val.subschemeι z, rfl⟩

end AlgebraicGeometry.Scheme.IntegralCycle

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {U X V : SmoothSite (Spec (.of k))}

/-- Each actual point in a generator of flat graph precomposition lifts to
the whole original support pullback, with both original projections. -/
theorem exists_point_lift_of_mem_flat_graph_comp_cycle
    (g : U ⟶ X) [Flat g.left] (A : FiniteCorrespondenceGenerator X.hom V.hom)
    (B : FiniteCorrespondenceGenerator U.hom V.hom)
    (hB : B ∈ ((Cor.graphFunctor k).map g ≫
      (show Cor.mk X ⟶ Cor.mk V from A.cycle)).support) (z : B.scheme) :
    ∃ a : A.scheme, A.projection a = g.left (B.projection z) ∧
      A.targetProjection a = B.targetProjection z := by
  classical
  have hB' : B.toIntegralClosedSubscheme ∈
      (FiniteCorrespondence.toIntegralCycle (f := U.hom) (g := V.hom)
        ((Cor.graphFunctor k).map g ≫
        (show Cor.mk X ⟶ Cor.mk V from A.cycle))).support := by
    change B.toIntegralClosedSubscheme ∈ (Finsupp.mapDomain
      FiniteCorrespondenceGenerator.toIntegralClosedSubscheme _).support
    rw [Finsupp.mapDomain_support_of_injective toIntegralClosedSubscheme_injective]
    exact Finset.mem_image.mpr ⟨B, hB, rfl⟩
  rw [A.toIntegralCycle_graphFunctor_comp_of_flat g] at hB'
  obtain ⟨w, hw⟩ := IntegralCycle.range_subschemeι_subset_of_mem_finitePushforward
    (A.graphPullbackMap g.left (MorphismProperty.Over.w g))
    (fundamentalCycle (A.graphPullback g.left)) B.toIntegralClosedSubscheme hB'
    (Set.mem_range_self z)
  change A.graphPullbackMap g.left (MorphismProperty.Over.w g) w = B.inclusion z at hw
  have hs : pullback.fst g.left A.projection w = B.projection z := by
    have h := congrArg (pullback.fst U.hom V.hom) hw
    change (A.graphPullbackMap g.left (MorphismProperty.Over.w g) ≫
      pullback.fst U.hom V.hom) w = B.projection z at h
    rw [graphPullbackMap_fst] at h
    exact h
  have ht : A.targetProjection (pullback.snd g.left A.projection w) =
      B.targetProjection z := by
    have h := congrArg (pullback.snd U.hom V.hom) hw
    change (A.graphPullbackMap g.left (MorphismProperty.Over.w g) ≫
      pullback.snd U.hom V.hom) w = B.targetProjection z at h
    rw [graphPullbackMap_snd] at h
    exact h
  refine ⟨pullback.snd g.left A.projection w, ?_, ht⟩
  have h := congrArg (fun f : A.graphPullback g.left ⟶ X.left ↦ f w)
    (pullback.condition (f := g.left) (g := A.projection))
  change g.left (pullback.fst g.left A.projection w) =
    A.projection (pullback.snd g.left A.projection w) at h
  exact h.symm.trans (congrArg g.left hs)

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {U X V : SmoothSite (Spec (.of k))}

/-- Signed cancellation can remove pulled-back generators but cannot create
untracked support points. Both projections come from one original generator. -/
theorem exists_support_point_lift_of_mem_flat_graph_comp
    (β : FiniteCorrespondence X.hom V.hom) (g : U ⟶ X) [Flat g.left]
    (B : FiniteCorrespondenceGenerator U.hom V.hom)
    (hB : B ∈ ((Cor.graphFunctor k).map g ≫ β).support) (z : B.scheme) :
    ∃ A ∈ β.support, ∃ a : A.scheme,
      A.projection a = g.left (B.projection z) ∧
      A.targetProjection a = B.targetProjection z := by
  classical
  have hβ : ∑ A ∈ β.support, β A • A.cycle = β := by
    simpa only [Finsupp.sum, FiniteCorrespondenceGenerator.cycle,
      Finsupp.smul_single, smul_eq_mul, mul_one] using β.sum_single
  have hsum : (Cor.graphFunctor k).map g ≫ β =
      ∑ A ∈ β.support, β A • ((Cor.graphFunctor k).map g ≫
        (show Cor.mk X ⟶ Cor.mk V from A.cycle)) := by
    change incidenceTorPairing k (X := U) (Y := X) (Z := V)
      ((Cor.graphFunctor k).map g) β = _
    conv_lhs => rw [← hβ]
    simp only [map_sum, map_zsmul]
    rfl
  rw [hsum] at hB
  obtain ⟨A, hA, hB⟩ := Finsupp.mem_support_finsetSum B hB
  obtain ⟨a, ha⟩ := A.exists_point_lift_of_mem_flat_graph_comp_cycle g B
    (Finsupp.support_smul hB) z
  exact ⟨A, hA, a, ha⟩

/-- Any designated set of target points over a source point is preserved
under actual flat graph precomposition at a point lying above it. -/
theorem target_mem_of_mem_flat_graph_comp
    (β : FiniteCorrespondence X.hom V.hom) (g : U ⟶ X) [Flat g.left]
    (x : X.left) (x' : U.left) (hx : g.left x' = x)
    (T : Set V.left)
    (hT : ∀ A ∈ β.support, ∀ a : A.scheme,
      A.projection a = x → A.targetProjection a ∈ T)
    (B : FiniteCorrespondenceGenerator U.hom V.hom)
    (hB : B ∈ ((Cor.graphFunctor k).map g ≫ β).support)
    (z : B.scheme) (hz : B.projection z = x') : B.targetProjection z ∈ T := by
  obtain ⟨A, hA, a, hs, ht⟩ :=
    exists_support_point_lift_of_mem_flat_graph_comp β g B hB z
  rw [hz, hx] at hs
  exact ht ▸ hT A hA a hs

/-- In particular a designated target center survives every pointed étale
source refinement. The statement is proved already for flat source maps. -/
theorem target_eq_of_mem_flat_graph_comp
    (β : FiniteCorrespondence X.hom V.hom) (g : U ⟶ X) [Flat g.left]
    (x : X.left) (x' : U.left) (hx : g.left x' = x) (v : V.left)
    (hv : ∀ A ∈ β.support, ∀ a : A.scheme,
      A.projection a = x → A.targetProjection a = v)
    (B : FiniteCorrespondenceGenerator U.hom V.hom)
    (hB : B ∈ ((Cor.graphFunctor k).map g ≫ β).support)
    (z : B.scheme) (hz : B.projection z = x') : B.targetProjection z = v := by
  exact target_mem_of_mem_flat_graph_comp β g x x' hx {v} hv B hB z hz

end Motivic.FiniteCorrespondence

end
