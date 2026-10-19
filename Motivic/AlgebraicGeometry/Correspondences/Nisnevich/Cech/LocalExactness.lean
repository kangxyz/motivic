/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Cech.Contraction
public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Cech.FiniteSupport
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.BaseChange.ClosedImageBaseChange
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteLifting

/-!
# Local Čech contraction for actual finite correspondences

An actual finite common image is lifted over a pointed Nisnevich neighborhood.
The full source-graph incidence maps to its base change; its original generic
Tor coefficients give an actual Čech pairing. Faithfulness of the base-changed
closed immersion then preserves all signed cancellations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Motivic.FiniteCorrespondenceGenerator

universe u

namespace Motivic.FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X Y U V : SmoothSite (Spec (.of k))}

local instance (T : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

local instance (T : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

/-- A lift of one actual common finite image contracts every signed relation
supported there after an arbitrary source morphism. -/
theorem exists_cech_boundary_of_common_support_lift_with_point_lift
    (α : FiniteCorrespondence X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (hzero : (α : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q = 0)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ A ∈ α.support, A.scheme ⟶ C)
    (hr : ∀ A hA, r A hA ≫ j =
      A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
    (g : U ⟶ X)
    (b : pullback (j ≫ pullback.fst X.hom Y.hom) g.left ⟶ V.left)
    (hb : b ≫ q.left = pullback.fst (j ≫ pullback.fst X.hom Y.hom) g.left ≫
      j ≫ pullback.snd X.hom Y.hom) :
    ∃ β : Cor.mk U ⟶ Cor.mk (SmoothSite.etalePullback q q),
      (Cor.graphFunctor k).map g ≫ α =
        β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
          β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme,
        ∃ (A : FiniteCorrespondenceGenerator X.hom V.hom) (hA : A ∈ α.support)
          (a : A.scheme) (d : (pullback (j ≫ pullback.fst X.hom Y.hom) g.left : Scheme)),
          A.projection a = g.left (B.projection z) ∧
          A.targetProjection a = (SmoothSite.etalePullbackFst q q).left (B.targetProjection z) ∧
          r A hA a = pullback.fst (j ≫ pullback.fst X.hom Y.hom) g.left d ∧
          pullback.snd (j ≫ pullback.fst X.hom Y.hom) g.left d = B.projection z ∧
          b d = (SmoothSite.etalePullbackSnd q q).left (B.targetProjection z) := by
  classical
  let p := j ≫ pullback.fst X.hom Y.hom
  let D := pullback p g.left
  let j' : D ⟶ pullback U.hom Y.hom := ClosedImageBaseChange.inclusion
    X.hom Y.hom U.hom g.left (MorphismProperty.Over.w g) j
  let s : D ⟶ pullback U.hom V.hom :=
    pullback.lift (j' ≫ pullback.fst U.hom Y.hom) b (by
      calc
        _ = (j' ≫ pullback.snd U.hom Y.hom) ≫ Y.hom := by
          simp only [Category.assoc, pullback.condition]
        _ = b ≫ V.hom := by
          dsimp only [j']
          rw [ClosedImageBaseChange.inclusion_snd, ← hb, Category.assoc,
            MorphismProperty.Over.w q])
  have hs₁ : s ≫ pullback.fst U.hom V.hom = j' ≫ pullback.fst U.hom Y.hom :=
    pullback.lift_fst _ _ _
  have hs₂ : s ≫ pullback.snd U.hom V.hom ≫ q.left =
      j' ≫ pullback.snd U.hom Y.hom := by
    rw [← Category.assoc, show s ≫ pullback.snd U.hom V.hom = b from
      pullback.lift_snd _ _ _, hb]
    exact (ClosedImageBaseChange.inclusion_snd X.hom Y.hom U.hom g.left
      (MorphismProperty.Over.w g) j).symm
  have : IsFinite (s ≫ pullback.fst U.hom V.hom) := by
    rw [hs₁]
    dsimp only [j']
    rw [ClosedImageBaseChange.inclusion_fst]
    infer_instance
  have : IsFinite s := IsFinite.of_comp s (pullback.fst U.hom V.hom)
  let F := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (α := U.left) |>.toFinset
  let G (e : F) : FiniteCorrespondenceGenerator U.hom X.hom :=
    componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
      (MorphismProperty.Over.w g) e.val
      (by simpa only [F, Set.Finite.mem_toFinset] using e.property)
  let I := α.support × F
  let t (i : I) : (G i.2).incidence i.1.val ⟶ D :=
    graphIncidenceToCommonSupport k i.1.val q C j (r i.1.val i.1.property)
      (hr i.1.val i.1.property) g i.2.val
      (by simpa only [F, Set.Finite.mem_toFinset] using i.2.property)
  let γ (i : I) : Cor.mk U ⟶ Cor.mk V :=
    (G i.2).incidenceTorCorrespondence k i.1.val
  let δ (i : I) : IntegralCycle D := IntegralCycle.finitePushforward (t i)
    (IntegralCycle.ofGenericCoefficients ((G i.2).incidence i.1.val)
      ((G i.2).incidenceTorCoefficient (S := Spec (.of k)) i.1.val))
  let n (i : I) : ℤ := α i.1.val
  let Q (B : FiniteCorrespondenceGenerator U.hom (SmoothSite.etalePullback q q).hom)
      (z : B.scheme) : Prop :=
    ∃ (A : FiniteCorrespondenceGenerator X.hom V.hom) (hA : A ∈ α.support)
      (a : A.scheme) (d : D),
      A.projection a = g.left (B.projection z) ∧
      A.targetProjection a = (SmoothSite.etalePullbackFst q q).left (B.targetProjection z) ∧
      r A hA a = pullback.fst p g.left d ∧
      pullback.snd p g.left d = B.projection z ∧
      b d = (SmoothSite.etalePullbackSnd q q).left (B.targetProjection z)
  have hgraph : (Cor.graphFunctor k).map g = ∑ e : F, (G e).cycle := by
    change componentGraphCycleOver g.left (MorphismProperty.Over.w g) = _
    rw [componentGraphCycleOver_eq_sum, ← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro e _
    have he : e.val ∈ irreducibleComponents U.left := by
      simpa only [F, Set.Finite.mem_toFinset] using e.property
    rw [dite_eq_left he]
  have hα : ∑ A : α.support, α A.val • A.val.cycle = α := by
    calc
      _ = ∑ A ∈ α.support, α A • A.cycle :=
        Finset.sum_coe_sort α.support (fun A ↦ α A • A.cycle)
      _ = α := by
        simpa only [Finsupp.sum, FiniteCorrespondenceGenerator.cycle,
          Finsupp.smul_single, smul_eq_mul, mul_one] using α.sum_single
  have hsum : ∑ i : I, n i • γ i = (Cor.graphFunctor k).map g ≫ α := by
    rw [Fintype.sum_prod_type]
    change (∑ A : α.support, ∑ e : F, α A.val • (G e).incidenceTorCorrespondence k A.val) =
      incidenceTorPairing k (X := U) (Y := X) (Z := V)
        ((Cor.graphFunctor k).map g) α
    conv_rhs => rw [hgraph, ← hα]
    simp only [map_sum, AddMonoidHom.finsetSum_apply, map_zsmul, incidenceTorPairing_cycle]
    simp only [Finset.smul_sum]
  have hpair (i : I) : ∃ β : Cor.mk U ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) = γ i ∧
      toIntegralCycle (f := U.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
        IntegralCycle.finitePushforward s (δ i) ∧
      toIntegralCycle (f := U.hom) (g := Y.hom) (γ i ≫ (Cor.graphFunctor k).map q) =
        IntegralCycle.finitePushforward j' (δ i) ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, Q B z := by
    obtain ⟨β, h₁, h₂, h₃, hpoint⟩ :=
      exists_cech_incidence_pairing_over_common_support_with_point_lift k (G i.2) i.1.val q D
        (t i) s j' hs₁ hs₂
        (by
          rw [hs₁]
          dsimp only [j']
          rw [ClosedImageBaseChange.inclusion_fst]
          exact graphIncidenceToCommonSupport_snd k i.1.val q C j _ _ g _ _)
        (by
          dsimp only [j']
          rw [ClosedImageBaseChange.inclusion_snd]
          exact graphIncidenceToCommonSupport_target k i.1.val q C j _ _ g _ _)
    refine ⟨β, h₁, h₂, h₃, ?_⟩
    intro B hB z
    obtain ⟨w, hws, hwt, hwb⟩ := hpoint B hB z
    refine ⟨i.1.val, i.1.property, (G i.2).incidenceSnd i.1.val w, t i w,
      ?_, hwt, ?_, ?_, ?_⟩
    · have hsource : (G i.2).incidenceSnd i.1.val ≫ i.1.val.projection =
          (G i.2).incidenceSource i.1.val ≫ g.left := by
        calc
          _ = (G i.2).incidenceFst i.1.val ≫ (G i.2).targetProjection :=
            ((G i.2).incidence_condition i.1.val).symm
          _ = _ := by
            dsimp only [incidenceSource, G]
            rw [Category.assoc, componentGraphGeneratorOver_projection_target]
      have h := congrArg (fun f : (G i.2).incidence i.1.val ⟶ X.left ↦ f w) hsource
      change i.1.val.projection ((G i.2).incidenceSnd i.1.val w) =
        g.left ((G i.2).incidenceSource i.1.val w) at h
      rwa [hws] at h
    · have hmap : t i ≫ pullback.fst p g.left =
          (G i.2).incidenceSnd i.1.val ≫ r i.1.val i.1.property :=
        graphIncidenceToCommonSupport_fst k i.1.val q C j _ _ g _ _
      exact (congrArg (fun f : (G i.2).incidence i.1.val ⟶ C ↦ f w) hmap).symm
    · have hmap : t i ≫ pullback.snd p g.left = (G i.2).incidenceSource i.1.val :=
        graphIncidenceToCommonSupport_snd k i.1.val q C j _ _ g _ _
      exact (congrArg (fun f : (G i.2).incidence i.1.val ⟶ U.left ↦ f w) hmap).trans hws
    · have hsb : s ≫ pullback.snd U.hom V.hom = b := pullback.lift_snd _ _ _
      rw [Category.assoc, hsb] at hwb
      exact hwb
  obtain ⟨β, hβ, hpoint⟩ := exists_cech_boundary_of_finite_presentation_with_point_property k
    ((Cor.graphFunctor k).map g ≫ α) q D s j' γ δ n Q hsum hpair (by
      rw [Category.assoc, hzero, comp_zero])
  exact ⟨β, hβ.symm, hpoint⟩

/-- The original common-support contraction endpoint projects the same
construction with its source and both target point witnesses. -/
theorem exists_cech_boundary_of_common_support_lift
    (α : FiniteCorrespondence X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (hzero : (α : Cor.mk X ⟶ Cor.mk V) ≫ (Cor.graphFunctor k).map q = 0)
    (C : Scheme.{u}) (j : C ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
    [IsFinite (j ≫ pullback.fst X.hom Y.hom)]
    (r : ∀ A ∈ α.support, A.scheme ⟶ C)
    (hr : ∀ A hA, r A hA ≫ j =
      A.graphPostcompositionMap q.left (MorphismProperty.Over.w q))
    (g : U ⟶ X)
    (b : pullback (j ≫ pullback.fst X.hom Y.hom) g.left ⟶ V.left)
    (hb : b ≫ q.left = pullback.fst (j ≫ pullback.fst X.hom Y.hom) g.left ≫
      j ≫ pullback.snd X.hom Y.hom) :
    ∃ β : Cor.mk U ⟶ Cor.mk (SmoothSite.etalePullback q q),
      (Cor.graphFunctor k).map g ≫ α =
        β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
          β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) := by
  obtain ⟨β, hβ, _⟩ := exists_cech_boundary_of_common_support_lift_with_point_lift
    k α q hzero C j r hr g b hb
  exact ⟨β, hβ⟩

/-- Every signed correspondence relation for one completely decomposed étale
arrow is a Čech boundary after a pointed smooth Nisnevich neighborhood.
The relation is in the actual correspondence category, with its original Tor
composition and residue degrees; no perfect-field hypothesis is needed. -/
theorem exists_nisnevich_cech_boundary
    (α : Cor.mk X ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v))
    (hzero : α ≫ (Cor.graphFunctor k).map q = 0) (x : X.left) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
      ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
      ∃ β : Cor.mk U ⟶ Cor.mk (SmoothSite.etalePullback q q),
        (Cor.graphFunctor k).map g ≫ α =
          β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
            β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) := by
  classical
  change FiniteCorrespondence X.hom V.hom at α
  by_cases hα : α = 0
  · subst α
    refine ⟨X, 𝟙 X, ?_, x, rfl, ?_, 0, ?_⟩
    · change Etale (𝟙 X.left)
      infer_instance
    · change IsIso ((𝟙 X.left : X.left ⟶ X.left).residueFieldMap x)
      infer_instance
    · simp
  obtain ⟨C, j, hj, hp, hfac⟩ := exists_common_finite_image k α.support
    (Finsupp.support_nonempty_iff.mpr hα) q
  choose r hr using hfac
  let p : C ⟶ X.left := j ≫ pullback.fst X.hom Y.hom
  let target : C ⟶ Y.left := j ≫ pullback.snd X.hom Y.hom
  let l : pullback target q.left ⟶ C := pullback.fst target q.left
  have : Etale l := by dsimp only [l]; infer_instance
  have : IsSeparated l := by dsimp only [l]; infer_instance
  have hl : ∀ z : C, p z = x → ∃ v : (pullback target q.left : Scheme),
      l v = z ∧ IsIso (l.residueFieldMap v) := by
    intro z _
    obtain ⟨v, hv, hres⟩ := hq (target z)
    have := hres
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := target) (g := q.left) z v hv.symm
    refine ⟨w, hw₁, ?_⟩
    exact target.isIso_residueFieldMap_pullback_fst q.left v w hw₂
  obtain ⟨U, g, hg, u, hu, hgu, b₀, hb₀⟩ :=
    SmoothSite.exists_nisnevich_lift_of_isFinite (S := Spec (.of k)) X p x l hl
  let b : pullback p g.left ⟶ V.left := b₀ ≫ pullback.snd target q.left
  have hb : b ≫ q.left = pullback.fst p g.left ≫ target := by
    dsimp only [b]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hb₀]
  obtain ⟨β, hβ⟩ := exists_cech_boundary_of_common_support_lift k α q hzero
    C j r hr g b hb
  exact ⟨U, g, hg, u, hu, hgu, β, hβ⟩

end Motivic.FiniteCorrespondence
