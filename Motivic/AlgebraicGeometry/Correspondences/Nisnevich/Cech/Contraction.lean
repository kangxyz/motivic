/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Cech.GraphPushforward
public import Motivic.Aglib.AlgebraicGeometry.Modules.Pushforward.Finite.Injective

/-!
# Čech contraction through an actual common closed support

Whole incidence cycles retain their original Tor coefficients in a common
finite support. Their paired second projections factor through the chosen
support lift. A finite signed presentation then contracts whenever its target
graph composite vanishes, using faithfulness of the actual closed immersion.
The existence of the local common support and lift is a separate geometric
step; these statements do not assume the desired local exactness theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {T X Y V : SmoothSite (Spec (.of k))}

/-- A literal factor of the whole incidence through a common support gives
both the Čech pairing and the same original cycle on that common support. -/
theorem exists_cech_incidence_pairing_over_common_support_with_point_lift
    (G : FiniteCorrespondenceGenerator T.hom X.hom)
    (A : FiniteCorrespondenceGenerator X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (C : Scheme.{u}) (r : G.incidence A ⟶ C) [IsFinite r]
    (s : C ⟶ pullback T.hom V.hom) [IsFinite s]
    (j : C ⟶ pullback T.hom Y.hom) [IsFinite j]
    (hsrc : s ≫ pullback.fst T.hom V.hom = j ≫ pullback.fst T.hom Y.hom)
    (htgt : s ≫ pullback.snd T.hom V.hom ≫ q.left = j ≫ pullback.snd T.hom Y.hom)
    (hrsource : r ≫ s ≫ pullback.fst T.hom V.hom = G.incidenceSource A)
    (hrtarget : r ≫ j ≫ pullback.snd T.hom Y.hom = G.incidenceTarget A ≫ q.left) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) =
        G.incidenceTorCorrespondence k A ∧
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
        IntegralCycle.finitePushforward s (IntegralCycle.finitePushforward r
          (IntegralCycle.ofGenericCoefficients (G.incidence A)
            (G.incidenceTorCoefficient (S := Spec (.of k)) A))) ∧
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := Y.hom)
        ((G.incidenceTorCorrespondence k A : Cor.mk T ⟶ Cor.mk V) ≫
          (Cor.graphFunctor k).map q) =
        IntegralCycle.finitePushforward j (IntegralCycle.finitePushforward r
          (IntegralCycle.ofGenericCoefficients (G.incidence A)
            (G.incidenceTorCoefficient (S := Spec (.of k)) A))) ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, ∃ w : G.incidence A,
        G.incidenceSource A w = B.projection z ∧
        G.incidenceTarget A w =
          (SmoothSite.etalePullbackFst q q).left (B.targetProjection z) ∧
        ((r ≫ s) ≫ pullback.snd T.hom V.hom) w =
          (SmoothSite.etalePullbackSnd q q).left (B.targetProjection z) := by
  obtain ⟨β, h₁, h₂, hpoint⟩ := exists_cech_pairing_of_incidenceTor_with_point_lift
    k G A (r ≫ s) q
    (by rw [incidenceMap_fst, Category.assoc, hrsource])
    (by
      calc
        _ = G.incidenceTarget A ≫ q.left := by
          rw [← Category.assoc, G.incidenceMap_snd A]
        _ = _ := by
          simpa only [Category.assoc] using
            ((congrArg (fun f ↦ r ≫ f) htgt).trans hrtarget).symm)
  refine ⟨β, h₁, ?_, ?_, hpoint⟩
  · simpa only [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply] using h₂
  · have h := toIntegralCycle_graph_incidenceTor k G A q (r ≫ j)
      (by rw [Category.assoc, ← hsrc, hrsource])
      (by rw [Category.assoc, hrtarget])
    simpa only [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply] using h

/-- The original common-support incidence endpoint is the projection of the
same pairing, retaining its three exact cycle identities. -/
theorem exists_cech_incidence_pairing_over_common_support
    (G : FiniteCorrespondenceGenerator T.hom X.hom)
    (A : FiniteCorrespondenceGenerator X.hom V.hom) (q : V ⟶ Y) [Etale q.left]
    (C : Scheme.{u}) (r : G.incidence A ⟶ C) [IsFinite r]
    (s : C ⟶ pullback T.hom V.hom) [IsFinite s]
    (j : C ⟶ pullback T.hom Y.hom) [IsFinite j]
    (hsrc : s ≫ pullback.fst T.hom V.hom = j ≫ pullback.fst T.hom Y.hom)
    (htgt : s ≫ pullback.snd T.hom V.hom ≫ q.left = j ≫ pullback.snd T.hom Y.hom)
    (hrsource : r ≫ s ≫ pullback.fst T.hom V.hom = G.incidenceSource A)
    (hrtarget : r ≫ j ≫ pullback.snd T.hom Y.hom = G.incidenceTarget A ≫ q.left) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) =
        G.incidenceTorCorrespondence k A ∧
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
        IntegralCycle.finitePushforward s (IntegralCycle.finitePushforward r
          (IntegralCycle.ofGenericCoefficients (G.incidence A)
            (G.incidenceTorCoefficient (S := Spec (.of k)) A))) ∧
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := Y.hom)
        ((G.incidenceTorCorrespondence k A : Cor.mk T ⟶ Cor.mk V) ≫
          (Cor.graphFunctor k).map q) =
        IntegralCycle.finitePushforward j (IntegralCycle.finitePushforward r
          (IntegralCycle.ofGenericCoefficients (G.incidence A)
            (G.incidenceTorCoefficient (S := Spec (.of k)) A))) := by
  obtain ⟨β, h₁, h₂, h₃, _⟩ :=
    exists_cech_incidence_pairing_over_common_support_with_point_lift
      k G A q C r s j hsrc htgt hrsource hrtarget
  exact ⟨β, h₁, h₂, h₃⟩

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {T Y V : SmoothSite (Spec (.of k))}

/-- A finite signed presentation contracts through a common actual closed
support. Closed-immersion faithfulness preserves every cancellation. -/
theorem exists_cech_boundary_of_finite_presentation_with_point_property
    {I : Type v} [Fintype I] (α : Cor.mk T ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (C : Scheme.{u}) (s : C ⟶ pullback T.hom V.hom) [IsFinite s]
    (j : C ⟶ pullback T.hom Y.hom) [IsClosedImmersion j]
    (γ : I → (Cor.mk T ⟶ Cor.mk V)) (δ : I → IntegralCycle C) (n : I → ℤ)
    (Q : ∀ B : FiniteCorrespondenceGenerator T.hom (SmoothSite.etalePullback q q).hom,
      B.scheme → Prop)
    (hα : ∑ i, n i • γ i = α)
    (hpair : ∀ i, ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) = γ i ∧
      toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
        IntegralCycle.finitePushforward s (δ i) ∧
      toIntegralCycle (f := T.hom) (g := Y.hom) (γ i ≫ (Cor.graphFunctor k).map q) =
        IntegralCycle.finitePushforward j (δ i) ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, Q B z)
    (hzero : α ≫ (Cor.graphFunctor k).map q = 0) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
        β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) = α ∧
      ∀ B, B ∈ β.support → ∀ z : B.scheme, Q B z := by
  classical
  choose β hfirst hsecond hthird hpoint using hpair
  let B : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q) := ∑ i, n i • β i
  let Δ : IntegralCycle C := ∑ i, n i • δ i
  have hbfirst : B ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) = α := by
    dsimp only [B]
    rw [Preadditive.sum_comp]
    simp only [Preadditive.zsmul_comp, hfirst]
    exact hα
  have hΔ : IntegralCycle.finitePushforward j Δ = 0 := by
    calc
      _ = toIntegralCycle (f := T.hom) (g := Y.hom)
          ((∑ i, n i • γ i) ≫ (Cor.graphFunctor k).map q) := by
        dsimp only [Δ]
        rw [Preadditive.sum_comp]
        simp only [Preadditive.zsmul_comp, map_sum, map_zsmul, hthird]
      _ = 0 := by rw [hα, hzero, map_zero]
  have hΔzero : Δ = 0 := IntegralCycle.finitePushforward_injective_of_isClosedImmersion j
    (hΔ.trans (map_zero _).symm)
  have hbsecond : B ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) = 0 := by
    apply toIntegralCycle_injective
    calc
      _ = IntegralCycle.finitePushforward s Δ := by
        dsimp only [B, Δ]
        rw [Preadditive.sum_comp]
        simp only [Preadditive.zsmul_comp, map_sum, map_zsmul]
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun z : IntegralCycle (pullback T.hom V.hom) ↦ n i • z) (hsecond i)
      _ = _ := by rw [hΔzero, map_zero, map_zero]
  refine ⟨B, by rw [hbfirst, hbsecond, sub_zero], ?_⟩
  intro A hA z
  change A ∈ (∑ i, n i • β i).support at hA
  obtain ⟨i, _, hi⟩ := Finsupp.mem_support_finsetSum A hA
  exact hpoint i A (Finsupp.support_smul hi) z

/-- The original signed contraction endpoint is the unrestricted point-property
projection of the same finite sum. -/
theorem exists_cech_boundary_of_finite_presentation
    {I : Type v} [Fintype I] (α : Cor.mk T ⟶ Cor.mk V) (q : V ⟶ Y) [Etale q.left]
    (C : Scheme.{u}) (s : C ⟶ pullback T.hom V.hom) [IsFinite s]
    (j : C ⟶ pullback T.hom Y.hom) [IsClosedImmersion j]
    (γ : I → (Cor.mk T ⟶ Cor.mk V)) (δ : I → IntegralCycle C) (n : I → ℤ)
    (hα : ∑ i, n i • γ i = α)
    (hpair : ∀ i, ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) = γ i ∧
      toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
        IntegralCycle.finitePushforward s (δ i) ∧
      toIntegralCycle (f := T.hom) (g := Y.hom) (γ i ≫ (Cor.graphFunctor k).map q) =
        IntegralCycle.finitePushforward j (δ i))
    (hzero : α ≫ (Cor.graphFunctor k).map q = 0) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
        β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q) = α := by
  have hpair' (i : I) : ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) = γ i ∧
      toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
        IntegralCycle.finitePushforward s (δ i) ∧
      toIntegralCycle (f := T.hom) (g := Y.hom) (γ i ≫ (Cor.graphFunctor k).map q) =
        IntegralCycle.finitePushforward j (δ i) ∧
      ∀ B, B ∈ β.support → ∀ _z : B.scheme, True := by
    obtain ⟨β, h₁, h₂, h₃⟩ := hpair i
    exact ⟨β, h₁, h₂, h₃, fun _ _ _ ↦ trivial⟩
  obtain ⟨β, hβ, _⟩ := exists_cech_boundary_of_finite_presentation_with_point_property
    k α q C s j γ δ n (fun _ _ ↦ True) hα hpair' hzero
  exact ⟨β, hβ⟩

end Motivic.FiniteCorrespondence
