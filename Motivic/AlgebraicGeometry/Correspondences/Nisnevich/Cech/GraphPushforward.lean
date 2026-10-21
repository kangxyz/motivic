/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Cech.IncidencePairing

/-!
# Graph pushforward of the original generic support coefficients

A correspondence presented as finite pushforward of an actual generic
coefficient cycle remains that same coefficient cycle after graph
postcomposition. Only the actual target map changes. This applies in
particular to the original incidence Tor coefficients and retains all
collisions and residue degrees.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {T Y V : SmoothSite (Spec (.of k))}

/-- The Noetherian instance used in this module. -/
local instance graphPushforwardNoetherian
    (X : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsNoetherian X.left)

/-- The reduced scheme instance used in this module. -/
local instance graphPushforwardReduced
    (X : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj X.left) :=
  inferInstanceAs (IsReduced X.left)

/-- Graph postcomposition changes the finite support map while preserving
its complete original generic coefficient cycle. -/
theorem toIntegralCycle_graph_of_generic_coefficients
    (W : Scheme.{u}) [IsNoetherian W]
    (m : W ⟶ pullback T.hom V.hom) [IsFinite m]
    [IsFinite (m ≫ pullback.fst T.hom V.hom)]
    (hm : ∀ x : genericPoints W,
      Set.range (((IntegralClosedSubscheme.pointClosure x.val).val.subschemeι ≫ m) ≫
        pullback.fst T.hom V.hom) ∈ irreducibleComponents T.left)
    (q : V ⟶ Y) (j : W ⟶ pullback T.hom Y.hom) [IsFinite j]
    (hj₁ : j ≫ pullback.fst T.hom Y.hom = m ≫ pullback.fst T.hom V.hom)
    (hj₂ : j ≫ pullback.snd T.hom Y.hom = m ≫ pullback.snd T.hom V.hom ≫ q.left)
    (c : genericPoints W → ℤ) (α : Cor.mk T ⟶ Cor.mk V)
    (hα : FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom) α =
      IntegralCycle.finitePushforward m (IntegralCycle.ofGenericCoefficients W c)) :
    FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := Y.hom)
      (α ≫ (Cor.graphFunctor k).map q) =
      IntegralCycle.finitePushforward j (IntegralCycle.ofGenericCoefficients W c) := by
  classical
  let := IntegralCycle.genericPointFintype W
  let D (x : genericPoints W) := IntegralClosedSubscheme.pointClosure x.val
  let r (x : genericPoints W) := (D x).val.subschemeι ≫ m
  let (x : genericPoints W) : IsFinite (r x ≫ pullback.fst T.hom V.hom) := by
    dsimp only [r]
    rw [Category.assoc]
    infer_instance
  let σ : Cor.mk T ⟶ Cor.mk V := ∑ x, c x • weightedSupportImage k
    (T := T) (V := V) (D x).val.subscheme (r x) (hm x)
  have hσ : FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom) σ =
      IntegralCycle.finitePushforward m (IntegralCycle.ofGenericCoefficients W c) := by
    dsimp only [σ]
    rw [IntegralCycle.ofGenericCoefficients_eq_sum]
    simp only [map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro x _
    rw [toIntegralCycle_weightedSupportImage_pointClosure]
    simp only [← map_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hασ : α = σ := FiniteCorrespondence.toIntegralCycle_injective (hα.trans hσ.symm)
  rw [hασ]
  dsimp only [σ]
  rw [Preadditive.sum_comp, IntegralCycle.ofGenericCoefficients_eq_sum]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro x _
  have hx := supportLiftImageGenerator_graph k (D x).val.subscheme (r x) (hm x) q
    ((D x).val.subschemeι ≫ j)
    (by simp only [r, Category.assoc, hj₁])
    (by simp only [r, Category.assoc, hj₂])
  change FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := Y.hom)
    (FiniteCorrespondence.incidenceTorPairing k (X := T) (Y := V) (Z := Y)
      (c x • weightedSupportImage k (T := T) (V := V) (D x).val.subscheme (r x) (hm x))
      (componentGraphCycleOver q.left (MorphismProperty.Over.w q))) = _
  rw [map_zsmul, AddMonoidHom.smul_apply, map_zsmul]
  refine (congrArg (fun z : IntegralCycle (pullback T.hom Y.hom) ↦ c x • z) hx).trans ?_
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
  change c x • IntegralCycle.finitePushforward j (closedFundamentalCycle (D x).val) = _
  rw [closedFundamentalCycle_of_isIntegral]
  simp only [← map_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

/-- Actual incidence Tor composition has graph pushforward given by the same
original generic Tor coefficients on the whole incidence scheme. -/
theorem toIntegralCycle_graph_incidenceTor
    {X : SmoothSite (Spec (.of k))}
    (G : FiniteCorrespondenceGenerator T.hom X.hom)
    (A : FiniteCorrespondenceGenerator X.hom V.hom)
    (q : V ⟶ Y) (j : G.incidence A ⟶ pullback T.hom Y.hom) [IsFinite j]
    (hj₁ : j ≫ pullback.fst T.hom Y.hom = G.incidenceSource A)
    (hj₂ : j ≫ pullback.snd T.hom Y.hom = G.incidenceTarget A ≫ q.left) :
    FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := Y.hom)
      ((G.incidenceTorCorrespondence k A : Cor.mk T ⟶ Cor.mk V) ≫
        (Cor.graphFunctor k).map q) =
      IntegralCycle.finitePushforward j (IntegralCycle.ofGenericCoefficients (G.incidence A)
        (G.incidenceTorCoefficient (S := Spec (.of k)) A)) := by
  have : IsFinite (G.incidenceMap A ≫ pullback.fst T.hom V.hom) := by
    rw [incidenceMap_fst]
    infer_instance
  exact toIntegralCycle_graph_of_generic_coefficients k (G.incidence A) (G.incidenceMap A)
    (fun x ↦ by
      rw [Category.assoc, incidenceMap_fst, G.range_incidence_component_source k A x]
      exact G.range_projection_mem) q j
    (hj₁.trans (G.incidenceMap_fst A).symm)
    (by
      calc
        _ = G.incidenceTarget A ≫ q.left := hj₂
        _ = (G.incidenceMap A ≫ pullback.snd T.hom V.hom) ≫ q.left :=
          congrArg (fun f ↦ f ≫ q.left) (G.incidenceMap_snd A).symm
        _ = _ := Category.assoc _ _ _)
    (G.incidenceTorCoefficient (S := Spec (.of k)) A)
    (G.incidenceTorCorrespondence k A) (G.toIntegralCycle_incidenceTorCorrespondence k A)

end Motivic.FiniteCorrespondenceGenerator
