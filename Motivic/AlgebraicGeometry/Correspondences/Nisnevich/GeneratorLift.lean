/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Exterior.Simplex.GraphInterchangeRight
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Pullbacks

/-!
# Correspondence factorization from an actual support lift

A lift of the whole scheme-theoretic pullback of an integral support gives a
factorization of its restriction through the lifted target. The construction
retains the existing incidence Tor coefficients and finite-image residue
degrees. No flatness or reduction of the support pullback is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

variable (k : Type u) [Field k]
  {X Y U V : SmoothSite (Spec (.of k))}

local instance (T : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

local instance (T : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

section Image

variable (D : Scheme.{u}) [IsIntegral D] [IsNoetherian D]
  (m : D ⟶ pullback U.hom V.hom) [IsFinite m]
  (hm : Set.range (m ≫ pullback.fst U.hom V.hom) ∈ irreducibleComponents U.left)
  [IsFinite (m ≫ pullback.fst U.hom V.hom)]

/-- The actual integral finite image of a lifted component is admissible. -/
def supportLiftImageGenerator : FiniteCorrespondenceGenerator U.hom V.hom :=
  ⟨m.ker, isIntegral_finiteImage m,
    isFinite_image_projection m (pullback.fst U.hom V.hom),
    (range_image_projection m (pullback.fst U.hom V.hom)).symm ▸ hm⟩

variable (q : V ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
/-- Pushing the full component through its finite image and then the graph
preserves its actual residue degree. The ambient target map need not be finite. -/
theorem supportLiftImageGenerator_graph
    (j : D ⟶ pullback U.hom Y.hom) [IsFinite j]
    (hj₁ : j ≫ pullback.fst U.hom Y.hom = m ≫ pullback.fst U.hom V.hom)
    (hj₂ : j ≫ pullback.snd U.hom Y.hom =
      m ≫ pullback.snd U.hom V.hom ≫ q.left) :
    FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.incidenceTorPairing k (X := U) (Y := V) (Z := Y)
        ((m.residueDegree (genericPoint D) : ℤ) •
          (supportLiftImageGenerator k D m hm).cycle)
        (componentGraphCycleOver (X := V.left) (Y := Y.left) q.left (MorphismProperty.Over.w q))) =
      IntegralCycle.finitePushforward j (fundamentalCycle D) := by
  let B := supportLiftImageGenerator k D m hm
  let e := B.graphPostcompositionMap q.left (MorphismProperty.Over.w q)
  have : IsFinite e := by dsimp only [e]; infer_instance
  have ha : m.toImage ≫ e = j := by
    apply pullback.hom_ext
    · dsimp only [e]
      rw [Category.assoc, graphPostcompositionMap_fst]
      change m.toImage ≫ m.imageι ≫ pullback.fst U.hom V.hom = _
      rw [← Category.assoc, Scheme.Hom.toImage_imageι, hj₁]
    · dsimp only [e]
      rw [Category.assoc, graphPostcompositionMap_snd]
      change m.toImage ≫ m.imageι ≫ pullback.snd U.hom V.hom ≫ q.left = _
      rw [← Category.assoc, Scheme.Hom.toImage_imageι, hj₂]
  have hpoint : m.toImage (genericPoint D) = genericPoint B.scheme := genericPoint_toImage m
  have hdegree : m.toImage.residueDegree (genericPoint D) =
      m.residueDegree (genericPoint D) := by
    have h := residueDegree_comp m.toImage m.imageι (genericPoint D)
    simpa only [Scheme.Hom.toImage_imageι, residueDegree_of_surjectiveOnStalks,
      one_mul] using h.symm
  have := isFinite_toImage m
  have hpush : IntegralCycle.finitePushforward m.toImage (fundamentalCycle D) =
      (m.residueDegree (genericPoint D) : ℤ) • fundamentalCycle B.scheme := by
    rw [fundamentalCycle_of_isIntegral, fundamentalCycle_of_isIntegral,
      IntegralCycle.finitePushforward_single]
    simp only [IntegralClosedSubscheme.point_pointClosure, one_mul, hdegree,
      Finsupp.smul_single, smul_eq_mul, mul_one]
    congr 1
    apply IntegralClosedSubscheme.point_injective
    simp only [IntegralClosedSubscheme.point_finiteImage,
      IntegralClosedSubscheme.point_pointClosure, hpoint]
  have := isFinite_toImage m
  change FiniteCorrespondence.toIntegralCycle
    (FiniteCorrespondence.incidenceTorPairing k (X := U) (Y := V) (Z := Y)
      ((m.residueDegree (genericPoint D) : ℤ) • B.cycle)
      (componentGraphCycleOver (X := V.left) (Y := Y.left) q.left (MorphismProperty.Over.w q))) = _
  rw [map_zsmul, AddMonoidHom.smul_apply, map_zsmul,
    B.toIntegralCycle_incidenceTorPairing_componentGraph_right k q.left
      (MorphismProperty.Over.w q)]
  calc
    _ = IntegralCycle.finitePushforward e
        (IntegralCycle.finitePushforward m.toImage (fundamentalCycle D)) := by
      rw [hpush, map_zsmul]
    _ = IntegralCycle.finitePushforward (m.toImage ≫ e) (fundamentalCycle D) := by
      rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
      rfl
    _ = IntegralCycle.finitePushforward j (fundamentalCycle D) := by simp only [ha]

end Image

section Lift

variable (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (g : U ⟶ X) (q : V ⟶ Y)
  (b : pullback A.projection g.left ⟶ V.left)
  (hb : b ≫ q.left = pullback.fst A.projection g.left ≫ A.targetProjection)

include hb

set_option backward.isDefEq.respectTransparency false in
private theorem exists_component_graph_factorization
    (C : Set U.left) (hC : C ∈ irreducibleComponents U.left) :
    ∃ β : FiniteCorrespondence U.hom V.hom,
      FiniteCorrespondence.incidenceTorPairing k (X := U) (Y := V) (Z := Y) β
        (componentGraphCycleOver (X := V.left) (Y := Y.left) q.left (MorphismProperty.Over.w q)) =
      (componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
        (MorphismProperty.Over.w g) C hC).incidenceTorCorrespondence k A := by
  classical
  let G := componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
    (MorphismProperty.Over.w g) C hC
  let t : G.incidence A ⟶ pullback A.projection g.left :=
    pullback.lift (G.incidenceSnd A) (G.incidenceSource A) (by
      change G.incidenceSnd A ≫ A.projection =
        (G.incidenceFst A ≫ G.projection) ≫ g.left
      rw [Category.assoc, componentGraphGeneratorOver_projection_target]
      exact (G.incidence_condition A).symm)
  have ht : t ≫ b ≫ q.left = G.incidenceTarget A := by
    rw [hb, ← Category.assoc]
    simp only [t, pullback.lift_fst]
  let m : G.incidence A ⟶ pullback U.hom V.hom :=
    pullback.lift (G.incidenceSource A) (t ≫ b) (by
      calc
        _ = G.incidenceTarget A ≫ Y.hom := G.incidence_base A
        _ = (t ≫ b) ≫ V.hom := by
          rw [← ht]
          simp only [Category.assoc, MorphismProperty.Over.w])
  have hm₁ : m ≫ pullback.fst U.hom V.hom = G.incidenceSource A :=
    pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd U.hom V.hom ≫ q.left = G.incidenceTarget A := by
    rw [← Category.assoc, show m ≫ pullback.snd U.hom V.hom = t ≫ b from
      pullback.lift_snd _ _ _, Category.assoc, ht]
  have : IsFinite (m ≫ pullback.fst U.hom V.hom) := by rw [hm₁]; infer_instance
  have : IsFinite m := IsFinite.of_comp m (pullback.fst U.hom V.hom)
  let := IntegralCycle.genericPointFintype (G.incidence A)
  let D (x : genericPoints (G.incidence A)) := IntegralClosedSubscheme.pointClosure x.val
  let r (x : genericPoints (G.incidence A)) := (D x).val.subschemeι ≫ m
  have hrfin (x : genericPoints (G.incidence A)) :
      IsFinite (r x ≫ pullback.fst U.hom V.hom) := by
    dsimp only [r]
    rw [Category.assoc, hm₁]
    infer_instance
  have hr (x : genericPoints (G.incidence A)) :
      Set.range (r x ≫ pullback.fst U.hom V.hom) ∈ irreducibleComponents U.left := by
    dsimp only [r]
    rw [Category.assoc, hm₁, G.range_incidence_component_source k A x]
    exact G.range_projection_mem
  let B (x : genericPoints (G.incidence A)) : FiniteCorrespondenceGenerator U.hom V.hom :=
    letI := hrfin x
    supportLiftImageGenerator k (D x).val.subscheme (r x) (hr x)
  let δ (x : genericPoints (G.incidence A)) : FiniteCorrespondence U.hom V.hom :=
    ((r x).residueDegree (genericPoint (D x).val.subscheme) : ℤ) • (B x).cycle
  have hδ (x : genericPoints (G.incidence A)) :
      FiniteCorrespondence.toIntegralCycle
        (FiniteCorrespondence.incidenceTorPairing k (X := U) (Y := V) (Z := Y) (δ x)
          (componentGraphCycleOver (X := V.left) (Y := Y.left) q.left
            (MorphismProperty.Over.w q))) =
      IntegralCycle.finitePushforward (G.incidenceMap A)
        (Finsupp.single (D x) 1) := by
    have := hrfin x
    have hh := supportLiftImageGenerator_graph k (D x).val.subscheme (r x) (hr x) q
      ((D x).val.subschemeι ≫ G.incidenceMap A)
      (by simp only [Category.assoc, incidenceMap_fst, r, hm₁])
      (by simp only [Category.assoc, incidenceMap_snd, r, hm₂])
    change FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.incidenceTorPairing k (X := U) (Y := V) (Z := Y) (δ x)
        (componentGraphCycleOver (X := V.left) (Y := Y.left) q.left
          (MorphismProperty.Over.w q))) = _ at hh
    rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply] at hh
    change _ = IntegralCycle.finitePushforward (G.incidenceMap A)
      (closedFundamentalCycle (D x).val) at hh
    rw [closedFundamentalCycle_of_isIntegral] at hh
    exact hh
  refine ⟨∑ x, G.incidenceTorCoefficient (S := Spec (.of k)) A x • δ x, ?_⟩
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [G.toIntegralCycle_incidenceTorCorrespondence k A,
    IntegralCycle.ofGenericCoefficients_eq_sum]
  simp only [map_sum, map_zsmul, AddMonoidHom.finsetSum_apply, AddMonoidHom.smul_apply]
  apply Finset.sum_congr rfl
  intro x _
  rw [hδ]
  simp only [← map_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

/-- A literal lift of the entire pulled-back integral support gives a
correspondence lift through the target map, with all actual Tor weights retained. -/
theorem exists_graph_factorization_of_support_lift :
    ∃ β : FiniteCorrespondence U.hom V.hom,
      FiniteCorrespondence.incidenceTorPairing k (X := U) (Y := V) (Z := Y) β
        (componentGraphCycleOver (X := V.left) (Y := Y.left) q.left (MorphismProperty.Over.w q)) =
      FiniteCorrespondence.incidenceTorPairing k (X := U) (Y := X) (Z := Y)
        (componentGraphCycleOver (X := U.left) (Y := X.left) g.left
          (MorphismProperty.Over.w g)) A.cycle := by
  classical
  let F := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (α := U.left) |>.toFinset
  have h (C : Set U.left) (hC : C ∈ irreducibleComponents U.left) :=
    exists_component_graph_factorization k A g q b hb C hC
  choose β hβ using h
  refine ⟨∑ C ∈ F, if hC : C ∈ irreducibleComponents U.left then β C hC else 0, ?_⟩
  rw [componentGraphCycleOver_eq_sum g.left (MorphismProperty.Over.w g)]
  simp only [map_sum, AddMonoidHom.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro C _
  split_ifs with hC
  · rw [hβ, FiniteCorrespondence.incidenceTorPairing_cycle]
  · simp

end Lift

end Motivic.FiniteCorrespondenceGenerator
