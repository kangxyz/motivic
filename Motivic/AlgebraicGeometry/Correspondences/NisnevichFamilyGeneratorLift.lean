/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.SupportLiftImageControl
public import Motivic.Aglib.AlgebraicGeometry.ClosedImageBaseChange
public import Motivic.AlgebraicGeometry.Correspondences.GraphFunctor

/-!
# Correspondence lifting through a finite partition of the actual support

A finite closed-open cover of the actual support pullback, with a separate
lift to a labeled target on each piece, gives a sum of correspondence lifts.
Each integral incidence component is contained in a piece containing its
generic point. Its original Tor coefficient and finite-image residue degree
are retained. The family of possible targets can be arbitrarily large. Every
surviving lifted generator retains an actual map to the whole original support
pullback, compatible with the original graph postcomposition.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Motivic.FiniteCorrespondenceGenerator

variable (k : Type u) [Field k]
  {X Y U : SmoothSite (Spec (.of k))}

local instance (T : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

local instance (T : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

variable (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (g : U ⟶ X) {I : Type v} (V : I → SmoothSite (Spec (.of k)))
  (q : ∀ i, V i ⟶ Y) (n : ℕ)
  (F : Fin n → (pullback A.projection g.left).Opens)
  (hFclosed : ∀ j, IsClosed (F j : Set (pullback A.projection g.left : Scheme)))
  (hFtop : (⨆ j, F j) = ⊤) (label : Fin n → I)
  (b : ∀ j, (F j).toScheme ⟶ (V (label j)).left)
  (hb : ∀ j, b j ≫ (q (label j)).left =
    (F j).ι ≫ pullback.fst A.projection g.left ≫ A.targetProjection)

include hFclosed hFtop hb

set_option backward.isDefEq.respectTransparency false in
private theorem exists_component_graph_family_factorization
    (C : Set U.left) (hC : C ∈ irreducibleComponents U.left) :
    ∃ β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
      (componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
        (MorphismProperty.Over.w g) C hC).incidenceTorCorrespondence k A ∧
      ∀ j B, B ∈ (β j).support →
        (∃ r : B.scheme ⟶ pullback A.projection g.left,
          r ≫ ClosedImageBaseChange.inclusion X.hom Y.hom U.hom g.left
            (MorphismProperty.Over.w g) A.inclusion =
          B.graphPostcompositionMap (q (label j)).left
            (MorphismProperty.Over.w (q (label j)))) ∧
        ∀ z : B.scheme, ∃ t : (F j).toScheme,
          ((F j).ι ≫ pullback.snd A.projection g.left) t = B.projection z ∧
          b j t = B.targetProjection z := by
  classical
  let G := componentGraphGeneratorOver (X := U.left) (Y := X.left) g.left
    (MorphismProperty.Over.w g) C hC
  let t : G.incidence A ⟶ pullback A.projection g.left :=
    pullback.lift (G.incidenceSnd A) (G.incidenceSource A) (by
      change G.incidenceSnd A ≫ A.projection =
        (G.incidenceFst A ≫ G.projection) ≫ g.left
      rw [Category.assoc, componentGraphGeneratorOver_projection_target]
      exact (G.incidence_condition A).symm)
  let := IntegralCycle.genericPointFintype (G.incidence A)
  let D (x : genericPoints (G.incidence A)) := IntegralClosedSubscheme.pointClosure x.val
  have hpiece (x : genericPoints (G.incidence A)) : ∃ j, t x.val ∈ F j := by
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [hFtop]
    trivial
  choose κ hκ using hpiece
  have hRange (x : genericPoints (G.incidence A)) :
      Set.range ((D x).val.subschemeι ≫ t) ⊆ Set.range (F (κ x)).ι := by
    rw [Scheme.Opens.range_ι]
    have hs : closure ({x.val} : Set (G.incidence A)) ⊆
        t ⁻¹' (F (κ x) : Set (pullback A.projection g.left : Scheme)) :=
      ((hFclosed (κ x)).preimage t.continuous).closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr (hκ x))
    rintro z ⟨z', rfl⟩
    apply hs
    rw [← IntegralClosedSubscheme.support_pointClosure]
    exact (D x).val.range_subschemeι ▸ Set.mem_range_self z'
  let a (x : genericPoints (G.incidence A)) : (D x).val.subscheme ⟶ (F (κ x)).toScheme :=
    IsOpenImmersion.lift (F (κ x)).ι ((D x).val.subschemeι ≫ t) (hRange x)
  have ha (x : genericPoints (G.incidence A)) :
      a x ≫ (F (κ x)).ι = (D x).val.subschemeι ≫ t :=
    IsOpenImmersion.lift_fac _ _ _
  have ht (x : genericPoints (G.incidence A)) :
      a x ≫ b (κ x) ≫ (q (label (κ x))).left =
        (D x).val.subschemeι ≫ G.incidenceTarget A := by
    rw [hb, ← Category.assoc, ha]
    simp only [Category.assoc, t, pullback.lift_fst_assoc]
  let m (x : genericPoints (G.incidence A)) :
      (D x).val.subscheme ⟶ pullback U.hom (V (label (κ x))).hom :=
    pullback.lift ((D x).val.subschemeι ≫ G.incidenceSource A) (a x ≫ b (κ x)) (by
      calc
        _ = (D x).val.subschemeι ≫ G.incidenceTarget A ≫ Y.hom := by
          rw [Category.assoc, G.incidence_base A]
        _ = (a x ≫ b (κ x)) ≫ (V (label (κ x))).hom := by
          rw [← Category.assoc, ← ht x]
          simp only [Category.assoc, MorphismProperty.Over.w])
  have hm₁ (x : genericPoints (G.incidence A)) :
      m x ≫ pullback.fst U.hom (V (label (κ x))).hom =
        (D x).val.subschemeι ≫ G.incidenceSource A := pullback.lift_fst _ _ _
  have hm₂ (x : genericPoints (G.incidence A)) :
      m x ≫ pullback.snd U.hom (V (label (κ x))).hom ≫ (q (label (κ x))).left =
        (D x).val.subschemeι ≫ G.incidenceTarget A := by
    rw [← Category.assoc, show m x ≫ pullback.snd U.hom (V (label (κ x))).hom =
      a x ≫ b (κ x) from pullback.lift_snd _ _ _, Category.assoc, ht]
  have hmfin (x : genericPoints (G.incidence A)) :
      IsFinite (m x ≫ pullback.fst U.hom (V (label (κ x))).hom) := by
    rw [hm₁]
    infer_instance
  have hm (x : genericPoints (G.incidence A)) : IsFinite (m x) := by
    have := hmfin x
    exact IsFinite.of_comp (m x) (pullback.fst U.hom (V (label (κ x))).hom)
  have hr (x : genericPoints (G.incidence A)) :
      Set.range (m x ≫ pullback.fst U.hom (V (label (κ x))).hom) ∈
        irreducibleComponents U.left := by
    rw [hm₁, G.range_incidence_component_source k A x]
    exact G.range_projection_mem
  let B (x : genericPoints (G.incidence A)) :
      FiniteCorrespondenceGenerator U.hom (V (label (κ x))).hom :=
    letI := hmfin x
    letI := hm x
    supportLiftImageGenerator k (D x).val.subscheme (m x) (hr x)
  have hB (x : genericPoints (G.incidence A)) :
      ∃ r : (B x).scheme ⟶ pullback A.projection g.left,
        r ≫ ClosedImageBaseChange.inclusion X.hom Y.hom U.hom g.left
          (MorphismProperty.Over.w g) A.inclusion =
        (B x).graphPostcompositionMap (q (label (κ x))).left
          (MorphismProperty.Over.w (q (label (κ x)))) := by
    have := hmfin x
    have := hm x
    obtain ⟨r, _, hr⟩ := exists_supportLiftImageGenerator_closed_factor
      k (D x).val.subscheme (m x) (hr x) (q (label (κ x)))
      (pullback A.projection g.left)
      (ClosedImageBaseChange.inclusion X.hom Y.hom U.hom g.left
        (MorphismProperty.Over.w g) A.inclusion)
      ((D x).val.subschemeι ≫ t)
      (by
        simp only [Category.assoc, ClosedImageBaseChange.inclusion_fst]
        change (D x).val.subschemeι ≫ t ≫ pullback.snd A.projection g.left = _
        rw [hm₁]
        simp only [t, pullback.lift_snd])
      (by
        simp only [Category.assoc, ClosedImageBaseChange.inclusion_snd]
        rw [hm₂]
        change (D x).val.subschemeι ≫ t ≫ pullback.fst A.projection g.left ≫
          A.targetProjection = (D x).val.subschemeι ≫ G.incidenceSnd A ≫ A.targetProjection
        simp only [t, pullback.lift_fst_assoc])
    exact ⟨r, hr⟩
  have hBfiber (x : genericPoints (G.incidence A)) (z : (B x).scheme) :
      ∃ t : (F (κ x)).toScheme,
        ((F (κ x)).ι ≫ pullback.snd A.projection g.left) t = (B x).projection z ∧
        b (κ x) t = (B x).targetProjection z := by
    have := hm x
    obtain ⟨d, hd⟩ := surjective_toImage (m x) z
    have hs : a x ≫ (F (κ x)).ι ≫ pullback.snd A.projection g.left =
        m x ≫ pullback.fst U.hom (V (label (κ x))).hom := by
      rw [← Category.assoc, ha, hm₁]
      simp only [Category.assoc, t, pullback.lift_snd]
    have hi₁ : (m x).toImage ≫ (B x).projection =
        m x ≫ pullback.fst U.hom (V (label (κ x))).hom := by
      change (m x).toImage ≫ (m x).imageι ≫ _ = _
      rw [Scheme.Hom.toImage_imageι_assoc]
    have hi₂ : (m x).toImage ≫ (B x).targetProjection = a x ≫ b (κ x) := by
      change (m x).toImage ≫ (m x).imageι ≫ _ = _
      rw [Scheme.Hom.toImage_imageι_assoc]
      exact pullback.lift_snd _ _ _
    refine ⟨a x d, ?_, ?_⟩
    · have h := congrArg (fun f : (D x).val.subscheme ⟶ U.left ↦ f d)
        (hs.trans hi₁.symm)
      change ((F (κ x)).ι ≫ pullback.snd A.projection g.left) (a x d) =
        (B x).projection ((m x).toImage d) at h
      rwa [hd] at h
    · have h := congrArg
        (fun f : (D x).val.subscheme ⟶ (V (label (κ x))).left ↦ f d) hi₂
      change (B x).targetProjection ((m x).toImage d) = b (κ x) (a x d) at h
      rw [hd] at h
      exact h.symm
  let δ (x : genericPoints (G.incidence A)) : Cor.mk U ⟶ Cor.mk (V (label (κ x))) :=
    ((m x).residueDegree (genericPoint (D x).val.subscheme) : ℤ) • (B x).cycle
  have hδ (x : genericPoints (G.incidence A)) :
      FiniteCorrespondence.toIntegralCycle (f := U.hom) (g := Y.hom)
        (δ x ≫ (Cor.graphFunctor k).map (q (label (κ x)))) =
      IntegralCycle.finitePushforward (G.incidenceMap A) (Finsupp.single (D x) 1) := by
    have := hmfin x
    have := hm x
    have hh := supportLiftImageGenerator_graph k (D x).val.subscheme (m x) (hr x)
      (q (label (κ x))) ((D x).val.subschemeι ≫ G.incidenceMap A)
      (by simp only [Category.assoc, incidenceMap_fst, hm₁])
      (by simp only [Category.assoc, incidenceMap_snd, hm₂])
    change FiniteCorrespondence.toIntegralCycle
      (f := U.hom) (g := Y.hom)
      (δ x ≫ (Cor.graphFunctor k).map (q (label (κ x)))) = _ at hh
    rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply] at hh
    change _ = IntegralCycle.finitePushforward (G.incidenceMap A)
      (closedFundamentalCycle (D x).val) at hh
    rw [closedFundamentalCycle_of_isIntegral] at hh
    exact hh
  let ε (j : Fin n) (x : genericPoints (G.incidence A)) :
      Cor.mk U ⟶ Cor.mk (V (label j)) :=
    if h : κ x = j then h ▸ δ x else 0
  have hε (x : genericPoints (G.incidence A)) :
      (∑ j, ε j x ≫ (Cor.graphFunctor k).map (q (label j))) =
        δ x ≫ (Cor.graphFunctor k).map (q (label (κ x))) := by
    rw [Finset.sum_eq_single (κ x)]
    · simp only [ε, dite_true]
    · intro j _ hj
      simp only [ε, dite_eq_right (Ne.symm hj), zero_comp]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  refine ⟨fun j ↦ ∑ x, G.incidenceTorCoefficient (S := Spec (.of k)) A x • ε j x, ?_, ?_⟩
  · have hsum :
        (∑ j, (∑ x, G.incidenceTorCoefficient (S := Spec (.of k)) A x • ε j x) ≫
          (Cor.graphFunctor k).map (q (label j))) =
        ∑ x, G.incidenceTorCoefficient (S := Spec (.of k)) A x •
          (δ x ≫ (Cor.graphFunctor k).map (q (label (κ x)))) := by
      simp only [Preadditive.sum_comp, Preadditive.zsmul_comp]
      rw [Finset.sum_comm]
      simp only [← Finset.smul_sum, hε]
    rw [hsum]
    apply FiniteCorrespondence.toIntegralCycle_injective (f := U.hom) (g := Y.hom)
    change _ = FiniteCorrespondence.toIntegralCycle (f := U.hom) (g := Y.hom)
      (G.incidenceTorCorrespondence k A)
    rw [G.toIntegralCycle_incidenceTorCorrespondence k A,
      IntegralCycle.ofGenericCoefficients_eq_sum]
    simp only [map_sum, map_zsmul]
    apply Finset.sum_congr rfl
    intro x _
    rw [hδ]
    simp only [← map_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl
  · intro j B' hB'
    obtain ⟨x, _, hx⟩ := Finsupp.mem_support_finsetSum B' hB'
    have hx' := Finsupp.support_smul hx
    by_cases hκ : κ x = j
    · subst j
      simp only [ε, dite_true] at hx'
      have hB'eq : B' = B x := by
        simpa only [δ, cycle,
          Finsupp.support_single _ (one_ne_zero : (1 : ℤ) ≠ 0), Finset.mem_singleton]
          using Finsupp.support_smul hx'
      subst B'
      exact ⟨hB x, hBfiber x⟩
    · simp only [ε, dite_eq_right hκ, Finsupp.support_zero, Finset.notMem_empty] at hx'

/-- A closed-open covering partition of the actual support pullback, lifted to
separately labeled targets, factors the restricted generator as a finite sum.
No finiteness assumption is made on the target family or its ambient maps. -/
theorem exists_graph_family_factorization_with_fiber_lift :
    ∃ β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map g ≫ A.cycle ∧
      ∀ j B, B ∈ (β j).support →
        (∃ r : B.scheme ⟶ pullback A.projection g.left,
          r ≫ ClosedImageBaseChange.inclusion X.hom Y.hom U.hom g.left
            (MorphismProperty.Over.w g) A.inclusion =
          B.graphPostcompositionMap (q (label j)).left
            (MorphismProperty.Over.w (q (label j)))) ∧
        ∀ z : B.scheme, ∃ t : (F j).toScheme,
          ((F j).ι ≫ pullback.snd A.projection g.left) t = B.projection z ∧
          b j t = B.targetProjection z := by
  classical
  let E := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (α := U.left) |>.toFinset
  have h (C : Set U.left) (hC : C ∈ irreducibleComponents U.left) :=
    exists_component_graph_family_factorization k A g V q n F hFclosed hFtop label b hb C hC
  choose β hβ hrβ using h
  refine ⟨fun j ↦ ∑ C ∈ E, if hC : C ∈ irreducibleComponents U.left then β C hC j else 0, ?_, ?_⟩
  · simp only [Preadditive.sum_comp]
    rw [Finset.sum_comm]
    change _ = FiniteCorrespondence.incidenceTorPairing k (X := U) (Y := X) (Z := Y)
      (componentGraphCycleOver (X := U.left) (Y := X.left) g.left
        (MorphismProperty.Over.w g)) A.cycle
    rw [componentGraphCycleOver_eq_sum g.left (MorphismProperty.Over.w g)]
    simp only [map_sum, AddMonoidHom.finsetSum_apply]
    apply Finset.sum_congr rfl
    intro C _
    split_ifs with hC
    · rw [hβ, FiniteCorrespondence.incidenceTorPairing_cycle]
    · simp
  · intro j B hB
    obtain ⟨C, _, hBC⟩ := Finsupp.mem_support_finsetSum B hB
    split_ifs at hBC with hC
    · exact hrβ C hC j B hBC
    · simp only [Finsupp.support_zero, Finset.notMem_empty] at hBC

/-- The actual whole-support maps are retained by the same construction
which additionally tracks points back to their original clopen pieces. -/
theorem exists_graph_family_factorization_with_support_lift :
    ∃ β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map g ≫ A.cycle ∧
      ∀ j B, B ∈ (β j).support →
        ∃ r : B.scheme ⟶ pullback A.projection g.left,
          r ≫ ClosedImageBaseChange.inclusion X.hom Y.hom U.hom g.left
            (MorphismProperty.Over.w g) A.inclusion =
          B.graphPostcompositionMap (q (label j)).left
            (MorphismProperty.Over.w (q (label j))) := by
  obtain ⟨β, hβ, hrβ⟩ := A.exists_graph_family_factorization_with_fiber_lift
    k g V q n F hFclosed hFtop label b hb
  exact ⟨β, hβ, fun j B hB ↦ (hrβ j B hB).1⟩

/-- The original finite-sum equality endpoint, obtained from the same
support-controlled construction. -/
theorem exists_graph_family_factorization_of_support_lift :
    ∃ β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j)),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map g ≫ A.cycle := by
  obtain ⟨β, hβ, _⟩ := A.exists_graph_family_factorization_with_support_lift
    k g V q n F hFclosed hFtop label b hb
  exact ⟨β, hβ⟩

end Motivic.FiniteCorrespondenceGenerator
