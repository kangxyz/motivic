/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.FinitePushforwardInjective
public import Motivic.AlgebraicGeometry.SmoothSiteCoproducts
public import Motivic.AlgebraicGeometry.Correspondences.GraphFunctor
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichGeneratorLift
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Binary disjoint unions in finite correspondences

The actual disjoint union is a binary coproduct for genuine finite
correspondences. Its inclusions are the actual graph cycles. The construction
uses the componentwise diagonal and lifts its two clopen parts, retaining the
original support cycles and their residue degrees.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic

namespace Cor

variable (k : Type u) [Field k]

local instance (T : SmoothSite (Spec (.of k))) : IsNoetherian ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsNoetherian T.left)

local instance (T : SmoothSite (Spec (.of k))) : IsReduced ((𝟭 Scheme).obj T.left) :=
  inferInstanceAs (IsReduced T.left)

/-- The actual ambient product map induced by a map of targets. -/
def graphTargetMap (X : SmoothSite (Spec (.of k)))
    {Y Z : SmoothSite (Spec (.of k))} (q : Y ⟶ Z) :
    pullback X.hom Y.hom ⟶ pullback X.hom Z.hom :=
  pullback.map _ _ _ _ (𝟙 _) q.left (𝟙 _) (by simp)
    (by simp)

@[reassoc (attr := simp)]
theorem graphTargetMap_fst (X : SmoothSite (Spec (.of k)))
    {Y Z : SmoothSite (Spec (.of k))} (q : Y ⟶ Z) :
    graphTargetMap k X q ≫ pullback.fst X.hom Z.hom = pullback.fst X.hom Y.hom := by
  simp [graphTargetMap]

@[reassoc (attr := simp)]
theorem graphTargetMap_snd (X : SmoothSite (Spec (.of k)))
    {Y Z : SmoothSite (Spec (.of k))} (q : Y ⟶ Z) :
    graphTargetMap k X q ≫ pullback.snd X.hom Z.hom =
      pullback.snd X.hom Y.hom ≫ q.left := by
  simp [graphTargetMap]

instance graphTargetMap_isClosedImmersion (X : SmoothSite (Spec (.of k)))
    {Y Z : SmoothSite (Spec (.of k))} (q : Y ⟶ Z) [IsClosedImmersion q.left] :
    IsClosedImmersion (graphTargetMap k X q) := by
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) inferInstance inferInstance
    (by simp) (MorphismProperty.Over.w q).symm

/-- When the actual ambient map is finite, graph postcomposition is its genuine
finite pushforward on the original cycle. -/
theorem toIntegralCycle_comp_graph_of_finite
    {X Y Z : SmoothSite (Spec (.of k))} (q : Y ⟶ Z)
    [IsFinite (graphTargetMap k X q)] (α : Cor.mk X ⟶ Cor.mk Y) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)
      (α ≫ (graphFunctor k).map q) =
    IntegralCycle.finitePushforward (graphTargetMap k X q)
      (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom) α) := by
  have heq :
      (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Z.hom)).comp
          ((FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)).flip
            ((graphFunctor k).map q)) =
        (IntegralCycle.finitePushforward (graphTargetMap k X q)).comp
          (FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)) := by
    apply Finsupp.addHom_ext
    intro A n
    have hsingle : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hsingle]
    simp only [map_zsmul]
    congr 1
    change FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.incidenceTorPairing k (X := X) (Y := Y) (Z := Z)
        A.cycle (componentGraphCycleOver q.left (MorphismProperty.Over.w q))) = _
    rw [A.toIntegralCycle_incidenceTorPairing_componentGraph_right k q.left
      (MorphismProperty.Over.w q)]
    have hmap : A.graphPostcompositionMap q.left (MorphismProperty.Over.w q) =
        A.inclusion ≫ graphTargetMap k X q := by
      apply pullback.hom_ext <;> simp [FiniteCorrespondenceGenerator.projection,
        FiniteCorrespondenceGenerator.targetProjection, correspondenceProjection,
        FiniteCorrespondenceGenerator.inclusion]
    simp only [hmap, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]
    congr 1
    have : IsNoetherian (pullback X.hom Y.hom) :=
      isNoetherian_of_finiteType (pullback.fst X.hom Y.hom)
    change closedFundamentalCycle A.val =
      FiniteCorrespondence.toIntegralCycle A.cycle
    rw [closedFundamentalCycle_of_isIntegral, FiniteCorrespondenceGenerator.cycle,
      FiniteCorrespondence.toIntegralCycle_single]
    rfl
  exact congrArg (fun f => f α) heq

/-- The graph of an actual closed immersion is a monomorphism in `Cor`. -/
instance graph_map_mono_of_isClosedImmersion
    {Y Z : SmoothSite (Spec (.of k))} (q : Y ⟶ Z) [IsClosedImmersion q.left] :
    Mono ((graphFunctor k).map q) where
  right_cancellation {X} α β h := by
    apply FiniteCorrespondence.toIntegralCycle_injective
    apply IntegralCycle.finitePushforward_injective_of_isClosedImmersion
      (graphTargetMap k X.toSmoothSite q)
    have h' := congrArg
      (FiniteCorrespondence.toIntegralCycle (f := X.toSmoothSite.hom) (g := Z.hom)) h
    rw [toIntegralCycle_comp_graph_of_finite k q α,
      toIntegralCycle_comp_graph_of_finite k q β] at h'
    exact h'

/-- An integral support whose target lies in an open subscheme lifts through
that open immersion as an actual correspondence. -/
theorem exists_graph_factorization_of_range_subset
    {W V Y : SmoothSite (Spec (.of k))}
    (A : FiniteCorrespondenceGenerator W.hom Y.hom) (q : V ⟶ Y)
    [IsOpenImmersion q.left]
    (hA : Set.range A.targetProjection ⊆ Set.range q.left) :
    ∃ β : Cor.mk W ⟶ Cor.mk V, β ≫ (graphFunctor k).map q = A.cycle := by
  let b : A.scheme ⟶ V.left := IsOpenImmersion.lift q.left A.targetProjection hA
  have hb : b ≫ q.left = A.targetProjection := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨β, hβ⟩ := A.exists_graph_factorization_of_support_lift k (𝟙 W) q
    (pullback.fst A.projection (𝟙 W.left) ≫ b)
    (by rw [Category.assoc, hb]; simp)
  refine ⟨β, ?_⟩
  change β ≫ (graphFunctor k).map q = (𝟙 (Cor.mk W)) ≫ A.cycle at hβ
  simpa only [Category.id_comp] using hβ

/-- The genuine diagonal components lying in a specified open image. -/
def partialIdentity {V W : SmoothSite (Spec (.of k))} (q : V ⟶ W) :
    Cor.mk W ⟶ Cor.mk W := by
  classical
  exact ∑ C ∈ TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.toFinset,
    if hC : C ∈ irreducibleComponents W.left then
      if C ⊆ Set.range q.left then (componentIdentityGenerator W.hom C hC).cycle else 0
    else 0

/-- The portion of the diagonal over an open image factors through its graph. -/
theorem exists_partialIdentity_factorization
    {V W : SmoothSite (Spec (.of k))} (q : V ⟶ W) [IsOpenImmersion q.left] :
    ∃ p : Cor.mk W ⟶ Cor.mk V, p ≫ (graphFunctor k).map q = partialIdentity k q := by
  classical
  have hlift (C : Set W.left) (hC : C ∈ irreducibleComponents W.left)
      (h : C ⊆ Set.range q.left) :
      ∃ p : Cor.mk W ⟶ Cor.mk V,
        p ≫ (graphFunctor k).map q = (componentIdentityGenerator W.hom C hC).cycle := by
    apply exists_graph_factorization_of_range_subset k _ q
    simpa only [componentIdentityGenerator_targetProjection, componentIdentityGenerator_range]
      using h
  choose p hp using hlift
  refine ⟨∑ C ∈ TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.toFinset,
    if hC : C ∈ irreducibleComponents W.left then
      if h : C ⊆ Set.range q.left then p C hC h else 0
    else 0, ?_⟩
  rw [Preadditive.sum_comp]
  unfold partialIdentity
  apply Finset.sum_congr rfl
  intro C _
  split_ifs with hC h
  · exact hp C hC h
  · simp
  · simp

/-- Disjoint source and target components have empty actual incidence. -/
theorem graph_comp_partialIdentity_eq_zero
    {U V W : SmoothSite (Spec (.of k))} (q : U ⟶ W) (r : V ⟶ W)
    (h : Disjoint (Set.range q.left) (Set.range r.left)) :
    (graphFunctor k).map q ≫ partialIdentity k r = 0 := by
  classical
  unfold partialIdentity
  rw [Preadditive.comp_sum]
  apply Finset.sum_eq_zero
  intro C _
  split_ifs with hC hCr
  · change FiniteCorrespondence.incidenceTorPairing k (X := U) (Y := W) (Z := W)
      (componentGraphCycleOver q.left (MorphismProperty.Over.w q))
      (componentIdentityGenerator W.hom C hC).cycle = 0
    rw [componentGraphCycleOver_eq_sum]
    simp only [map_sum, AddMonoidHom.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro D _
    split_ifs with hD
    · rw [FiniteCorrespondence.incidenceTorPairing_cycle]
      let A := componentGraphGeneratorOver q.left (MorphismProperty.Over.w q) D hD
      let B := componentIdentityGenerator W.hom C hC
      have : IsEmpty (A.incidence B) := ⟨fun x => by
        have hxq : A.targetProjection (A.incidenceFst B x) ∈ Set.range q.left := by
          rw [← componentGraphGeneratorOver_projection_target q.left
            (MorphismProperty.Over.w q) D hD]
          exact Set.mem_range_self _
        have hxr : B.projection (A.incidenceSnd B x) ∈ Set.range r.left := by
          apply hCr
          exact (componentIdentityGenerator_range W.hom C hC) ▸ Set.mem_range_self _
        have heq : A.targetProjection (A.incidenceFst B x) =
            B.projection (A.incidenceSnd B x) :=
          congrArg (fun f => f x) (A.incidence_condition B)
        exact Set.disjoint_left.mp h (heq ▸ hxq) hxr⟩
      exact A.incidenceTorCorrespondence_eq_zero_of_isEmpty k B
    · simp
  · simp
  · simp

/-- The actual disjoint-union object in the correspondence category. -/
def coproduct (X Y : Cor k) : Cor k :=
  ⟨SmoothSite.coproduct X.toSmoothSite Y.toSmoothSite⟩

/-- The first coproduct inclusion is its genuine componentwise graph cycle. -/
def coproductInl (X Y : Cor k) : X ⟶ coproduct k X Y :=
  (graphFunctor k).map (SmoothSite.coproductInl X.toSmoothSite Y.toSmoothSite)

/-- The second coproduct inclusion is its genuine componentwise graph cycle. -/
def coproductInr (X Y : Cor k) : Y ⟶ coproduct k X Y :=
  (graphFunctor k).map (SmoothSite.coproductInr X.toSmoothSite Y.toSmoothSite)

/-- The two clopen portions sum to the actual diagonal, component by component. -/
theorem partialIdentity_inl_add_inr (X Y : SmoothSite (Spec (.of k))) :
    partialIdentity k (SmoothSite.coproductInl X Y) +
      partialIdentity k (SmoothSite.coproductInr X Y) =
        𝟙 (Cor.mk (SmoothSite.coproduct X Y)) := by
  classical
  change _ = componentIdentityCycle (X := (SmoothSite.coproduct X Y).left)
    (SmoothSite.coproduct X Y).hom
  rw [partialIdentity, partialIdentity, ← Finset.sum_add_distrib,
    componentIdentityCycle_eq_sum]
  apply Finset.sum_congr rfl
  intro C _
  simp only [Functor.id_obj]
  by_cases hC : C ∈ irreducibleComponents (SmoothSite.coproduct X Y).left
  · simp only [dite_eq_left hC]
    obtain h | h := SmoothSite.irreducibleComponent_subset_coproduct_range X Y hC
    · have hn := SmoothSite.irreducibleComponent_not_subset_both_coproduct_ranges X Y hC
      have h' : ¬ C ⊆ Set.range (SmoothSite.coproductInr X Y).left :=
        fun h' => hn ⟨h, h'⟩
      simp only [ite_eq_left h, ite_eq_right h', add_zero]
    · have hn := SmoothSite.irreducibleComponent_not_subset_both_coproduct_ranges X Y hC
      have h' : ¬ C ⊆ Set.range (SmoothSite.coproductInl X Y).left :=
        fun h' => hn ⟨h', h⟩
      simp only [ite_eq_left h, ite_eq_right h', zero_add]
  · simp only [dite_eq_right hC, add_zero]

/-- Genuine inverse-clopen-graph cycles satisfy the five biproduct matrix identities. -/
theorem exists_coproduct_projections (X Y : Cor k) :
    ∃ (p : coproduct k X Y ⟶ X) (q : coproduct k X Y ⟶ Y),
      coproductInl k X Y ≫ p = 𝟙 X ∧
      coproductInl k X Y ≫ q = 0 ∧
      coproductInr k X Y ≫ p = 0 ∧
      coproductInr k X Y ≫ q = 𝟙 Y ∧
      p ≫ coproductInl k X Y + q ≫ coproductInr k X Y = 𝟙 (coproduct k X Y) := by
  obtain ⟨p, hp⟩ := exists_partialIdentity_factorization k
    (SmoothSite.coproductInl X.toSmoothSite Y.toSmoothSite)
  obtain ⟨q, hq⟩ := exists_partialIdentity_factorization k
    (SmoothSite.coproductInr X.toSmoothSite Y.toSmoothSite)
  let i := coproductInl k X Y
  let j := coproductInr k X Y
  change p ≫ i = partialIdentity k
    (SmoothSite.coproductInl X.toSmoothSite Y.toSmoothSite) at hp
  change q ≫ j = partialIdentity k
    (SmoothSite.coproductInr X.toSmoothSite Y.toSmoothSite) at hq
  have hi : Mono i := graph_map_mono_of_isClosedImmersion k _
  have hj : Mono j := graph_map_mono_of_isClosedImmersion k _
  have htotal : p ≫ i + q ≫ j = 𝟙 (coproduct k X Y) := by
    rw [hp, hq]
    exact partialIdentity_inl_add_inr k X.toSmoothSite Y.toSmoothSite
  have hij : i ≫ q = 0 := by
    apply (cancel_mono j).mp
    rw [Category.assoc, hq, zero_comp]
    exact graph_comp_partialIdentity_eq_zero k _ _
      (isCompl_range_inl_inr X.toSmoothSite.left Y.toSmoothSite.left).disjoint
  have hji : j ≫ p = 0 := by
    apply (cancel_mono i).mp
    rw [Category.assoc, hp, zero_comp]
    exact graph_comp_partialIdentity_eq_zero k _ _
      (isCompl_range_inl_inr X.toSmoothSite.left Y.toSmoothSite.left).disjoint.symm
  have hii : i ≫ p = 𝟙 X := by
    apply (cancel_mono i).mp
    have hh := congrArg (fun a => i ≫ a) htotal
    simpa only [Preadditive.comp_add, ← Category.assoc, hij, zero_comp,
      add_zero, Category.comp_id, Category.id_comp] using hh
  have hjj : j ≫ q = 𝟙 Y := by
    apply (cancel_mono j).mp
    have hh := congrArg (fun a => j ≫ a) htotal
    simpa only [Preadditive.comp_add, ← Category.assoc, hji, zero_comp,
      zero_add, Category.comp_id, Category.id_comp] using hh
  exact ⟨p, q, hii, hij, hji, hjj, htotal⟩

/-- The actual graph inclusions exhibit disjoint union as a categorical coproduct. -/
def coproductIsColimit (X Y : Cor k) :
    IsColimit (BinaryCofan.mk (coproductInl k X Y) (coproductInr k X Y)) := by
  let p := (exists_coproduct_projections k X Y).choose
  let q := (exists_coproduct_projections k X Y).choose_spec.choose
  obtain ⟨hp, hq, hp', hq', htotal⟩ :=
    (exists_coproduct_projections k X Y).choose_spec.choose_spec
  change coproductInl k X Y ≫ p = _ at hp
  change coproductInl k X Y ≫ q = _ at hq
  change coproductInr k X Y ≫ p = _ at hp'
  change coproductInr k X Y ≫ q = _ at hq'
  refine BinaryCofan.IsColimit.mk _ (fun f g => p ≫ f + q ≫ g) ?_ ?_ ?_
  · intro T f g
    change coproductInl k X Y ≫ (p ≫ f + q ≫ g) = f
    simp only [Preadditive.comp_add, ← Category.assoc, hp, hq, Category.id_comp,
      zero_comp, add_zero]
  · intro T f g
    change coproductInr k X Y ≫ (p ≫ f + q ≫ g) = g
    simp only [Preadditive.comp_add, ← Category.assoc, hp', hq', Category.id_comp,
      zero_comp, zero_add]
  · intro T f g m hm₁ hm₂
    change coproductInl k X Y ≫ m = f at hm₁
    change coproductInr k X Y ≫ m = g at hm₂
    calc
      m = (p ≫ coproductInl k X Y + q ≫ coproductInr k X Y) ≫ m := by
        rw [htotal, Category.id_comp]
      _ = p ≫ f + q ≫ g := by
        rw [Preadditive.add_comp, Category.assoc, Category.assoc, hm₁, hm₂]

instance (X Y : Cor k) : HasBinaryCoproduct X Y :=
  ⟨⟨_, coproductIsColimit k X Y⟩⟩

instance : HasBinaryCoproducts (Cor k) := hasBinaryCoproducts_of_hasColimit_pair _

instance : HasBinaryBiproducts (Cor k) := HasBinaryBiproducts.of_hasBinaryCoproducts

/-- Restriction along the actual graph inclusions is a bijection on correspondence groups. -/
theorem coproduct_restriction_bijective (X Y T : Cor k) :
    Function.Bijective (fun α : coproduct k X Y ⟶ T =>
      (coproductInl k X Y ≫ α, coproductInr k X Y ≫ α)) := by
  constructor
  · intro α β h
    apply (coproductIsColimit k X Y).hom_ext
    intro j
    cases j with
    | mk j => cases j
              · exact congrArg Prod.fst h
              · exact congrArg Prod.snd h
  · rintro ⟨α, β⟩
    refine ⟨(coproductIsColimit k X Y).desc (BinaryCofan.mk α β), ?_⟩
    ext
    · exact (coproductIsColimit k X Y).fac (BinaryCofan.mk α β) ⟨WalkingPair.left⟩
    · exact (coproductIsColimit k X Y).fac (BinaryCofan.mk α β) ⟨WalkingPair.right⟩

/-- An empty source has no integral finite-correspondence generator, so every
actual signed correspondence with that source vanishes. -/
theorem hom_eq_zero_of_isEmpty_source {X Y : Cor k} [IsEmpty X.toSmoothSite.left]
    (α : X ⟶ Y) : α = 0 := by
  apply Finsupp.ext
  intro A
  exact isEmptyElim (α := X.toSmoothSite.left) (A.projection (Classical.arbitrary A.scheme))

instance hom_subsingleton_of_isEmpty_source {X Y : Cor k} [IsEmpty X.toSmoothSite.left] :
    Subsingleton (X ⟶ Y) :=
  ⟨fun α β => (hom_eq_zero_of_isEmpty_source k α).trans
    (hom_eq_zero_of_isEmpty_source k β).symm⟩

/-- An empty target also has no actual integral correspondence supports. -/
theorem hom_eq_zero_of_isEmpty_target {X Y : Cor k} [IsEmpty Y.toSmoothSite.left]
    (α : X ⟶ Y) : α = 0 := by
  apply Finsupp.ext
  intro A
  exact isEmptyElim (α := Y.toSmoothSite.left) (A.targetProjection (Classical.arbitrary A.scheme))

instance hom_subsingleton_of_isEmpty_target {X Y : Cor k} [IsEmpty Y.toSmoothSite.left] :
    Subsingleton (X ⟶ Y) :=
  ⟨fun α β => (hom_eq_zero_of_isEmpty_target k α).trans
    (hom_eq_zero_of_isEmpty_target k β).symm⟩

/-- The empty scheme, regarded as an actual correspondence object. -/
def empty : Cor k := ⟨SmoothSite.mk (Scheme.emptyTo (Spec (.of k)))⟩

instance empty_isEmpty : IsEmpty (empty k).toSmoothSite.left :=
  inferInstanceAs (IsEmpty (∅ : Scheme.{u}))

/-- The actual empty scheme is a zero object of finite correspondences. -/
theorem empty_isZero : IsZero (empty k) where
  unique_to _ := ⟨{ default := 0, uniq := hom_eq_zero_of_isEmpty_source k }⟩
  unique_from _ := ⟨{ default := 0, uniq := hom_eq_zero_of_isEmpty_target k }⟩

instance : HasZeroObject (Cor k) := ⟨⟨empty k, empty_isZero k⟩⟩

instance : HasFiniteCoproducts (Cor k) := hasFiniteCoproducts_of_has_binary_and_initial

instance : HasFiniteBiproducts (Cor k) := HasFiniteBiproducts.of_hasFiniteCoproducts

end Cor

end Motivic
