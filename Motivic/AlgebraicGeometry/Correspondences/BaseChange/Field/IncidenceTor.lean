/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Incidence
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Cycles.ExteriorImageRemainingTorAttachment
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.DiagonalBaseChange
public import Motivic.AlgebraicGeometry.Correspondences.Composition.Associativity.GenericDominance

/-!
# Actual component-generator incidence under field change

The reduced components are identified with their actual closed images in the
new smooth product. Their pair product is never reduced. The literal pair
closed immersion attaches the one original middle list to actual incidence Tor.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Hom
open _root_.AlgebraicGeometry.Scheme.Products

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- The whole support's ambient inclusion retains its literal new target coordinate. -/
@[reassoc (attr := simp)]
theorem fieldBaseChangeInclusion_snd :
    A.fieldBaseChangeInclusion φ ≫
      pullback.snd ((SmoothSite.fieldBaseChange φ).obj X).hom
        ((SmoothSite.fieldBaseChange φ).obj Y).hom = A.fieldBaseChangeTargetProjection φ := by
  unfold fieldBaseChangeInclusion
  have h := congrArg (fun e => e.left)
    (SmoothSite.baseChangeProductIso_hom_snd (Spec.map (CommRingCat.ofHom φ)) X Y)
  dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productSnd,
    SmoothSite.homMk_left] at h
  dsimp only [SmoothSite.fieldBaseChange]
  rw [Category.assoc, h]
  apply pullback.hom_ext
  · rw [Category.assoc, SmoothSite.baseChange_map_fst,
      fieldBaseChangeTargetProjection_fst, ← Category.assoc,
      fieldBaseChangeAmbientInclusion_fst]
    rfl
  · simp only [Category.assoc, SmoothSite.baseChange_map_snd,
      fieldBaseChangeAmbientInclusion_snd]
    exact (A.fieldBaseChangeTargetProjection_snd φ).symm

/-- The original reduced component and its actual closed image are canonically isomorphic. -/
def fieldBaseChangeComponentSchemeIso (a : genericPoints (A.fieldBaseChangeSupport φ)) :
    (IntegralClosedSubscheme.pointClosure a.1).val.subscheme ≅
      (A.fieldBaseChangeComponentGenerator φ a).scheme :=
  asIso ((IntegralClosedSubscheme.pointClosure a.1).val.subschemeι ≫
    A.fieldBaseChangeInclusion φ).toImage

@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentSchemeIso_hom_inclusion
    (a : genericPoints (A.fieldBaseChangeSupport φ)) :
    (A.fieldBaseChangeComponentSchemeIso φ a).hom ≫
      (A.fieldBaseChangeComponentGenerator φ a).inclusion =
        (IntegralClosedSubscheme.pointClosure a.1).val.subschemeι ≫ A.fieldBaseChangeInclusion φ :=
  Scheme.Hom.toImage_imageι _

@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentSchemeIso_hom_projection
    (a : genericPoints (A.fieldBaseChangeSupport φ)) :
    (A.fieldBaseChangeComponentSchemeIso φ a).hom ≫
      (A.fieldBaseChangeComponentGenerator φ a).projection =
        (IntegralClosedSubscheme.pointClosure a.1).val.subschemeι ≫
          A.fieldBaseChangeProjection φ := by
  change _ ≫ (A.fieldBaseChangeComponentGenerator φ a).inclusion ≫ _ = _
  rw [fieldBaseChangeComponentSchemeIso_hom_inclusion_assoc, fieldBaseChangeInclusion_fst]

@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentSchemeIso_hom_targetProjection
    (a : genericPoints (A.fieldBaseChangeSupport φ)) :
    (A.fieldBaseChangeComponentSchemeIso φ a).hom ≫
      (A.fieldBaseChangeComponentGenerator φ a).targetProjection =
        (IntegralClosedSubscheme.pointClosure a.1).val.subschemeι ≫
          A.fieldBaseChangeTargetProjection φ := by
  change _ ≫ (A.fieldBaseChangeComponentGenerator φ a).inclusion ≫ _ = _
  rw [fieldBaseChangeComponentSchemeIso_hom_inclusion_assoc, fieldBaseChangeInclusion_snd]

/-- The actual generator support embeds back into the whole pulled-back support. -/
def fieldBaseChangeComponentToWhole (a : genericPoints (A.fieldBaseChangeSupport φ)) :
    (A.fieldBaseChangeComponentGenerator φ a).scheme ⟶ A.fieldBaseChangeSupport φ :=
  (A.fieldBaseChangeComponentSchemeIso φ a).inv ≫
    (IntegralClosedSubscheme.pointClosure a.1).val.subschemeι

instance fieldBaseChangeComponentToWhole_isClosedImmersion
    (a : genericPoints (A.fieldBaseChangeSupport φ)) :
    IsClosedImmersion (A.fieldBaseChangeComponentToWhole φ a) := by
  unfold fieldBaseChangeComponentToWhole
  infer_instance

@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentToWhole_projection
    (a : genericPoints (A.fieldBaseChangeSupport φ)) :
    A.fieldBaseChangeComponentToWhole φ a ≫ A.fieldBaseChangeProjection φ =
      (A.fieldBaseChangeComponentGenerator φ a).projection := by
  rw [fieldBaseChangeComponentToWhole, Category.assoc,
    ← fieldBaseChangeComponentSchemeIso_hom_projection, Iso.inv_hom_id_assoc]

@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentToWhole_targetProjection
    (a : genericPoints (A.fieldBaseChangeSupport φ)) :
    A.fieldBaseChangeComponentToWhole φ a ≫ A.fieldBaseChangeTargetProjection φ =
      (A.fieldBaseChangeComponentGenerator φ a).targetProjection := by
  rw [fieldBaseChangeComponentToWhole, Category.assoc,
    ← fieldBaseChangeComponentSchemeIso_hom_targetProjection, Iso.inv_hom_id_assoc]

variable (a : genericPoints (A.fieldBaseChangeSupport φ))
  (b : genericPoints (B.fieldBaseChangeSupport φ))

/-- The original component pair maps isomorphically to the actual new generator support product. -/
def fieldBaseChangeComponentPairMap : A.fieldBaseChangeComponentPair φ B a b ⟶
    (A.fieldBaseChangeComponentGenerator φ a).supportProduct
      (B.fieldBaseChangeComponentGenerator φ b) :=
  pullback.map _ _ _ _ (A.fieldBaseChangeComponentSchemeIso φ a).hom
    (B.fieldBaseChangeComponentSchemeIso φ b).hom (𝟙 (Spec (.of L)))
    (by simp only [Category.comp_id, fieldBaseChangeComponentSchemeIso_hom_targetProjection_assoc,
      Category.assoc, fieldBaseChangeTargetProjection_snd])
    (by
      simp only [Category.comp_id, fieldBaseChangeComponentSchemeIso_hom_projection_assoc]
      exact congrArg ((IntegralClosedSubscheme.pointClosure b.1).val.subschemeι ≫ ·)
        (B.fieldBaseChangeProjection_snd φ).symm)

instance fieldBaseChangeComponentPairMap_isIso :
    IsIso (A.fieldBaseChangeComponentPairMap φ B a b) := by
  unfold fieldBaseChangeComponentPairMap
  infer_instance

/-- The full pair product is identified without replacing its structure by its reduction. -/
def fieldBaseChangeComponentPairIso : A.fieldBaseChangeComponentPair φ B a b ≅
    (A.fieldBaseChangeComponentGenerator φ a).supportProduct
      (B.fieldBaseChangeComponentGenerator φ b) :=
  asIso (A.fieldBaseChangeComponentPairMap φ B a b)

/-- The actual generator-pair product embeds into the original whole new support product. -/
def fieldBaseChangeGeneratorPairInclusion :
    (A.fieldBaseChangeComponentGenerator φ a).supportProduct
        (B.fieldBaseChangeComponentGenerator φ b) ⟶ A.fieldBaseChangeSupportProduct φ B :=
  (A.fieldBaseChangeComponentPairIso φ B a b).inv ≫
    A.fieldBaseChangeComponentPairInclusion φ B a b

instance fieldBaseChangeGeneratorPairInclusion_isClosedImmersion :
    IsClosedImmersion (A.fieldBaseChangeGeneratorPairInclusion φ B a b) := by
  unfold fieldBaseChangeGeneratorPairInclusion
  infer_instance

@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentPairMap_fst :
    A.fieldBaseChangeComponentPairMap φ B a b ≫
      pullback.fst
        ((A.fieldBaseChangeComponentGenerator φ a).targetProjection ≫
          ((SmoothSite.fieldBaseChange φ).obj Y).hom)
        ((B.fieldBaseChangeComponentGenerator φ b).projection ≫
          ((SmoothSite.fieldBaseChange φ).obj Y).hom) =
      pullback.fst
        ((IntegralClosedSubscheme.pointClosure a.1).val.subschemeι ≫
          A.fieldBaseChangeSupportHom φ)
        ((IntegralClosedSubscheme.pointClosure b.1).val.subschemeι ≫
          B.fieldBaseChangeSupportHom φ) ≫ (A.fieldBaseChangeComponentSchemeIso φ a).hom :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentPairMap_snd :
    A.fieldBaseChangeComponentPairMap φ B a b ≫
      pullback.snd
        ((A.fieldBaseChangeComponentGenerator φ a).targetProjection ≫
          ((SmoothSite.fieldBaseChange φ).obj Y).hom)
        ((B.fieldBaseChangeComponentGenerator φ b).projection ≫
          ((SmoothSite.fieldBaseChange φ).obj Y).hom) =
      pullback.snd
        ((IntegralClosedSubscheme.pointClosure a.1).val.subschemeι ≫
          A.fieldBaseChangeSupportHom φ)
        ((IntegralClosedSubscheme.pointClosure b.1).val.subschemeι ≫
          B.fieldBaseChangeSupportHom φ) ≫ (B.fieldBaseChangeComponentSchemeIso φ b).hom :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem fieldBaseChangeGeneratorPairInclusion_fst :
    A.fieldBaseChangeGeneratorPairInclusion φ B a b ≫ A.fieldBaseChangeSupportProductFst φ B =
      pullback.fst
        ((A.fieldBaseChangeComponentGenerator φ a).targetProjection ≫
          ((SmoothSite.fieldBaseChange φ).obj Y).hom)
        ((B.fieldBaseChangeComponentGenerator φ b).projection ≫
          ((SmoothSite.fieldBaseChange φ).obj Y).hom) ≫ A.fieldBaseChangeComponentToWhole φ a := by
  apply (cancel_epi (A.fieldBaseChangeComponentPairMap φ B a b)).mp
  simp only [fieldBaseChangeGeneratorPairInclusion, fieldBaseChangeComponentPairIso,
    asIso_inv, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  simp [fieldBaseChangeComponentPairMap, fieldBaseChangeComponentPairInclusion,
    componentPairExteriorInclusion_eq_map,
    pullback.map, fieldBaseChangeSupportProductFst, fieldBaseChangeComponentToWhole,
    Category.assoc]

@[reassoc (attr := simp)]
theorem fieldBaseChangeGeneratorPairInclusion_snd :
    A.fieldBaseChangeGeneratorPairInclusion φ B a b ≫ A.fieldBaseChangeSupportProductSnd φ B =
      pullback.snd
        ((A.fieldBaseChangeComponentGenerator φ a).targetProjection ≫
          ((SmoothSite.fieldBaseChange φ).obj Y).hom)
        ((B.fieldBaseChangeComponentGenerator φ b).projection ≫
          ((SmoothSite.fieldBaseChange φ).obj Y).hom) ≫ B.fieldBaseChangeComponentToWhole φ b := by
  apply (cancel_epi (A.fieldBaseChangeComponentPairMap φ B a b)).mp
  simp only [fieldBaseChangeGeneratorPairInclusion, fieldBaseChangeComponentPairIso,
    asIso_inv, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  simp [fieldBaseChangeComponentPairMap, fieldBaseChangeComponentPairInclusion,
    componentPairExteriorInclusion_eq_map,
    pullback.map, fieldBaseChangeSupportProductSnd, fieldBaseChangeComponentToWhole,
    Category.assoc]

/-- Passing to the actual image presentation leaves the literal pair immersion ideal unchanged. -/
theorem fieldBaseChangeGeneratorPairInclusion_ker :
    (A.fieldBaseChangeGeneratorPairInclusion φ B a b).ker =
      (A.fieldBaseChangeComponentPairInclusion φ B a b).ker := by
  unfold fieldBaseChangeGeneratorPairInclusion
  exact Scheme.Hom.ker_comp_of_isIso _ _

/-- The actual component-generator incidence maps to the full new incidence. -/
def fieldBaseChangeComponentIncidenceToWhole :
    (A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b) ⟶ A.fieldBaseChangeIncidence φ B :=
  pullback.map _ _ _ _ (A.fieldBaseChangeComponentToWhole φ a)
    (B.fieldBaseChangeComponentToWhole φ b) (𝟙 ((SmoothSite.fieldBaseChange φ).obj Y).left)
    (by simp) (by simp)

instance fieldBaseChangeComponentIncidenceToWhole_isClosedImmersion :
    IsClosedImmersion (A.fieldBaseChangeComponentIncidenceToWhole φ B a b) := by
  unfold fieldBaseChangeComponentIncidenceToWhole
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion)
    inferInstance inferInstance (by simp) (by simp)

@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentIncidenceToWhole_fst :
    A.fieldBaseChangeComponentIncidenceToWhole φ B a b ≫ A.fieldBaseChangeIncidenceFst φ B =
      (A.fieldBaseChangeComponentGenerator φ a).incidenceFst
        (B.fieldBaseChangeComponentGenerator φ b) ≫ A.fieldBaseChangeComponentToWhole φ a :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentIncidenceToWhole_snd :
    A.fieldBaseChangeComponentIncidenceToWhole φ B a b ≫ A.fieldBaseChangeIncidenceSnd φ B =
      (A.fieldBaseChangeComponentGenerator φ a).incidenceSnd
        (B.fieldBaseChangeComponentGenerator φ b) ≫ B.fieldBaseChangeComponentToWhole φ b :=
  pullback.lift_snd _ _ _

/-- The two embeddings preserve the exact whole coefficient-product point. -/
@[reassoc]
theorem fieldBaseChangeComponentIncidenceToWhole_support :
    A.fieldBaseChangeComponentIncidenceToWhole φ B a b ≫
        A.fieldBaseChangeIncidenceToSupportProduct φ B =
      (A.fieldBaseChangeComponentGenerator φ a).incidenceToSupportProduct
          (B.fieldBaseChangeComponentGenerator φ b) ≫
        A.fieldBaseChangeGeneratorPairInclusion φ B a b := by
  apply pullback.hom_ext <;> simp

/-- The actual generator incidence is the Cartesian pullback of the whole incidence
along the actual closed component-pair product. -/
theorem fieldBaseChangeComponentIncidence_isPullback :
    IsPullback (A.fieldBaseChangeComponentIncidenceToWhole φ B a b)
      ((A.fieldBaseChangeComponentGenerator φ a).incidenceToSupportProduct
        (B.fieldBaseChangeComponentGenerator φ b))
      (A.fieldBaseChangeIncidenceToSupportProduct φ B)
      (A.fieldBaseChangeGeneratorPairInclusion φ B a b) where
  w := A.fieldBaseChangeComponentIncidenceToWhole_support φ B a b
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    let A' := A.fieldBaseChangeComponentGenerator φ a
    let B' := B.fieldBaseChangeComponentGenerator φ b
    have ha := congrArg (fun f => f ≫ A.fieldBaseChangeSupportProductFst φ B) s.condition
    have hb := congrArg (fun f => f ≫ A.fieldBaseChangeSupportProductSnd φ B) s.condition
    simp only [Category.assoc, fieldBaseChangeIncidenceToSupportProduct_fst,
      fieldBaseChangeGeneratorPairInclusion_fst] at ha
    simp only [Category.assoc, fieldBaseChangeIncidenceToSupportProduct_snd,
      fieldBaseChangeGeneratorPairInclusion_snd] at hb
    have hc :
        (s.snd ≫ pullback.fst (A'.targetProjection ≫ ((SmoothSite.fieldBaseChange φ).obj Y).hom)
          (B'.projection ≫ ((SmoothSite.fieldBaseChange φ).obj Y).hom)) ≫ A'.targetProjection =
        (s.snd ≫ pullback.snd (A'.targetProjection ≫ ((SmoothSite.fieldBaseChange φ).obj Y).hom)
          (B'.projection ≫ ((SmoothSite.fieldBaseChange φ).obj Y).hom)) ≫ B'.projection := by
      calc
        _ = s.fst ≫ A.fieldBaseChangeIncidenceFst φ B ≫
            A.fieldBaseChangeTargetProjection φ := by
          simpa only [Category.assoc, fieldBaseChangeComponentToWhole_targetProjection] using
            congrArg (· ≫ A.fieldBaseChangeTargetProjection φ) ha.symm
        _ = s.fst ≫ A.fieldBaseChangeIncidenceSnd φ B ≫
            B.fieldBaseChangeProjection φ := by rw [pullback.condition]
        _ = _ := by
          simpa only [Category.assoc, fieldBaseChangeComponentToWhole_projection] using
            congrArg (· ≫ B.fieldBaseChangeProjection φ) hb
    let m : s.pt ⟶ A'.incidence B' := pullback.lift
      (s.snd ≫ pullback.fst _ _) (s.snd ≫ pullback.snd _ _) hc
    have hm₁ : m ≫ A.fieldBaseChangeComponentIncidenceToWhole φ B a b = s.fst := by
      apply pullback.hom_ext
      · simpa only [Category.assoc, fieldBaseChangeComponentIncidenceToWhole_fst,
          m, A', B', incidenceFst, fieldBaseChangeIncidenceFst,
          pullback.lift_fst_assoc] using ha.symm
      · simpa only [Category.assoc, fieldBaseChangeComponentIncidenceToWhole_snd,
          m, A', B', incidenceSnd, fieldBaseChangeIncidenceSnd,
          pullback.lift_snd_assoc] using hb.symm
    have hm₂ : m ≫ A'.incidenceToSupportProduct B' = s.snd := by
      apply pullback.hom_ext <;> simp [m, A', B']
    refine ⟨m, hm₁, hm₂, ?_⟩
    intro t _ ht
    apply pullback.hom_ext (f := A'.targetProjection) (g := B'.projection)
    · simpa only [PullbackCone.mk_snd, A', B', Category.assoc,
        incidenceToSupportProduct_fst, incidenceFst] using
        congrArg (fun f => f ≫ pullback.fst _ _) (ht.trans hm₂.symm)
    · simpa only [PullbackCone.mk_snd, A', B', Category.assoc,
        incidenceToSupportProduct_snd, incidenceSnd] using
        congrArg (fun f => f ≫ pullback.snd _ _) (ht.trans hm₂.symm))⟩

/-- The actual finite whole-incidence projection to the new source. -/
abbrev fieldBaseChangeIncidenceSource : A.fieldBaseChangeIncidence φ B ⟶
    ((SmoothSite.fieldBaseChange φ).obj X).left :=
  A.fieldBaseChangeIncidenceFst φ B ≫ A.fieldBaseChangeProjection φ

instance fieldBaseChangeIncidenceSource_isFinite :
    IsFinite (A.fieldBaseChangeIncidenceSource φ B) :=
  inferInstanceAs (IsFinite (A.fieldBaseChangeIncidenceFst φ B ≫ A.fieldBaseChangeProjection φ))

@[reassoc (attr := simp)]
theorem fieldBaseChangeComponentIncidenceToWhole_source :
    A.fieldBaseChangeComponentIncidenceToWhole φ B a b ≫ A.fieldBaseChangeIncidenceSource φ B =
      (A.fieldBaseChangeComponentGenerator φ a).incidenceSource
        (B.fieldBaseChangeComponentGenerator φ b) := by
  simp only [fieldBaseChangeIncidenceSource, fieldBaseChangeComponentIncidenceToWhole_fst_assoc,
    fieldBaseChangeComponentToWhole_projection, incidenceSource]

/-- Admissibility proves generic preservation in the actual whole incidence. -/
theorem fieldBaseChangeComponentIncidenceToWhole_generic
    (v : genericPoints ((A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b))) :
    A.fieldBaseChangeComponentIncidenceToWhole φ B a b v.1 ∈
      genericPoints (A.fieldBaseChangeIncidence φ B) := by
  apply mem_genericPoints_of_image_generic (A.fieldBaseChangeIncidenceSource φ B)
  rw [← Scheme.Hom.comp_apply, fieldBaseChangeComponentIncidenceToWhole_source]
  exact (A.fieldBaseChangeComponentGenerator φ a).incidenceSource_mem_genericPoints L
    (B.fieldBaseChangeComponentGenerator φ b) v.1 v.2

/-- A whole generic lies on the pair support exactly when it has a generic incidence lift. -/
theorem fieldBaseChangeComponentIncidence_exists_generic_iff
    (w : genericPoints (A.fieldBaseChangeIncidence φ B)) :
    (∃ v : genericPoints ((A.fieldBaseChangeComponentGenerator φ a).incidence
        (B.fieldBaseChangeComponentGenerator φ b)),
      A.fieldBaseChangeComponentIncidenceToWhole φ B a b v.1 = w.1) ↔
    A.fieldBaseChangeIncidenceToSupportProduct φ B w.1 ∈
      Set.range (A.fieldBaseChangeGeneratorPairInclusion φ B a b) := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨(A.fieldBaseChangeComponentGenerator φ a).incidenceToSupportProduct
      (B.fieldBaseChangeComponentGenerator φ b) v.1, ?_⟩
    exact (congrArg (fun f => f v.1)
      (A.fieldBaseChangeComponentIncidenceToWhole_support φ B a b)).symm.trans
        (congrArg (A.fieldBaseChangeIncidenceToSupportProduct φ B) hv)
  · rintro ⟨e, he⟩
    obtain ⟨v, hv, -⟩ := Scheme.exists_preimage_of_isPullback
      (A.fieldBaseChangeComponentIncidence_isPullback φ B a b) w.1 e he.symm
    refine ⟨⟨v, ?_⟩, hv⟩
    exact mem_genericPoints_of_image_generic
      (A.fieldBaseChangeComponentIncidenceToWhole φ B a b) v (hv.symm ▸ w.2)

/-- An absent actual incidence lift forces the literal unreduced pair ideal to be the unit ideal. -/
theorem fieldBaseChangePair_ker_stalk_eq_top_of_no_lift
    (w : genericPoints (A.fieldBaseChangeIncidence φ B))
    (hno : ¬ ∃ v : genericPoints ((A.fieldBaseChangeComponentGenerator φ a).incidence
        (B.fieldBaseChangeComponentGenerator φ b)),
      A.fieldBaseChangeComponentIncidenceToWhole φ B a b v.1 = w.1) :
    (A.fieldBaseChangeComponentPairInclusion φ B a b).ker.stalk
      (A.fieldBaseChangeIncidenceToSupportProduct φ B w.1) = ⊤ := by
  rw [← A.fieldBaseChangeGeneratorPairInclusion_ker φ B a b]
  apply closedImmersion_ker_stalk_eq_top
  exact fun h => hno ((A.fieldBaseChangeComponentIncidence_exists_generic_iff φ B a b w).mpr h)

/-- The actual new generator-pair middle map retains both original middle coordinates. -/
@[reassoc]
theorem fieldBaseChangeGeneratorPairInclusion_middle :
    A.fieldBaseChangeGeneratorPairInclusion φ B a b ≫
        A.fieldBaseChangeSupportProductToOriginal φ B ≫ A.originalCoefficientMiddlePair B =
      (A.fieldBaseChangeComponentGenerator φ a).originalCoefficientMiddlePair
          (B.fieldBaseChangeComponentGenerator φ b) ≫
        SmoothSite.fieldBaseChangePairProjection φ Y := by
  apply pullback.hom_ext
  · simp only [Category.assoc, originalCoefficientMiddlePair_fst,
      fieldBaseChangeSupportProductToOriginal_fst_assoc,
      fieldBaseChangeGeneratorPairInclusion_fst_assoc,
      SmoothSite.fieldBaseChangePairProjection_fst]
    rw [← fieldBaseChangeTargetProjection_fst,
      fieldBaseChangeComponentToWhole_targetProjection_assoc,
      originalCoefficientMiddlePair_fst_assoc]
  · simp only [Category.assoc, originalCoefficientMiddlePair_snd,
      fieldBaseChangeSupportProductToOriginal_snd_assoc,
      fieldBaseChangeGeneratorPairInclusion_snd_assoc,
      SmoothSite.fieldBaseChangePairProjection_snd]
    rw [← fieldBaseChangeProjection_fst, fieldBaseChangeComponentToWhole_projection_assoc,
      originalCoefficientMiddlePair_snd_assoc]

/-- The old middle coordinate of the whole-incidence image is the actual old coordinate
of the component-generator incidence's new middle point. -/
@[reassoc]
theorem fieldBaseChangeComponentIncidenceToWhole_middle :
    A.fieldBaseChangeComponentIncidenceToWhole φ B a b ≫
        A.fieldBaseChangeIncidenceToOriginal φ B ≫ A.incidenceInclusion B ≫
          correspondenceTripleMiddle X.hom Y.hom Z.hom =
      (A.fieldBaseChangeComponentGenerator φ a).incidenceInclusion
          (B.fieldBaseChangeComponentGenerator φ b) ≫
        correspondenceTripleMiddle ((SmoothSite.fieldBaseChange φ).obj X).hom
          ((SmoothSite.fieldBaseChange φ).obj Y).hom ((SmoothSite.fieldBaseChange φ).obj Z).hom ≫
        pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)) := by
  simp only [correspondenceTripleMiddle, Category.assoc, incidenceInclusion_fst_assoc]
  change _ ≫ A.fieldBaseChangeIncidenceToOriginal φ B ≫ A.incidenceFst B ≫ A.targetProjection =
    (A.fieldBaseChangeComponentGenerator φ a).incidenceFst
      (B.fieldBaseChangeComponentGenerator φ b) ≫
      (A.fieldBaseChangeComponentGenerator φ a).targetProjection ≫ _
  rw [fieldBaseChangeIncidenceToOriginal_fst_assoc,
    fieldBaseChangeComponentIncidenceToWhole_fst_assoc,
    ← fieldBaseChangeTargetProjection_fst, fieldBaseChangeComponentToWhole_targetProjection_assoc]
  rfl

/-- The actual component incidence is also Cartesian over the original middle diagonal. -/
theorem fieldBaseChangeComponent_middle_isPullback :
    IsPullback
      ((A.fieldBaseChangeComponentGenerator φ a).incidenceInclusion
          (B.fieldBaseChangeComponentGenerator φ b) ≫
        correspondenceTripleMiddle ((SmoothSite.fieldBaseChange φ).obj X).hom
          ((SmoothSite.fieldBaseChange φ).obj Y).hom ((SmoothSite.fieldBaseChange φ).obj Z).hom ≫
        pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)))
      ((A.fieldBaseChangeComponentGenerator φ a).incidenceToSupportProduct
        (B.fieldBaseChangeComponentGenerator φ b)) (pullback.diagonal Y.hom)
      ((A.fieldBaseChangeComponentGenerator φ a).originalCoefficientMiddlePair
          (B.fieldBaseChangeComponentGenerator φ b) ≫
        SmoothSite.fieldBaseChangePairProjection φ Y) :=
  ((A.fieldBaseChangeComponentGenerator φ a).originalIncidence_middle_isPullback
    (B.fieldBaseChangeComponentGenerator φ b)).paste_horiz
      (SmoothSite.fieldBaseChangeDiagonal_isPullback φ Y)

/-- The actual new middle coordinate in a component-generator incidence. -/
abbrev fieldBaseChangeComponentMiddle
    (v : (A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b)) :=
  correspondenceTripleMiddle ((SmoothSite.fieldBaseChange φ).obj X).hom
    ((SmoothSite.fieldBaseChange φ).obj Y).hom ((SmoothSite.fieldBaseChange φ).obj Z).hom
    ((A.fieldBaseChangeComponentGenerator φ a).incidenceInclusion
      (B.fieldBaseChangeComponentGenerator φ b) v)

/-- The component middle and the whole-incidence old middle are the same actual point. -/
theorem fieldBaseChangeComponentMiddle_eq
    (v : (A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b)) :
    A.fieldBaseChangeIncidenceMiddle φ B
        (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v) =
      pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ))
        (A.fieldBaseChangeComponentMiddle φ B a b v) :=
  congrArg (fun f => f v) (A.fieldBaseChangeComponentIncidenceToWhole_middle φ B a b)

/-- An explicit original middle point retains its canonical coefficient scalar map. -/
def fieldBaseChangeComponentMiddleStalkMap
    (v : (A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b)) (y : Y.left)
    (hy : y = pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ))
      (A.fieldBaseChangeComponentMiddle φ B a b v)) :
    (pullback Y.hom Y.hom).presheaf.stalk (pullback.diagonal Y.hom y) ⟶
      ((A.fieldBaseChangeComponentGenerator φ a).supportProduct
        (B.fieldBaseChangeComponentGenerator φ b)).presheaf.stalk
        ((A.fieldBaseChangeComponentGenerator φ a).incidenceToSupportProduct
          (B.fieldBaseChangeComponentGenerator φ b) v) :=
  StalkTransport.pointedMap
    ((A.fieldBaseChangeComponentGenerator φ a).originalCoefficientMiddlePair
        (B.fieldBaseChangeComponentGenerator φ b) ≫ SmoothSite.fieldBaseChangePairProjection φ Y)
    _ _ ((congrArg (pullback.diagonal Y.hom) hy).trans
      (congrArg (fun f => f v) (A.fieldBaseChangeComponent_middle_isPullback φ B a b).w))

/-- The original/new middle scalar route gives the literal component coefficient list. -/
theorem fieldBaseChangeComponentMiddleList_eq
    (v : (A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ))
        (A.fieldBaseChangeComponentMiddle φ B a b v))))) :
    (s.map (SmoothSite.fieldBaseChangeDiagonalStalkMap φ Y
      (A.fieldBaseChangeComponentMiddle φ B a b v)).hom).map
        (Diagonal.baseChangeStalkMap
          ((A.fieldBaseChangeComponentGenerator φ a).originalIncidence_middle_isPullback
            (B.fieldBaseChangeComponentGenerator φ b)) v).hom =
      s.map (A.fieldBaseChangeComponentMiddleStalkMap φ B a b v _ rfl).hom := by
  have hmaps :
      SmoothSite.fieldBaseChangeDiagonalStalkMap φ Y
          (A.fieldBaseChangeComponentMiddle φ B a b v) ≫
        Diagonal.baseChangeStalkMap
          ((A.fieldBaseChangeComponentGenerator φ a).originalIncidence_middle_isPullback
            (B.fieldBaseChangeComponentGenerator φ b)) v =
      A.fieldBaseChangeComponentMiddleStalkMap φ B a b v _ rfl :=
    StalkTransport.pointedMap_comp _ _ _ _ _
      (congrArg (fun f => f v)
        ((A.fieldBaseChangeComponentGenerator φ a).originalIncidence_middle_isPullback
          (B.fieldBaseChangeComponentGenerator φ b)).w)
      (congrArg (fun f => f (A.fieldBaseChangeComponentMiddle φ B a b v))
        (SmoothSite.fieldBaseChangeDiagonal_isPullback φ Y).w)
  simp only [List.map_map]
  congr 1
  funext r
  exact ConcreteCategory.congr_hom hmaps r

/-- Transport of the original middle list computes every actual new generator Tor degree. -/
theorem fieldBaseChangeComponentTor_length_at_oldMiddle
    (v : (A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b)) (y : Y.left)
    (hy : y = pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ))
      (A.fieldBaseChangeComponentMiddle φ B a b v))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk (pullback.diagonal Y.hom y)))
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk (pullback.diagonal Y.hom y)) s)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap y).hom = Ideal.ofList s) (n : ℕ) :
    Module.length
      ((A.fieldBaseChangeComponentGenerator φ a).incidenceAmbientStalk
        (B.fieldBaseChangeComponentGenerator φ b) v)
      ((A.fieldBaseChangeComponentGenerator φ a).incidenceTor
        (B.fieldBaseChangeComponentGenerator φ b) v n) =
      Module.length
        (((A.fieldBaseChangeComponentGenerator φ a).supportProduct
          (B.fieldBaseChangeComponentGenerator φ b)).presheaf.stalk
          ((A.fieldBaseChangeComponentGenerator φ a).incidenceToSupportProduct
            (B.fieldBaseChangeComponentGenerator φ b) v))
        ((_root_.ChainComplex.Koszul.coefficientComplex (ModuleCat.of
          (((A.fieldBaseChangeComponentGenerator φ a).supportProduct
            (B.fieldBaseChangeComponentGenerator φ b)).presheaf.stalk
            ((A.fieldBaseChangeComponentGenerator φ a).incidenceToSupportProduct
              (B.fieldBaseChangeComponentGenerator φ b) v))
          (((A.fieldBaseChangeComponentGenerator φ a).supportProduct
            (B.fieldBaseChangeComponentGenerator φ b)).presheaf.stalk
            ((A.fieldBaseChangeComponentGenerator φ a).incidenceToSupportProduct
              (B.fieldBaseChangeComponentGenerator φ b) v)))
          (s.map (A.fieldBaseChangeComponentMiddleStalkMap φ B a b v y hy).hom)).homology n) := by
  subst y
  obtain ⟨hs', hker'⟩ := SmoothSite.fieldBaseChangeDiagonal_regular_kernel φ Y
    (A.fieldBaseChangeComponentMiddle φ B a b v) s hs hker
  refine ((A.fieldBaseChangeComponentGenerator φ a).incidenceTor_length_eq_middleKoszul
    (k := L) (X := (SmoothSite.fieldBaseChange φ).obj X)
    (Y := (SmoothSite.fieldBaseChange φ).obj Y) (Z := (SmoothSite.fieldBaseChange φ).obj Z)
    (B.fieldBaseChangeComponentGenerator φ b) v
    (s.map (SmoothSite.fieldBaseChangeDiagonalStalkMap φ Y
      (A.fieldBaseChangeComponentMiddle φ B a b v)).hom) hs' hker' n).trans ?_
  let R := ((A.fieldBaseChangeComponentGenerator φ a).supportProduct
    (B.fieldBaseChangeComponentGenerator φ b)).presheaf.stalk
    ((A.fieldBaseChangeComponentGenerator φ a).incidenceToSupportProduct
      (B.fieldBaseChangeComponentGenerator φ b) v)
  exact congrArg (fun t : List R =>
    Module.length R ((_root_.ChainComplex.Koszul.coefficientComplex (ModuleCat.of R R) t).homology
        n))
    (A.fieldBaseChangeComponentMiddleList_eq φ B a b v s)

/-- The original whole and component scalar routes commute at the actual incidence point. -/
theorem fieldBaseChangeComponentMiddleStalkMap_square
    (v : (A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b)) :
    Diagonal.baseChangeStalkMap (A.fieldBaseChangeIncidence_middle_isPullback φ B)
        (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v) ≫
      Diagonal.baseChangeStalkMap (A.fieldBaseChangeComponentIncidence_isPullback φ B a b) v =
    A.fieldBaseChangeComponentMiddleStalkMap φ B a b v
      (A.fieldBaseChangeIncidenceMiddle φ B
        (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v))
      (A.fieldBaseChangeComponentMiddle_eq φ B a b v) := by
  change StalkTransport.pointedMap
      (A.fieldBaseChangeSupportProductToOriginal φ B ≫ A.originalCoefficientMiddlePair B) _ _
      (congrArg (fun f => f (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v))
        (A.fieldBaseChangeIncidence_middle_isPullback φ B).w) ≫
    StalkTransport.pointedMap (A.fieldBaseChangeGeneratorPairInclusion φ B a b) _ _
      (congrArg (fun f => f v) (A.fieldBaseChangeComponentIncidence_isPullback φ B a b).w) = _
  rw [StalkTransport.pointedMap_comp]
  exact StalkTransport.pointedMap_congr _ _
    (A.fieldBaseChangeGeneratorPairInclusion_middle φ B a b) _ _ _ _

private theorem fieldBaseChangeClosedQuotientKoszul_length {E P : Scheme.{u}}
    (j : E ⟶ P) [IsClosedImmersion j] (e : E) (x : P) (hx : x = j e)
    (s : List (P.presheaf.stalk x)) (n : ℕ) :
    Module.length (P.presheaf.stalk x)
      ((_root_.ChainComplex.Koszul.coefficientComplex
        (ModuleCat.of (P.presheaf.stalk x) ((P.presheaf.stalk x) ⧸ j.ker.stalk x)) s).homology n) =
      Module.length (E.presheaf.stalk e)
        ((_root_.ChainComplex.Koszul.coefficientComplex (ModuleCat.of (E.presheaf.stalk e)
            (E.presheaf.stalk e))
          (s.map (StalkTransport.pointedMap j e x hx).hom)).homology n) := by
  subst x
  rw [StalkTransport.pointedMap_image]
  let eQ := (Hom.closedStalkQuotientLinearEquiv j e).toModuleIso
  let eK := (_root_.ChainComplex.Koszul.coefficientFunctor s).mapIso eQ
  have hlen := ((HomologicalComplex.homologyFunctor
    (ModuleCat (P.presheaf.stalk (j e))) (ComplexShape.down ℕ) n).mapIso eK).toLinearEquiv.length_eq
  exact hlen.trans (_root_.ChainComplex.Koszul.coefficientRestrict_length
    (j.stalkMap e).hom (j.stalkMap_surjective e) (ModuleCat.of (E.presheaf.stalk e)
      (E.presheaf.stalk e)) s n)

/-- The exact core Euler-sum term, before any coefficient-point or support replacement. -/
abbrev fieldBaseChangePairQuotientKoszul (w : A.fieldBaseChangeIncidence φ B)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w)))) :=
  _root_.ChainComplex.Koszul.coefficientComplex
    (ModuleCat.of ((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
        (A.fieldBaseChangeIncidenceToSupportProduct φ B w))
      (((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
        (A.fieldBaseChangeIncidenceToSupportProduct φ B w)) ⧸
          (A.fieldBaseChangeComponentPairInclusion φ B a b).ker.stalk
            (A.fieldBaseChangeIncidenceToSupportProduct φ B w)))
    (A.fieldBaseChangeMiddleList φ B w s)

/-- The whole-incidence Artinian cut proves finiteness for every actual component-pair quotient. -/
theorem fieldBaseChangePairQuotientKoszul_finiteHomology
    (w : genericPoints (A.fieldBaseChangeIncidence φ B))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))))
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w.1)).hom = Ideal.ofList s) :
    _root_.HomologicalComplex.ModuleLengthEuler.FiniteHomology (A.fieldBaseChangePairQuotientKoszul
        φ B a b w.1 s) := by
  have := A.fieldBaseChangeMiddleList_support_isArtinian φ B w s hker
  exact _root_.ChainComplex.Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥
      bot_le

/-- The exact Euler term on the unreduced pair immersion's literal kernel quotient. -/
def fieldBaseChangePairQuotientEuler
    (w : genericPoints (A.fieldBaseChangeIncidence φ B))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))))
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w.1)).hom = Ideal.ofList s) : ℤ :=
  _root_.HomologicalComplex.ModuleLengthEuler.chainEuler (A.fieldBaseChangePairQuotientKoszul φ B a
      b w.1 s)
    (A.fieldBaseChangePairQuotientKoszul_finiteHomology φ B a b w s hker)

/-- Without an actual generic incidence lift the same-list pair quotient Euler is zero. -/
theorem fieldBaseChangePairQuotientEuler_eq_zero_of_no_lift
    (w : genericPoints (A.fieldBaseChangeIncidence φ B))
    (hno : ¬ ∃ v : genericPoints ((A.fieldBaseChangeComponentGenerator φ a).incidence
        (B.fieldBaseChangeComponentGenerator φ b)),
      A.fieldBaseChangeComponentIncidenceToWhole φ B a b v.1 = w.1)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))))
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w.1)).hom = Ideal.ofList s) :
    A.fieldBaseChangePairQuotientEuler φ B a b w s hker = 0 := by
  have : Subsingleton
      (((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
        (A.fieldBaseChangeIncidenceToSupportProduct φ B w.1)) ⧸
          (A.fieldBaseChangeComponentPairInclusion φ B a b).ker.stalk
            (A.fieldBaseChangeIncidenceToSupportProduct φ B w.1)) :=
    Ideal.Quotient.subsingleton_iff.mpr
      (A.fieldBaseChangePair_ker_stalk_eq_top_of_no_lift φ B a b w hno)
  exact _root_.ChainComplex.Koszul.koszulDimension_chainEuler_zero_of_subsingleton _ _ _

/-- At an actual lift, every quotient-Koszul degree equals the actual new generator Tor degree. -/
theorem fieldBaseChangePairQuotientKoszul_length_at_lift
    (v : (A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B
        (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v)))))
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B
        (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v)))) s)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B
        (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v))).hom = Ideal.ofList s) (n : ℕ) :
    Module.length ((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
      (A.fieldBaseChangeIncidenceToSupportProduct φ B
        (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v)))
      ((A.fieldBaseChangePairQuotientKoszul φ B a b
        (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v) s).homology n) =
      Module.length
        ((A.fieldBaseChangeComponentGenerator φ a).incidenceAmbientStalk
          (B.fieldBaseChangeComponentGenerator φ b) v)
        ((A.fieldBaseChangeComponentGenerator φ a).incidenceTor
          (B.fieldBaseChangeComponentGenerator φ b) v n) := by
  have hlen := fieldBaseChangeClosedQuotientKoszul_length
    (A.fieldBaseChangeGeneratorPairInclusion φ B a b)
    ((A.fieldBaseChangeComponentGenerator φ a).incidenceToSupportProduct
      (B.fieldBaseChangeComponentGenerator φ b) v)
    (A.fieldBaseChangeIncidenceToSupportProduct φ B
      (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v))
    (congrArg (fun f => f v) (A.fieldBaseChangeComponentIncidenceToWhole_support φ B a b))
    (A.fieldBaseChangeMiddleList φ B
      (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v) s) n
  rw [A.fieldBaseChangeGeneratorPairInclusion_ker φ B a b] at hlen
  refine hlen.trans ?_
  have hlists :
      (A.fieldBaseChangeMiddleList φ B
        (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v) s).map
        (Diagonal.baseChangeStalkMap
          (A.fieldBaseChangeComponentIncidence_isPullback φ B a b) v).hom =
      s.map (A.fieldBaseChangeComponentMiddleStalkMap φ B a b v
        (A.fieldBaseChangeIncidenceMiddle φ B
          (A.fieldBaseChangeComponentIncidenceToWhole φ B a b v))
        (A.fieldBaseChangeComponentMiddle_eq φ B a b v)).hom := by
    simp only [fieldBaseChangeMiddleList, List.map_map]
    congr 1
    funext r
    exact ConcreteCategory.congr_hom
      (A.fieldBaseChangeComponentMiddleStalkMap_square φ B a b v) r
  let R := ((A.fieldBaseChangeComponentGenerator φ a).supportProduct
    (B.fieldBaseChangeComponentGenerator φ b)).presheaf.stalk
    ((A.fieldBaseChangeComponentGenerator φ a).incidenceToSupportProduct
      (B.fieldBaseChangeComponentGenerator φ b) v)
  refine (congrArg (fun t : List R =>
    Module.length R ((_root_.ChainComplex.Koszul.coefficientComplex (ModuleCat.of R R) t).homology
        n)) hlists).trans ?_
  exact (A.fieldBaseChangeComponentTor_length_at_oldMiddle φ B a b v _
    (A.fieldBaseChangeComponentMiddle_eq φ B a b v) s hs hker n).symm

/-- At the unique actual generic lift, the fixed-list quotient Euler is the
named new component-generator Tor coefficient, including every higher correction. -/
theorem fieldBaseChangePairQuotientEuler_eq_tor
    (w : genericPoints (A.fieldBaseChangeIncidence φ B))
    (v : genericPoints ((A.fieldBaseChangeComponentGenerator φ a).incidence
      (B.fieldBaseChangeComponentGenerator φ b)))
    (hv : A.fieldBaseChangeComponentIncidenceToWhole φ B a b v.1 = w.1)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))))
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))) s)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w.1)).hom = Ideal.ofList s) :
    A.fieldBaseChangePairQuotientEuler φ B a b w s hker =
      (A.fieldBaseChangeComponentGenerator φ a).incidenceTorCoefficient (S := Spec (.of L))
        (B.fieldBaseChangeComponentGenerator φ b) v := by
  obtain ⟨w, hw⟩ := w
  dsimp only at hv
  subst w
  unfold fieldBaseChangePairQuotientEuler _root_.HomologicalComplex.ModuleLengthEuler.chainEuler
      _root_.HomologicalComplex.ModuleLengthEuler.homologyEuler
    incidenceTorCoefficient _root_.HomologicalComplex.ModuleLengthEuler.signedLengthSum
  apply finsum_congr
  intro n
  simp only [_root_.HomologicalComplex.ModuleLengthEuler.integerLength,
    A.fieldBaseChangePairQuotientKoszul_length_at_lift φ B a b v.1 s hs hker n]

end Motivic.FiniteCorrespondenceGenerator
