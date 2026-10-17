/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.FieldBaseChangeSupport
public import Motivic.AlgebraicGeometry.Correspondences.IncidenceMiddleKoszulLength
public import Motivic.Aglib.AlgebraicGeometry.FlatFundamentalCycle
public import Motivic.Aglib.AlgebraicGeometry.ClosedImmersionKoszulEuler

/-!
# Whole incidence and the original equations under arbitrary field change

The product and incidence below use both whole pulled-back supports. Their
Cartesian projections retain the original middle-diagonal equations and all
nilpotents. No finite-type hypothesis on the extension, separability,
reducedness, or flatness of a support-to-source projection is imposed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingTheory.Sequence

universe u

namespace Motivic.FiniteCorrespondenceGenerator

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {X Y Z : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (B : FiniteCorrespondenceGenerator Y.hom Z.hom)

/-- The literal projection of the whole new support to its original support. -/
abbrev fieldBaseChangeSupportToOriginal : A.fieldBaseChangeSupport φ ⟶ A.scheme :=
  pullback.fst (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ))

/-- The structure map of the whole new support over the new field. -/
abbrev fieldBaseChangeSupportHom : A.fieldBaseChangeSupport φ ⟶ Spec (.of L) :=
  pullback.snd (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ))

/-- The whole support's actual new target projection. -/
def fieldBaseChangeTargetProjection : A.fieldBaseChangeSupport φ ⟶
    ((SmoothSite.fieldBaseChange φ).obj Y).left :=
  pullback.lift (A.fieldBaseChangeSupportToOriginal φ ≫ A.targetProjection)
    (A.fieldBaseChangeSupportHom φ) (by
      rw [Category.assoc, ← A.projection_base]
      exact pullback.condition)

@[reassoc (attr := simp)]
theorem fieldBaseChangeTargetProjection_fst :
    A.fieldBaseChangeTargetProjection φ ≫
      pullback.fst Y.hom (Spec.map (CommRingCat.ofHom φ)) =
        A.fieldBaseChangeSupportToOriginal φ ≫ A.targetProjection :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fieldBaseChangeTargetProjection_snd :
    A.fieldBaseChangeTargetProjection φ ≫
      ((SmoothSite.fieldBaseChange φ).obj Y).hom = A.fieldBaseChangeSupportHom φ :=
  pullback.lift_snd _ _ _

/-- The new whole product is literally the product of the two whole supports over `L`. -/
abbrev fieldBaseChangeSupportProduct : Scheme.{u} :=
  pullback (A.fieldBaseChangeSupportHom φ) (B.fieldBaseChangeSupportHom φ)

/-- The first whole-support coordinate. -/
abbrev fieldBaseChangeSupportProductFst : A.fieldBaseChangeSupportProduct φ B ⟶
    A.fieldBaseChangeSupport φ := pullback.fst _ _

/-- The second whole-support coordinate. -/
abbrev fieldBaseChangeSupportProductSnd : A.fieldBaseChangeSupportProduct φ B ⟶
    B.fieldBaseChangeSupport φ := pullback.snd _ _

/-- The original coordinates on the whole new support product. -/
def fieldBaseChangeSupportProductToOriginal : A.fieldBaseChangeSupportProduct φ B ⟶
    A.supportProduct B :=
  pullback.lift
    (A.fieldBaseChangeSupportProductFst φ B ≫ A.fieldBaseChangeSupportToOriginal φ)
    (A.fieldBaseChangeSupportProductSnd φ B ≫ B.fieldBaseChangeSupportToOriginal φ) (by
      simp only [Category.assoc, ← A.projection_base]
      rw [pullback.condition, pullback.condition, ← Category.assoc, ← Category.assoc]
      exact congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom φ)) pullback.condition)

@[reassoc (attr := simp)]
theorem fieldBaseChangeSupportProductToOriginal_fst :
    A.fieldBaseChangeSupportProductToOriginal φ B ≫
      pullback.fst (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) =
        A.fieldBaseChangeSupportProductFst φ B ≫ A.fieldBaseChangeSupportToOriginal φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fieldBaseChangeSupportProductToOriginal_snd :
    A.fieldBaseChangeSupportProductToOriginal φ B ≫
      pullback.snd (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) =
        A.fieldBaseChangeSupportProductSnd φ B ≫ B.fieldBaseChangeSupportToOriginal φ :=
  pullback.lift_snd _ _ _

/-- The whole new support product is the actual field pullback of the old product. -/
theorem fieldBaseChangeSupportProduct_isPullback :
    IsPullback (A.fieldBaseChangeSupportProductToOriginal φ B)
      (A.fieldBaseChangeSupportProductFst φ B ≫ A.fieldBaseChangeSupportHom φ)
      (pullback.fst (A.targetProjection ≫ Y.hom) (B.projection ≫ Y.hom) ≫
        A.targetProjection ≫ Y.hom) (Spec.map (CommRingCat.ofHom φ)) where
  w := by
    rw [fieldBaseChangeSupportProductToOriginal_fst_assoc]
    simp only [Category.assoc, ← A.projection_base]
    exact congrArg (A.fieldBaseChangeSupportProductFst φ B ≫ ·) pullback.condition
  isLimit' := ⟨PullbackCone.isLimitAux' _ (fun s ↦ by
    let a : s.pt ⟶ A.fieldBaseChangeSupport φ := pullback.lift
      (s.fst ≫ pullback.fst _ _) s.snd (by
        simpa only [Category.assoc, A.projection_base] using s.condition)
    let b : s.pt ⟶ B.fieldBaseChangeSupport φ := pullback.lift
      (s.fst ≫ pullback.snd _ _) s.snd (by
        calc
          _ = s.fst ≫ pullback.fst (A.targetProjection ≫ Y.hom)
              (B.projection ≫ Y.hom) ≫ A.targetProjection ≫ Y.hom := by
            simpa only [Category.assoc] using congrArg (s.fst ≫ ·)
              (pullback.condition (f := A.targetProjection ≫ Y.hom)
                (g := B.projection ≫ Y.hom)).symm
          _ = _ := s.condition)
    let m : s.pt ⟶ A.fieldBaseChangeSupportProduct φ B :=
      pullback.lift a b (by simp [a, b, fieldBaseChangeSupportHom])
    have hm₁ : m ≫ A.fieldBaseChangeSupportProductToOriginal φ B = s.fst := by
      apply pullback.hom_ext <;>
        simp [m, a, b, fieldBaseChangeSupportProductToOriginal,
          fieldBaseChangeSupportToOriginal, fieldBaseChangeSupportProductFst,
          fieldBaseChangeSupportProductSnd]
    have hm₂ : m ≫ (A.fieldBaseChangeSupportProductFst φ B ≫
        A.fieldBaseChangeSupportHom φ) = s.snd := by
      simp [m, a, fieldBaseChangeSupportProductFst, fieldBaseChangeSupportHom]
    refine ⟨m, hm₁, hm₂, ?_⟩
    intro t ht₁ ht₂
    dsimp only [PullbackCone.mk_pt, PullbackCone.mk_fst, PullbackCone.mk_snd] at t ht₁ ht₂
    apply pullback.hom_ext (f := A.fieldBaseChangeSupportHom φ)
      (g := B.fieldBaseChangeSupportHom φ)
    · apply pullback.hom_ext
      · simpa only [Category.assoc, fieldBaseChangeSupportProductToOriginal_fst,
          m, pullback.lift_fst_assoc, a, pullback.lift_fst] using
          congrArg (fun f => f ≫ pullback.fst _ _) ht₁
      · simpa [m, a, fieldBaseChangeSupportProductFst, fieldBaseChangeSupportHom] using ht₂
    · apply pullback.hom_ext
      · simpa only [Category.assoc, fieldBaseChangeSupportProductToOriginal_snd,
          m, pullback.lift_snd_assoc, b, pullback.lift_fst] using
          congrArg (fun f => f ≫ pullback.snd _ _) ht₁
      · simpa only [Category.assoc, m, pullback.lift_snd_assoc, b, pullback.lift_snd,
          ← pullback.condition (f := A.fieldBaseChangeSupportHom φ)
            (g := B.fieldBaseChangeSupportHom φ), fieldBaseChangeSupportProductFst] using ht₂)⟩

/-- The actual whole new incidence, before any component decomposition. -/
abbrev fieldBaseChangeIncidence : Scheme.{u} :=
  pullback (A.fieldBaseChangeTargetProjection φ) (B.fieldBaseChangeProjection φ)

/-- The first whole-support coordinate of the new incidence. -/
abbrev fieldBaseChangeIncidenceFst : A.fieldBaseChangeIncidence φ B ⟶
    A.fieldBaseChangeSupport φ := pullback.fst _ _

/-- The second whole-support coordinate of the new incidence. -/
abbrev fieldBaseChangeIncidenceSnd : A.fieldBaseChangeIncidence φ B ⟶
    B.fieldBaseChangeSupport φ := pullback.snd _ _

/-- Forgetting the new field sends the actual incidence to the actual old incidence. -/
def fieldBaseChangeIncidenceToOriginal : A.fieldBaseChangeIncidence φ B ⟶ A.incidence B :=
  pullback.lift
    (A.fieldBaseChangeIncidenceFst φ B ≫ A.fieldBaseChangeSupportToOriginal φ)
    (A.fieldBaseChangeIncidenceSnd φ B ≫ B.fieldBaseChangeSupportToOriginal φ) (by
      have h := congrArg (fun f => f ≫ pullback.fst Y.hom
        (Spec.map (CommRingCat.ofHom φ))) (pullback.condition
          (f := A.fieldBaseChangeTargetProjection φ) (g := B.fieldBaseChangeProjection φ))
      simpa only [Category.assoc, fieldBaseChangeTargetProjection_fst,
        fieldBaseChangeProjection_fst] using h)

@[reassoc (attr := simp)]
theorem fieldBaseChangeIncidenceToOriginal_fst :
    A.fieldBaseChangeIncidenceToOriginal φ B ≫ A.incidenceFst B =
      A.fieldBaseChangeIncidenceFst φ B ≫ A.fieldBaseChangeSupportToOriginal φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fieldBaseChangeIncidenceToOriginal_snd :
    A.fieldBaseChangeIncidenceToOriginal φ B ≫ A.incidenceSnd B =
      A.fieldBaseChangeIncidenceSnd φ B ≫ B.fieldBaseChangeSupportToOriginal φ :=
  pullback.lift_snd _ _ _

/-- The incidence's first projection is Cartesian over the original first support. -/
theorem fieldBaseChangeIncidence_first_isPullback :
    IsPullback (A.fieldBaseChangeIncidenceToOriginal φ B)
      (A.fieldBaseChangeIncidenceFst φ B) (A.incidenceFst B)
      (A.fieldBaseChangeSupportToOriginal φ) := by
  apply IsPullback.of_right (t := (IsPullback.of_hasPullback A.targetProjection B.projection).flip)
  · simpa only [fieldBaseChangeIncidenceToOriginal_snd,
      Category.assoc, fieldBaseChangeTargetProjection_fst] using
      ((IsPullback.of_hasPullback (A.fieldBaseChangeTargetProjection φ)
        (B.fieldBaseChangeProjection φ)).flip.paste_horiz
          (B.fieldBaseChangeProjection_isPullback φ))
  · exact A.fieldBaseChangeIncidenceToOriginal_fst φ B

/-- The whole new incidence is the actual scalar extension of the whole old incidence. -/
theorem fieldBaseChangeIncidence_isPullback :
    IsPullback (A.fieldBaseChangeIncidenceToOriginal φ B)
      (A.fieldBaseChangeIncidenceFst φ B ≫ A.fieldBaseChangeSupportHom φ)
      (A.incidenceSource B ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)) := by
  simpa only [incidenceSource, Category.assoc] using
    (A.fieldBaseChangeIncidence_first_isPullback φ B).paste_vert
      (IsPullback.of_hasPullback (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)))

/-- The actual closed incidence map into the product of both whole new supports. -/
def fieldBaseChangeIncidenceToSupportProduct : A.fieldBaseChangeIncidence φ B ⟶
    A.fieldBaseChangeSupportProduct φ B :=
  pullback.lift (A.fieldBaseChangeIncidenceFst φ B) (A.fieldBaseChangeIncidenceSnd φ B) (by
    have hB : B.fieldBaseChangeProjection φ ≫ ((SmoothSite.fieldBaseChange φ).obj Y).hom =
        B.fieldBaseChangeSupportHom φ := B.fieldBaseChangeProjection_snd φ
    have h := congrArg (fun f => f ≫ ((SmoothSite.fieldBaseChange φ).obj Y).hom)
      (pullback.condition (f := A.fieldBaseChangeTargetProjection φ)
        (g := B.fieldBaseChangeProjection φ))
    simpa only [Category.assoc, fieldBaseChangeTargetProjection_snd,
      hB] using h)

@[reassoc (attr := simp)]
theorem fieldBaseChangeIncidenceToSupportProduct_fst :
    A.fieldBaseChangeIncidenceToSupportProduct φ B ≫ A.fieldBaseChangeSupportProductFst φ B =
      A.fieldBaseChangeIncidenceFst φ B := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem fieldBaseChangeIncidenceToSupportProduct_snd :
    A.fieldBaseChangeIncidenceToSupportProduct φ B ≫ A.fieldBaseChangeSupportProductSnd φ B =
      A.fieldBaseChangeIncidenceSnd φ B := pullback.lift_snd _ _ _

/-- Both routes retain exactly the original pair of support coordinates. -/
@[reassoc]
theorem fieldBaseChangeIncidenceToSupportProduct_original :
    A.fieldBaseChangeIncidenceToOriginal φ B ≫ A.incidenceToSupportProduct B =
      A.fieldBaseChangeIncidenceToSupportProduct φ B ≫
        A.fieldBaseChangeSupportProductToOriginal φ B := by
  apply pullback.hom_ext <;> simp

/-- The whole incidence closed immersion is the field base change of the old immersion. -/
theorem fieldBaseChangeIncidence_support_isPullback :
    IsPullback (A.fieldBaseChangeIncidenceToOriginal φ B)
      (A.fieldBaseChangeIncidenceToSupportProduct φ B) (A.incidenceToSupportProduct B)
      (A.fieldBaseChangeSupportProductToOriginal φ B) := by
  refine IsPullback.of_bot (t := A.fieldBaseChangeSupportProduct_isPullback φ B) ?_
    (A.fieldBaseChangeIncidenceToSupportProduct_original φ B)
  simpa only [Category.assoc, fieldBaseChangeIncidenceToSupportProduct_fst_assoc,
    incidenceToSupportProduct_fst_assoc, ← A.projection_base, incidenceSource] using
    A.fieldBaseChangeIncidence_isPullback φ B

instance fieldBaseChangeIncidenceToSupportProduct_isClosedImmersion :
    IsClosedImmersion (A.fieldBaseChangeIncidenceToSupportProduct φ B) :=
  MorphismProperty.of_isPullback (A.fieldBaseChangeIncidence_support_isPullback φ B)
    inferInstance

/-- The same original middle diagonal cuts out the entire whole new incidence. -/
theorem fieldBaseChangeIncidence_middle_isPullback :
    IsPullback
      (A.fieldBaseChangeIncidenceToOriginal φ B ≫ A.incidenceInclusion B ≫
        correspondenceTripleMiddle X.hom Y.hom Z.hom)
      (A.fieldBaseChangeIncidenceToSupportProduct φ B) (pullback.diagonal Y.hom)
      (A.fieldBaseChangeSupportProductToOriginal φ B ≫ A.originalCoefficientMiddlePair B) :=
  (A.fieldBaseChangeIncidence_support_isPullback φ B).paste_horiz
    (A.originalIncidence_middle_isPullback B)

local instance fieldBaseChangeIncidence_fieldMap_flat :
    Flat (Spec.map (CommRingCat.ofHom φ)) :=
  Flat.SpecMap_iff.mpr (RingHom.Flat.of_isField (Field.toIsField k) φ)

instance fieldBaseChangeSupportProductToOriginal_flat :
    Flat (A.fieldBaseChangeSupportProductToOriginal φ B) :=
  MorphismProperty.of_isPullback (A.fieldBaseChangeSupportProduct_isPullback φ B).flip
    inferInstance

instance fieldBaseChangeIncidenceToOriginal_flat :
    Flat (A.fieldBaseChangeIncidenceToOriginal φ B) :=
  MorphismProperty.of_isPullback (A.fieldBaseChangeIncidence_isPullback φ B).flip inferInstance

/-- Finite type comes from the new source scheme, never from finite type of `L/k`. -/
instance fieldBaseChangeSupportHom_finiteType :
    LocallyOfFiniteType (A.fieldBaseChangeSupportHom φ) := by
  change LocallyOfFiniteType (pullback.snd (A.projection ≫ X.hom) (Spec.map (CommRingCat.ofHom φ)))
  rw [← A.fieldBaseChangeProjection_snd φ]
  infer_instance

instance fieldBaseChangeSupportProduct_isNoetherian :
    IsNoetherian (A.fieldBaseChangeSupportProduct φ B) :=
  isNoetherian_of_finiteType (A.fieldBaseChangeSupportProductSnd φ B)

instance fieldBaseChangeIncidenceFst_isFinite : IsFinite (A.fieldBaseChangeIncidenceFst φ B) :=
  inferInstanceAs (IsFinite (pullback.fst (A.fieldBaseChangeTargetProjection φ)
    (B.fieldBaseChangeProjection φ)))

instance fieldBaseChangeIncidence_isNoetherian : IsNoetherian (A.fieldBaseChangeIncidence φ B) :=
  isNoetherian_of_finiteType (A.fieldBaseChangeIncidenceFst φ B)

/-- Flatness sends a generic point of the whole new incidence to an old incidence generic. -/
theorem fieldBaseChangeIncidenceToOriginal_generic
    (w : genericPoints (A.fieldBaseChangeIncidence φ B)) :
    A.fieldBaseChangeIncidenceToOriginal φ B w.1 ∈ genericPoints (A.incidence B) :=
  mem_genericPoints_of_generalizing _ (Flat.generalizingMap _) w.1 w.2

/-- The original middle point attached to an actual whole new incidence point. -/
abbrev fieldBaseChangeIncidenceMiddle (w : A.fieldBaseChangeIncidence φ B) :=
  correspondenceTripleMiddle X.hom Y.hom Z.hom
    (A.incidenceInclusion B (A.fieldBaseChangeIncidenceToOriginal φ B w))

/-- The one original diagonal list, with its literal scalar action on the whole new product. -/
def fieldBaseChangeMiddleList (w : A.fieldBaseChangeIncidence φ B)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w)))) :
    List ((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
      (A.fieldBaseChangeIncidenceToSupportProduct φ B w)) :=
  s.map (Diagonal.baseChangeStalkMap (A.fieldBaseChangeIncidence_middle_isPullback φ B) w).hom

/-- The same original equations generate the exact whole-incidence stalk kernel. -/
theorem fieldBaseChangeMiddleList_ideal (w : A.fieldBaseChangeIncidence φ B)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w))))
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w)).hom = Ideal.ofList s) :
    Ideal.ofList (A.fieldBaseChangeMiddleList φ B w s) =
      RingHom.ker ((A.fieldBaseChangeIncidenceToSupportProduct φ B).stalkMap w).hom := by
  rw [Diagonal.baseChange_stalk_kernel (A.fieldBaseChangeIncidence_middle_isPullback φ B) w,
    show RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      ((A.fieldBaseChangeIncidenceToOriginal φ B ≫ A.incidenceInclusion B ≫
        correspondenceTripleMiddle X.hom Y.hom Z.hom) w)).hom = Ideal.ofList s from hker,
    Ideal.map_ofList]
  rfl

/-- Every equation lies in the actual product-stalk maximal ideal. -/
theorem fieldBaseChangeMiddleList_mem_maximalIdeal (w : A.fieldBaseChangeIncidence φ B)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w))))
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w)).hom = Ideal.ofList s) :
    ∀ r ∈ A.fieldBaseChangeMiddleList φ B w s,
      r ∈ IsLocalRing.maximalIdeal ((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
        (A.fieldBaseChangeIncidenceToSupportProduct φ B w)) := by
  have hle := IsLocalRing.le_maximalIdeal
    (RingHom.ker_ne_top ((A.fieldBaseChangeIncidenceToSupportProduct φ B).stalkMap w).hom)
  rw [← A.fieldBaseChangeMiddleList_ideal φ B w s hker] at hle
  exact fun r hr => hle (Ideal.subset_span hr)

/-- The quotient by the same list is the actual incidence stalk, retaining its nilpotents. -/
def fieldBaseChangeMiddleListQuotientEquiv (w : A.fieldBaseChangeIncidence φ B)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w))))
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w)).hom = Ideal.ofList s) :
    ((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
      (A.fieldBaseChangeIncidenceToSupportProduct φ B w)) ⧸
        (Ideal.ofList (A.fieldBaseChangeMiddleList φ B w s) ⊔ ⊥) ≃+*
      (A.fieldBaseChangeIncidence φ B).presheaf.stalk w :=
  (Ideal.quotEquivOfEq (by rw [sup_bot_eq, A.fieldBaseChangeMiddleList_ideal φ B w s hker])).trans
    (stalkQuotientKerEquiv (A.fieldBaseChangeIncidenceToSupportProduct φ B) w)

/-- At a whole-incidence generic, the literal `J = 0` quotient is Artinian. -/
theorem fieldBaseChangeMiddleList_support_isArtinian
    (w : genericPoints (A.fieldBaseChangeIncidence φ B))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))))
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w.1)).hom = Ideal.ofList s) :
    IsArtinianRing (((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
      (A.fieldBaseChangeIncidenceToSupportProduct φ B w.1)) ⧸
        (Ideal.ofList (A.fieldBaseChangeMiddleList φ B w.1 s) ⊔ ⊥)) := by
  rw [sup_bot_eq, A.fieldBaseChangeMiddleList_ideal φ B w.1 s hker]
  exact stalk_quotient_ker_isArtinian (A.fieldBaseChangeIncidenceToSupportProduct φ B) w.1 w.2

/-- The two actual scalar routes send every original equation to the same element. -/
theorem fieldBaseChangeMiddleStalkMap_comp (w : A.fieldBaseChangeIncidence φ B) :
    Diagonal.baseChangeStalkMap (A.originalIncidence_middle_isPullback B)
        (A.fieldBaseChangeIncidenceToOriginal φ B w) ≫
      Diagonal.baseChangeStalkMap (A.fieldBaseChangeIncidence_support_isPullback φ B) w =
    Diagonal.baseChangeStalkMap (A.fieldBaseChangeIncidence_middle_isPullback φ B) w :=
  StalkTransport.pointedMap_comp _ _ _ _ _
    (congrArg (fun f => f w) (A.fieldBaseChangeIncidence_support_isPullback φ B).w)
    (congrArg (fun f => f (A.fieldBaseChangeIncidenceToOriginal φ B w))
      (A.originalIncidence_middle_isPullback B).w)

/-- The whole new product uses the literal image of the one original coefficient list. -/
theorem fieldBaseChangeMiddleList_eq (w : A.fieldBaseChangeIncidence φ B)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w)))) :
    A.fieldBaseChangeMiddleList φ B w s =
      (s.map (Diagonal.baseChangeStalkMap (A.originalIncidence_middle_isPullback B)
        (A.fieldBaseChangeIncidenceToOriginal φ B w)).hom).map
          (Diagonal.baseChangeStalkMap
            (A.fieldBaseChangeIncidence_support_isPullback φ B) w).hom := by
  simp only [fieldBaseChangeMiddleList, List.map_map]
  congr 1
  funext r
  exact (ConcreteCategory.congr_hom (A.fieldBaseChangeMiddleStalkMap_comp φ B w) r).symm

/-- The genuine product and incidence local closed fibers have the same length. -/
theorem fieldBaseChangeIncidence_closedFiber_length (w : A.fieldBaseChangeIncidence φ B) :
    Module.length ((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
        (A.fieldBaseChangeIncidenceToSupportProduct φ B w))
      (Koszul.coefficientClosedFiber (Diagonal.baseChangeStalkMap
        (A.fieldBaseChangeIncidence_support_isPullback φ B) w).hom) =
    Module.length ((A.fieldBaseChangeIncidence φ B).presheaf.stalk w)
      (Koszul.coefficientClosedFiber ((A.fieldBaseChangeIncidenceToOriginal φ B).stalkMap w).hom) :=
  Intersection.exteriorClosedFiber_length (A.fieldBaseChangeIncidenceToOriginal φ B)
    (A.fieldBaseChangeIncidenceToSupportProduct φ B) (A.incidenceToSupportProduct B)
    (A.fieldBaseChangeSupportProductToOriginal φ B)
    (A.fieldBaseChangeIncidence_support_isPullback φ B) w

/-- All degrees of the actual old incidence Tor survive as the same-list whole new
Koszul homology, with the full possibly nonreduced incidence closed-fiber factor. -/
theorem fieldBaseChangeMiddleKoszul_length (w : A.fieldBaseChangeIncidence φ B)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w))))
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w))) s)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w)).hom = Ideal.ofList s) (n : ℕ) :
    Module.length ((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
      (A.fieldBaseChangeIncidenceToSupportProduct φ B w))
      ((Koszul.coefficientComplex
        (ModuleCat.of ((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
            (A.fieldBaseChangeIncidenceToSupportProduct φ B w))
          ((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
            (A.fieldBaseChangeIncidenceToSupportProduct φ B w)))
        (A.fieldBaseChangeMiddleList φ B w s)).homology n) =
      Module.length (A.incidenceAmbientStalk B (A.fieldBaseChangeIncidenceToOriginal φ B w))
        (A.incidenceTor B (A.fieldBaseChangeIncidenceToOriginal φ B w) n) *
      Module.length ((A.fieldBaseChangeIncidence φ B).presheaf.stalk w)
        (Koszul.coefficientClosedFiber
          ((A.fieldBaseChangeIncidenceToOriginal φ B).stalkMap w).hom) := by
  rw [A.fieldBaseChangeMiddleList_eq φ B w s]
  let g := Diagonal.baseChangeStalkMap (A.fieldBaseChangeIncidence_support_isPullback φ B) w
  have hlocal : IsLocalHom g.hom := inferInstanceAs (IsLocalHom
    (StalkTransport.pointedMap (A.fieldBaseChangeSupportProductToOriginal φ B)
      (A.fieldBaseChangeIncidenceToSupportProduct φ B w)
      (A.incidenceToSupportProduct B (A.fieldBaseChangeIncidenceToOriginal φ B w))
      (congrArg (fun f => f w) (A.fieldBaseChangeIncidence_support_isPullback φ B).w)).hom)
  refine (Koszul.regularCoefficientFlat_length g.hom
    (Diagonal.baseChangeStalkMap_flat (A.fieldBaseChangeIncidence_support_isPullback φ B) w)
    (s.map (Diagonal.baseChangeStalkMap (A.originalIncidence_middle_isPullback B)
      (A.fieldBaseChangeIncidenceToOriginal φ B w)).hom) n).trans ?_
  exact congrArg₂ (fun a b : ℕ∞ => a * b)
    (A.incidenceTor_length_eq_middleKoszul B (A.fieldBaseChangeIncidenceToOriginal φ B w)
      s hs hker n).symm (A.fieldBaseChangeIncidence_closedFiber_length φ B w)

/-- The projected generic of the original whole incidence. -/
def fieldBaseChangeIncidenceOriginalGeneric
    (w : genericPoints (A.fieldBaseChangeIncidence φ B)) : genericPoints (A.incidence B) :=
  ⟨A.fieldBaseChangeIncidenceToOriginal φ B w.1,
    A.fieldBaseChangeIncidenceToOriginal_generic φ B w⟩

/-- The actual incidence closed fiber has finite length at a whole-incidence generic. -/
theorem fieldBaseChangeIncidenceFiber_length_ne_top
    (w : genericPoints (A.fieldBaseChangeIncidence φ B)) :
    Module.length ((A.fieldBaseChangeIncidence φ B).presheaf.stalk w.1)
      (Koszul.coefficientClosedFiber
        ((A.fieldBaseChangeIncidenceToOriginal φ B).stalkMap w.1).hom) ≠ ⊤ := by
  have := isArtinianRing_stalk_of_mem_genericPoints w.1 w.2
  exact Module.length_ne_top

/-- The whole local closed-fiber multiplicity, after proving its length finite. -/
def fieldBaseChangeIncidenceFiberMultiplicity
    (w : genericPoints (A.fieldBaseChangeIncidence φ B)) : ℤ :=
  LengthEuler.integerLength
    (Koszul.coefficientClosedFiber
      ((A.fieldBaseChangeIncidenceToOriginal φ B).stalkMap w.1).hom)
    (A.fieldBaseChangeIncidenceFiber_length_ne_top φ B w)

/-- The original middle equations acting on the actual whole new product stalk. -/
abbrev fieldBaseChangeMiddleKoszul (w : A.fieldBaseChangeIncidence φ B)
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w)))) :=
  Koszul.coefficientComplex
    (ModuleCat.of ((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
        (A.fieldBaseChangeIncidenceToSupportProduct φ B w))
      ((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
        (A.fieldBaseChangeIncidenceToSupportProduct φ B w)))
    (A.fieldBaseChangeMiddleList φ B w s)

/-- Finiteness is supplied by the actual generic whole-incidence quotient. -/
theorem fieldBaseChangeMiddleKoszul_finiteHomology
    (w : genericPoints (A.fieldBaseChangeIncidence φ B))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))))
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w.1)).hom = Ideal.ofList s) :
    LengthEuler.FiniteHomology (A.fieldBaseChangeMiddleKoszul φ B w.1 s) := by
  have := A.fieldBaseChangeMiddleList_support_isArtinian φ B w s hker
  exact Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥ bot_le

/-- The same-list whole incidence Euler coefficient, keeping all homology degrees. -/
def fieldBaseChangeMiddleKoszulCoefficient
    (w : genericPoints (A.fieldBaseChangeIncidence φ B))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))))
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w.1)).hom = Ideal.ofList s) : ℤ :=
  LengthEuler.chainEuler (A.fieldBaseChangeMiddleKoszul φ B w.1 s)
    (A.fieldBaseChangeMiddleKoszul_finiteHomology φ B w s hker)

/-- The same-list whole Euler coefficient is the old actual Tor coefficient
multiplied by the whole incidence closed-fiber multiplicity. -/
theorem fieldBaseChangeMiddleKoszulCoefficient_eq
    (w : genericPoints (A.fieldBaseChangeIncidence φ B))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))))
    (hs : IsRegular ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))) s)
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w.1)).hom = Ideal.ofList s) :
    A.fieldBaseChangeMiddleKoszulCoefficient φ B w s hker =
      A.incidenceTorCoefficient (S := Spec (.of k)) B
        (A.fieldBaseChangeIncidenceOriginalGeneric φ B w) *
        A.fieldBaseChangeIncidenceFiberMultiplicity φ B w := by
  unfold fieldBaseChangeMiddleKoszulCoefficient LengthEuler.chainEuler
    incidenceTorCoefficient LengthEuler.signedLengthSum
  rw [finsum_mul]
  apply finsum_congr
  intro n
  simp only [LengthEuler.integerLength, fieldBaseChangeMiddleKoszul,
    A.fieldBaseChangeMiddleKoszul_length φ B w.1 s hs hker n,
    ENat.toNat_mul, Nat.cast_mul, mul_assoc, fieldBaseChangeIncidenceFiberMultiplicity,
    fieldBaseChangeIncidenceOriginalGeneric]

/-- The product of the original reduced support components, with its full scheme structure. -/
abbrev fieldBaseChangeComponentPair
    (a : genericPoints (A.fieldBaseChangeSupport φ))
    (b : genericPoints (B.fieldBaseChangeSupport φ)) : Scheme.{u} :=
  componentPairExterior (A.fieldBaseChangeSupportHom φ) (B.fieldBaseChangeSupportHom φ) a b

/-- The actual closed inclusion of the unreduced component-pair product. -/
abbrev fieldBaseChangeComponentPairInclusion
    (a : genericPoints (A.fieldBaseChangeSupport φ))
    (b : genericPoints (B.fieldBaseChangeSupport φ)) :
    A.fieldBaseChangeComponentPair φ B a b ⟶ A.fieldBaseChangeSupportProduct φ B :=
  componentPairExteriorInclusion (A.fieldBaseChangeSupportHom φ)
    (B.fieldBaseChangeSupportHom φ) a b

instance fieldBaseChangeComponentPair_isNoetherian
    (a : genericPoints (A.fieldBaseChangeSupport φ))
    (b : genericPoints (B.fieldBaseChangeSupport φ)) :
    IsNoetherian (A.fieldBaseChangeComponentPair φ B a b) :=
  isNoetherian_of_finiteType (A.fieldBaseChangeComponentPairInclusion φ B a b)

/-- Both original generic lengths multiply the full component-pair fundamental cycle. -/
theorem fieldBaseChangeSupportProduct_fundamentalCycle :
    let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
    let := IntegralCycle.genericPointFintype (B.fieldBaseChangeSupport φ)
    fundamentalCycle (A.fieldBaseChangeSupportProduct φ B) =
      ∑ a, ∑ b, ((genericMultiplicity a : ℤ) * (genericMultiplicity b : ℤ)) •
        IntegralCycle.finitePushforward (A.fieldBaseChangeComponentPairInclusion φ B a b)
          (fundamentalCycle (A.fieldBaseChangeComponentPair φ B a b)) :=
  fundamentalCycle_product_eq_component_pair_sum
    (A.fieldBaseChangeSupportHom φ) (B.fieldBaseChangeSupportHom φ)

/-- At an actual whole-incidence generic, fixed-support Euler replacement uses
one original list on every literal component-product kernel quotient. -/
theorem fieldBaseChangeMiddleKoszulCoefficient_eq_component_pair_sum
    (w : genericPoints (A.fieldBaseChangeIncidence φ B))
    (s : List ((pullback Y.hom Y.hom).presheaf.stalk
      (pullback.diagonal Y.hom (A.fieldBaseChangeIncidenceMiddle φ B w.1))))
    (hker : RingHom.ker ((pullback.diagonal Y.hom).stalkMap
      (A.fieldBaseChangeIncidenceMiddle φ B w.1)).hom = Ideal.ofList s) :
    let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
    let := IntegralCycle.genericPointFintype (B.fieldBaseChangeSupport φ)
    let := A.fieldBaseChangeMiddleList_support_isArtinian φ B w s hker
    A.fieldBaseChangeMiddleKoszulCoefficient φ B w s hker =
      ∑ a, ∑ b, ((genericMultiplicity a : ℤ) * (genericMultiplicity b : ℤ)) *
        LengthEuler.chainEuler (Koszul.coefficientComplex
          (ModuleCat.of ((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
              (A.fieldBaseChangeIncidenceToSupportProduct φ B w.1))
            (((A.fieldBaseChangeSupportProduct φ B).presheaf.stalk
              (A.fieldBaseChangeIncidenceToSupportProduct φ B w.1)) ⧸
                (A.fieldBaseChangeComponentPairInclusion φ B a b).ker.stalk
                  (A.fieldBaseChangeIncidenceToSupportProduct φ B w.1)))
          (A.fieldBaseChangeMiddleList φ B w.1 s))
          (Koszul.finiteHomology_of_artinian_quotient_of_le_annihilator _ _ ⊥ bot_le) := by
  classical
  let := IntegralCycle.genericPointFintype (A.fieldBaseChangeSupport φ)
  let := IntegralCycle.genericPointFintype (B.fieldBaseChangeSupport φ)
  let := A.fieldBaseChangeMiddleList_support_isArtinian φ B w s hker
  have hcycle : fundamentalCycle (A.fieldBaseChangeSupportProduct φ B) =
      ∑ ab : genericPoints (A.fieldBaseChangeSupport φ) ×
          genericPoints (B.fieldBaseChangeSupport φ),
        ((genericMultiplicity ab.1 : ℤ) * (genericMultiplicity ab.2 : ℤ)) •
          IntegralCycle.finitePushforward
            (A.fieldBaseChangeComponentPairInclusion φ B ab.1 ab.2)
            (fundamentalCycle (A.fieldBaseChangeComponentPair φ B ab.1 ab.2)) := by
    simpa only [Fintype.sum_prod_type] using A.fieldBaseChangeSupportProduct_fundamentalCycle φ B
  simpa only [Fintype.sum_prod_type, fieldBaseChangeMiddleKoszulCoefficient,
    fieldBaseChangeMiddleKoszul] using
    chainEuler_eq_sum_of_fundamentalCycle_eq
      (fun ab : genericPoints (A.fieldBaseChangeSupport φ) ×
          genericPoints (B.fieldBaseChangeSupport φ) =>
        A.fieldBaseChangeComponentPair φ B ab.1 ab.2)
      (fun ab : genericPoints (A.fieldBaseChangeSupport φ) ×
          genericPoints (B.fieldBaseChangeSupport φ) =>
        A.fieldBaseChangeComponentPairInclusion φ B ab.1 ab.2)
      (fun ab : genericPoints (A.fieldBaseChangeSupport φ) ×
          genericPoints (B.fieldBaseChangeSupport φ) =>
        (genericMultiplicity ab.1 : ℤ) * (genericMultiplicity ab.2 : ℤ))
      hcycle (A.fieldBaseChangeIncidenceToSupportProduct φ B w.1)
      (A.fieldBaseChangeMiddleList φ B w.1 s)
      (A.fieldBaseChangeMiddleList_mem_maximalIdeal φ B w.1 s hker)

end Motivic.FiniteCorrespondenceGenerator
