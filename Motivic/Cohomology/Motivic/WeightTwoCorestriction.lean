/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoSymbols
public import Motivic.Cohomology.Motivic.RawFieldChange
public import Motivic.AlgebraicGeometry.Correspondences.SimplexExteriorGraphInterchangeRight

/-!
# Actual finite cycle pushforward for weight-two corestriction

The coefficient maps below are finite projections through the canonical simplex
and torus comparisons. The extension field is never regarded as a smooth scheme
over the original field. Integral supports are sent to their actual finite images,
with their original residue degrees; signed sums and colliding images are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial

universe u

namespace Motivic.WeightTwoCorestriction

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- The literal base-times-simplex smooth object over its own field. -/
abbrev source (F : Type u) [Field F] (r : ℕ) : SmoothSite (Spec (.of F)) :=
  SmoothSite.product (SmoothSite.base (Spec (.of F)))
    (AlgebraicSimplex.smoothSiteObj F r)

/-- The literal torus smooth object over its own field. -/
abbrev target (F : Type u) [Field F] (q : ℕ) : SmoothSite (Spec (.of F)) :=
  SmoothSite.torusPower (.of F) q

/-- Product comparison before forgetting the extension field. -/
def ambientIso (r q : ℕ) :
    (SmoothSite.fieldBaseChange (algebraMap k E)).obj
      (SmoothSite.product (source k r) (target k q)) ≅
    SmoothSite.product (source E r) (target E q) :=
  SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      (source k r) (target k q) ≪≫
    SmoothSite.productIso
      (SmoothSite.baseSimplexFieldChangeIso (algebraMap k E) ⦋r⦌)
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k E)) q)

/-- The genuine finite coefficient map on the simplex-times-torus ambient scheme. -/
def ambientMap (r q : ℕ) :
    (SmoothSite.product (source E r) (target E q)).left ⟶
      (SmoothSite.product (source k r) (target k q)).left :=
  (ambientIso (k := k) (E := E) r q).inv.left ≫
    pullback.fst (SmoothSite.product (source k r) (target k q)).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))

/-- The actual scalar projection on the simplex source. -/
def sourceMap (r : ℕ) : (source E r).left ⟶ (source k r).left :=
  (SmoothSite.baseSimplexFieldChangeIso (algebraMap k E) ⦋r⦌).inv.left ≫
    pullback.fst (source k r).hom (Spec.map (CommRingCat.ofHom (algebraMap k E)))

instance source_isIntegral (F : Type u) [Field F] (r : ℕ) :
    IsIntegral (source F r).left := by
  change IsIntegral (pullback (𝟙 (Spec (.of F))) (AlgebraicSimplex.structureMap F r))
  infer_instance

variable [Module.Finite k E]

local instance scalar_isFinite :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

local instance scalar_surjective :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  ⟨Function.surjective_to_subsingleton _⟩

instance ambientMap_isFinite (r q : ℕ) : IsFinite (ambientMap (k := k) (E := E) r q) := by
  unfold ambientMap
  infer_instance

instance sourceMap_isFinite (r : ℕ) : IsFinite (sourceMap (k := k) (E := E) r) := by
  unfold sourceMap
  infer_instance

instance sourceMap_surjective (r : ℕ) : Surjective (sourceMap (k := k) (E := E) r) := by
  unfold sourceMap
  infer_instance

omit [Module.Finite k E] in
/-- The coefficient projection retains the literal first projection. -/
@[reassoc (attr := simp)]
theorem ambientMap_fst (r q : ℕ) :
    ambientMap (k := k) (E := E) r q ≫
      pullback.fst (source k r).hom (target k q).hom =
    pullback.fst (source E r).hom (target E q).hom ≫ sourceMap (k := k) (E := E) r := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k E))
  have h := congrArg (fun f => f.left)
    (SmoothSite.baseChangeProductIso_inv_fst φ (source k r) (target k q))
  have h' := congrArg (fun f => f.left)
    (SmoothSite.productMap_fst
      (SmoothSite.baseSimplexFieldChangeIso (algebraMap k E) ⦋r⦌).inv
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k E)) q).inv)
  dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productFst,
    SmoothSite.homMk_left] at h h'
  dsimp only [ambientMap, ambientIso, Iso.trans_inv, MorphismProperty.Comma.comp_left,
    SmoothSite.productIso_inv, sourceMap]
  have hn := SmoothSite.baseChange_map_fst φ (SmoothSite.productFst (source k r) (target k q))
  dsimp only [SmoothSite.productFst, SmoothSite.homMk_left] at hn
  simp only [Category.assoc]
  have hh := congrArg (fun f => f ≫ pullback.fst (source k r).hom φ) h
  rw [Category.assoc] at hh
  rw [← hn, hh]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ pullback.fst (source k r).hom φ) h').trans
      (Category.assoc _ _ _))

/-- The actual integral finite image is still an admissible correspondence support. -/
def imageGenerator (r q : ℕ)
    (A : FiniteCorrespondenceGenerator (source E r).hom (target E q).hom) :
    FiniteCorrespondenceGenerator (source k r).hom (target k q).hom := by
  let V := A.toIntegralClosedSubscheme.finiteImage (ambientMap (k := k) (E := E) r q)
  refine ⟨V.val, V.property, ?_, ?_⟩
  · have : IsFinite ((A.inclusion ≫ ambientMap (k := k) (E := E) r q) ≫
        pullback.fst (source k r).hom (target k q).hom) := by
      rw [Category.assoc, ambientMap_fst, ← Category.assoc]
      exact inferInstanceAs (IsFinite (A.projection ≫ sourceMap (k := k) (E := E) r))
    exact isFinite_image_projection (A.inclusion ≫ ambientMap (k := k) (E := E) r q) _
  · change Set.range ((A.inclusion ≫ ambientMap (k := k) (E := E) r q).imageι ≫
      pullback.fst (source k r).hom (target k q).hom) ∈ _
    rw [range_image_projection, Category.assoc, ambientMap_fst, ← Category.assoc]
    change Set.range (A.projection ≫ sourceMap (k := k) (E := E) r) ∈ _
    have : IrreducibleSpace ((𝟭 Scheme).obj (source E r).left) :=
      inferInstanceAs (IrreducibleSpace (source E r).left)
    have : Surjective A.projection := ⟨A.projection_surjective⟩
    rw [Set.range_eq_univ.mpr (inferInstance : Surjective
      (A.projection ≫ sourceMap (k := k) (E := E) r)).surj]
    exact (irreducibleComponents_eq_singleton (X := (source k r).left)) ▸ Set.mem_singleton _

/-- Forgetting admissibility gives the same actual finite image, without reduction changes. -/
@[simp]
theorem imageGenerator_toIntegralClosedSubscheme (r q : ℕ)
    (A : FiniteCorrespondenceGenerator (source E r).hom (target E q).hom) :
    (imageGenerator (k := k) r q A).toIntegralClosedSubscheme =
      A.toIntegralClosedSubscheme.finiteImage (ambientMap (k := k) (E := E) r q) := rfl

/-- The signed transfer on actual cycle groups, retaining each support's own degree. -/
def cyclePushforward (r q : ℕ) :
    (Cor.mk (source E r) ⟶ Cor.mk (target E q)) →+
      (Cor.mk (source k r) ⟶ Cor.mk (target k q)) :=
  Finsupp.liftAddHom fun A =>
    { toFun := fun n => Finsupp.single (imageGenerator (k := k) r q A)
        (n * ((ambientMap (k := k) (E := E) r q).residueDegree A.point : ℤ))
      map_zero' := by simp
      map_add' := by intro m n; simp [add_mul, Finsupp.single_add] }

/-- Exact generator formula: coefficients are signed and images can collide. -/
@[simp]
theorem cyclePushforward_single (r q : ℕ)
    (A : FiniteCorrespondenceGenerator (source E r).hom (target E q).hom) (n : ℤ) :
    cyclePushforward (k := k) (E := E) r q (Finsupp.single A n) =
      Finsupp.single (imageGenerator (k := k) r q A)
        (n * ((ambientMap (k := k) (E := E) r q).residueDegree A.point : ℤ)) :=
  Finsupp.liftAddHom_apply_single _ _ _

/-- The cycle transfer is literally the original finite integral-cycle pushforward. -/
theorem toIntegralCycle_cyclePushforward (r q : ℕ)
    (α : Cor.mk (source E r) ⟶ Cor.mk (target E q)) :
    FiniteCorrespondence.toIntegralCycle (cyclePushforward (k := k) (E := E) r q α) =
      IntegralCycle.finitePushforward (ambientMap (k := k) (E := E) r q)
        (FiniteCorrespondence.toIntegralCycle α) := by
  have h : FiniteCorrespondence.toIntegralCycle.comp (cyclePushforward (k := k) (E := E) r q) =
      (IntegralCycle.finitePushforward (ambientMap (k := k) (E := E) r q)).comp
        FiniteCorrespondence.toIntegralCycle := by
    apply Finsupp.addHom_ext
    intro A n
    change FiniteCorrespondence.toIntegralCycle
        (cyclePushforward (k := k) (E := E) r q (Finsupp.single A n)) =
      IntegralCycle.finitePushforward (ambientMap (k := k) (E := E) r q)
        (FiniteCorrespondence.toIntegralCycle (Finsupp.single A n))
    rw [cyclePushforward_single, FiniteCorrespondence.toIntegralCycle_single,
      FiniteCorrespondence.toIntegralCycle_single, IntegralCycle.finitePushforward_single]
    rfl
  exact DFunLike.congr_fun h α

/-- The actual ambient inclusion inserting an identity coordinate. -/
def axisMap (F : Type u) [Field F] (r q : ℕ) (i : Fin (q + 1)) :
    (SmoothSite.product (source F r) (target F q)).left ⟶
      (SmoothSite.product (source F r) (target F (q + 1))).left :=
  (SmoothSite.productMap (𝟙 (source F r)) (SmoothSite.torusInsertOne (.of F) q i)).left

instance axisMap_isClosedImmersion (F : Type u) [Field F] (r q : ℕ) (i : Fin (q + 1)) :
    IsClosedImmersion (axisMap F r q i) := by
  let d := SmoothSite.productMap (𝟙 (source F r))
    (SmoothSite.torusDeleteCoordinate (.of F) q i)
  have : IsSeparated (d.left ≫ (SmoothSite.product (source F r) (target F q)).hom) := by
    rw [MorphismProperty.Over.w]
    infer_instance
  have : IsSeparated d.left := IsSeparated.of_comp _
    (SmoothSite.product (source F r) (target F q)).hom
  have h : axisMap F r q i ≫ d.left = 𝟙 _ := by
    change (SmoothSite.productMap (𝟙 _) (SmoothSite.torusInsertOne (.of F) q i) ≫ d).left = _
    dsimp only [d]
    rw [← SmoothSite.productMap_comp, Category.id_comp,
      SmoothSite.torusInsertOne_deleteCoordinate, SmoothSite.productMap_id]
    rfl
  have : IsClosedImmersion (axisMap F r q i ≫ d.left) := by rw [h]; infer_instance
  exact IsClosedImmersion.of_comp _ d.left

omit [Module.Finite k E] in
/-- Identity-coordinate insertion commutes with the canonical comparison before pushforward. -/
theorem ambientIso_axis (r q : ℕ) (i : Fin (q + 1)) :
    (SmoothSite.fieldBaseChange (algebraMap k E)).map
        (SmoothSite.productMap (𝟙 (source k r)) (SmoothSite.torusInsertOne (.of k) q i)) ≫
      (ambientIso (k := k) (E := E) r (q + 1)).hom =
    (ambientIso (k := k) (E := E) r q).hom ≫
      SmoothSite.productMap (𝟙 (source E r)) (SmoothSite.torusInsertOne (.of E) q i) := by
  dsimp only [ambientIso, Iso.trans_hom, SmoothSite.productIso_hom, SmoothSite.fieldBaseChange]
  rw [← Category.assoc, SmoothSite.baseChangeProductIso_naturality]
  simp only [Category.assoc, ← SmoothSite.productMap_comp, Category.comp_id]
  rw [SmoothSite.torusPowerBaseChangeIso_insertOne]
  have hi := (SmoothSite.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k E)))).map_id (source k r)
  rw [hi, Category.id_comp]

omit [Module.Finite k E] in
/-- The literal coefficient/identity-axis square of finite scheme maps. -/
theorem ambientMap_axis (r q : ℕ) (i : Fin (q + 1)) :
    axisMap E r q i ≫ ambientMap (k := k) (E := E) r (q + 1) =
      ambientMap (k := k) (E := E) r q ≫ axisMap k r q i := by
  have h : SmoothSite.productMap (𝟙 (source E r)) (SmoothSite.torusInsertOne (.of E) q i) ≫
      (ambientIso (k := k) (E := E) r (q + 1)).inv =
    (ambientIso (k := k) (E := E) r q).inv ≫
      (SmoothSite.fieldBaseChange (algebraMap k E)).map
        (SmoothSite.productMap (𝟙 (source k r)) (SmoothSite.torusInsertOne (.of k) q i)) := by
    apply (cancel_mono (ambientIso (k := k) (E := E) r (q + 1)).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ambientIso_axis, Iso.inv_hom_id_assoc]
  have hs := congrArg (fun f => f.left) h
  dsimp only [MorphismProperty.Comma.comp_left] at hs
  unfold ambientMap axisMap
  rw [← Category.assoc, hs, Category.assoc]
  exact (congrArg (fun f => (ambientIso (k := k) (E := E) r q).inv.left ≫ f)
    (SmoothSite.baseChange_map_fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      (SmoothSite.productMap (𝟙 (source k r)) (SmoothSite.torusInsertOne (.of k) q i)))).trans
        (Category.assoc _ _ _).symm

/-- Postcomposing any signed correspondence by an identity axis is literal finite pushforward. -/
theorem toIntegralCycle_axis (F : Type u) [Field F] (r q : ℕ) (i : Fin (q + 1))
    (α : Cor.mk (source F r) ⟶ Cor.mk (target F q)) :
    FiniteCorrespondence.toIntegralCycle
      (f := (source F r).hom) (g := (target F (q + 1)).hom)
      (α ≫ (Cor.graphFunctor F).map (SmoothSite.torusInsertOne (.of F) q i)) =
      IntegralCycle.finitePushforward (axisMap F r q i)
        (FiniteCorrespondence.toIntegralCycle α) := by
  have h : (FiniteCorrespondence.toIntegralCycle
      (f := (source F r).hom) (g := (target F (q + 1)).hom)).comp
      (Preadditive.rightComp (Cor.mk (source F r))
        ((Cor.graphFunctor F).map (SmoothSite.torusInsertOne (.of F) q i))) =
      (IntegralCycle.finitePushforward (axisMap F r q i)).comp
        FiniteCorrespondence.toIntegralCycle := by
    apply Finsupp.addHom_ext'
    intro A
    change FiniteCorrespondenceGenerator (source F r).hom (target F q).hom at A
    apply AddMonoidHom.ext_int
    change FiniteCorrespondence.toIntegralCycle
      (f := (source F r).hom) (g := (target F (q + 1)).hom)
      (A.cycle ≫ (Cor.graphFunctor F).map (SmoothSite.torusInsertOne (.of F) q i)) =
      IntegralCycle.finitePushforward (axisMap F r q i)
        (FiniteCorrespondence.toIntegralCycle A.cycle)
    have : IsNoetherian ((𝟭 Scheme).obj (source F r).left) :=
      inferInstanceAs (IsNoetherian (source F r).left)
    have : IsNoetherian A.scheme := isNoetherian_of_finiteType A.projection
    have hg := A.toIntegralCycle_incidenceTorPairing_componentGraph_right F
      (SmoothSite.torusInsertOne (.of F) q i).left
      (MorphismProperty.Over.w (SmoothSite.torusInsertOne (.of F) q i))
    have hm : A.graphPostcompositionMap (SmoothSite.torusInsertOne (.of F) q i).left
        (MorphismProperty.Over.w (SmoothSite.torusInsertOne (.of F) q i)) =
        A.inclusion ≫ axisMap F r q i := by
      apply pullback.hom_ext
      · simp only [FiniteCorrespondenceGenerator.graphPostcompositionMap_fst, Category.assoc]
        change A.projection = A.inclusion ≫
          (SmoothSite.productMap (𝟙 _) (SmoothSite.torusInsertOne (.of F) q i)).left ≫ _
        have hp := congrArg (fun f => f.left)
          (SmoothSite.productMap_fst (𝟙 (source F r)) (SmoothSite.torusInsertOne (.of F) q i))
        dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productFst,
          SmoothSite.homMk_left] at hp
        exact congrArg (fun f => A.inclusion ≫ f) hp.symm
      · simp only [FiniteCorrespondenceGenerator.graphPostcompositionMap_snd, Category.assoc]
        have hp := congrArg (fun f => f.left)
          (SmoothSite.productMap_snd (𝟙 (source F r)) (SmoothSite.torusInsertOne (.of F) q i))
        dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productSnd,
          SmoothSite.homMk_left] at hp
        change A.targetProjection ≫ _ = A.inclusion ≫ _ ≫ _
        dsimp only [axisMap]
        rw [hp, ← Category.assoc]
    simp only [hm, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply] at hg
    have : IsNoetherian (pullback (source F r).hom (target F q).hom) :=
      isNoetherian_of_finiteType (pullback.fst (source F r).hom (target F q).hom)
    have hc : IntegralCycle.finitePushforward A.inclusion (fundamentalCycle A.scheme) =
        FiniteCorrespondence.toIntegralCycle A.cycle := by
      change closedFundamentalCycle A.val = FiniteCorrespondence.toIntegralCycle A.cycle
      rw [closedFundamentalCycle_of_isIntegral, FiniteCorrespondenceGenerator.cycle,
        FiniteCorrespondence.toIntegralCycle_single]
      rfl
    rw [hc] at hg
    exact hg
  exact DFunLike.congr_fun h α

/-- Every signed identity-axis relation transfers to the same identity axis. -/
theorem cyclePushforward_axis (r q : ℕ) (i : Fin (q + 1))
    (α : Cor.mk (source E r) ⟶ Cor.mk (target E q)) :
    cyclePushforward (k := k) (E := E) r (q + 1)
      (α ≫ (Cor.graphFunctor E).map (SmoothSite.torusInsertOne (.of E) q i)) =
    cyclePushforward (k := k) (E := E) r q α ≫
      (Cor.graphFunctor k).map (SmoothSite.torusInsertOne (.of k) q i) := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_cyclePushforward, toIntegralCycle_axis,
    toIntegralCycle_axis, toIntegralCycle_cyclePushforward]
  change ((IntegralCycle.finitePushforward (ambientMap (k := k) (E := E) r (q + 1))).comp
      (IntegralCycle.finitePushforward (axisMap E r q i))) _ =
    ((IntegralCycle.finitePushforward (axisMap k r q i)).comp
      (IntegralCycle.finitePushforward (ambientMap (k := k) (E := E) r q))) _
  rw [← IntegralCycle.finitePushforward_comp, ← IntegralCycle.finitePushforward_comp]
  simp only [ambientMap_axis]

open PresheafWithTransfers

/-- The same signed cycle transfer, in the original coefficient universe. -/
def liftedCyclePushforward (r q : ℕ) :
    sections (torusRepresentable E q) (Cor.mk (source E r)) ⟶
      sections (torusRepresentable k q) (Cor.mk (source k r)) :=
  AddCommGrpCat.ofHom
    { toFun := fun α => ULift.up (cyclePushforward (k := k) (E := E) r q α.down)
      map_zero' := congrArg ULift.up (map_zero (cyclePushforward (k := k) (E := E) r q))
      map_add' := fun α β => congrArg ULift.up
        (map_add (cyclePushforward (k := k) (E := E) r q) α.down β.down) }

/-- The original relation morphism is annihilated after actual transfer and quotient. -/
theorem liftedCyclePushforward_relations (r q : ℕ) :
    (torusRelation E q).app (op (Cor.mk (source E r))) ≫
      liftedCyclePushforward (k := k) (E := E) r q ≫
        (toReducedTorus k q).hom.app (op (Cor.mk (source k r))) = 0 := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  change (toReducedTorus k q).hom.app _
    (liftedCyclePushforward (k := k) (E := E) r q
      ((torusRelation E q).app _ s)) = 0
  rw [torusRelation_app_apply, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  cases q with
  | zero => exact Fin.elim0 i
  | succ q =>
    let : HasBiproduct (fun _ : Fin (q + 1) => (torusRepresentable E q).obj) :=
      HasBiproduct.of_hasCoproduct _
    let β := ((biproduct.π (fun _ : Fin (q + 1) => (torusRepresentable E q).obj) i).app
      (op (Cor.mk (source E r))) s).down
    change (toReducedTorus k (q + 1)).hom.app _
      (ULift.up (cyclePushforward (k := k) (E := E) r (q + 1)
        (β ≫ (Cor.graphFunctor E).map (SmoothSite.torusInsertOne (.of E) q i)))) = 0
    rw [cyclePushforward_axis]
    exact congrArg (fun f => f.hom.app (op (Cor.mk (source k r)))
      (ULift.up (cyclePushforward (k := k) (E := E) r q β)))
        (torusIdentityAxis_toReducedTorus k (q + 1) i)

/-- Finite cycle pushforward descends through the actual objectwise identity-axis cokernel. -/
def reducedPushforward (r q : ℕ) :
    sections (reducedTorus E q) (Cor.mk (source E r)) ⟶
      sections (reducedTorus k q) (Cor.mk (source k r)) :=
  (PreservesCokernel.iso ((evaluation (Cor E)ᵒᵖ AddCommGrpCat).obj
      (op (Cor.mk (source E r)))) (torusRelation E q)).hom ≫
    cokernel.desc ((torusRelation E q).app (op (Cor.mk (source E r))))
      (liftedCyclePushforward (k := k) (E := E) r q ≫
        (toReducedTorus k q).hom.app (op (Cor.mk (source k r))))
      (liftedCyclePushforward_relations r q)

/-- The descended map has the exact original signed-cycle formula on quotient classes. -/
theorem reducedPushforward_quotient (r q : ℕ)
    (α : Cor.mk (source E r) ⟶ Cor.mk (target E q)) :
    reducedPushforward (k := k) (E := E) r q
      ((toReducedTorus E q).hom.app (op (Cor.mk (source E r))) (ULift.up α)) =
    (toReducedTorus k q).hom.app (op (Cor.mk (source k r)))
      (ULift.up (cyclePushforward (k := k) (E := E) r q α)) := by
  have h : (toReducedTorus E q).hom.app (op (Cor.mk (source E r))) ≫
      reducedPushforward (k := k) (E := E) r q =
    liftedCyclePushforward (k := k) (E := E) r q ≫
      (toReducedTorus k q).hom.app (op (Cor.mk (source k r))) := by
    change ((evaluation (Cor E)ᵒᵖ AddCommGrpCat).obj (op (Cor.mk (source E r)))).map
      (cokernel.π (torusRelation E q)) ≫
      (PreservesCokernel.iso ((evaluation (Cor E)ᵒᵖ AddCommGrpCat).obj
        (op (Cor.mk (source E r)))) (torusRelation E q)).hom ≫
      cokernel.desc ((torusRelation E q).app (op (Cor.mk (source E r)))) _ _ = _
    rw [PreservesCokernel.π_iso_hom_assoc]
    exact cokernel.π_desc _ _ _
  exact ConcreteCategory.congr_hom h (ULift.up α)

end Motivic.WeightTwoCorestriction
