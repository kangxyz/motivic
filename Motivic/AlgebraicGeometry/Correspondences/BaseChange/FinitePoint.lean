/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Cycles.ScalarExtension.FinitePointBaseChange
public import Motivic.AlgebraicGeometry.Correspondences.BaseChange.Field.Cycle
public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Cech.SupportPairing

/-!
# Field change of actual finite-point correspondences

The field change of the original degree-weighted finite image is the finite
pushforward of the whole scalar-extended source. In particular the source need
not embed into its target, and no injection of component images is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FinitePointCorrespondenceBaseChange
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.Cycles
open _root_.AlgebraicGeometry.Scheme.Hom

open FiniteCorrespondenceGenerator

variable {k L : Type u} [Field k] [Field L] (φ : k →+* L)
  {Y : SmoothSite.overField k} {P : Scheme.{u}} [IsIntegral P] [IsNoetherian P]
  (m : P ⟶ pullback (SmoothSite.base (Spec (.of k))).hom Y.hom)
  [IsFinite m] [IsFinite (m ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom Y.hom)]

omit [AlgebraicGeometry.IsNoetherian P] [IsFinite m]
  [IsFinite (m ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom Y.hom)] in
/-- The integral source necessarily dominates the unique field point. -/
theorem range_projection :
    Set.range (m ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom Y.hom) ∈
      irreducibleComponents (SmoothSite.base (Spec (.of k))).left := by
  let : Subsingleton ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  rw [Set.range_eq_univ.mpr (Function.surjective_to_subsingleton _)]
  exact (irreducibleComponents_eq_singleton (X := Spec (.of k))) ▸ Set.mem_singleton _

/-- The original reduced image, with its actual admissible finite projection. -/
abbrev imageGenerator : FiniteCorrespondenceGenerator
    (SmoothSite.base (Spec (.of k))).hom Y.hom :=
  supportLiftImageGenerator k P m (range_projection m)

/-- The whole scalar-extended source, using its original structural map through its image. -/
abbrev support : Scheme.{u} :=
  FinitePointBaseChange.source φ m.toImage
    ((imageGenerator m).projection ≫ (SmoothSite.base (Spec (.of k))).hom)

/-- The entire changed source maps to the changed ambient product. -/
def supportMap : support φ m ⟶
    (SmoothSite.product
      ((SmoothSite.fieldBaseChange φ).obj (SmoothSite.base (Spec (.of k))))
      ((SmoothSite.fieldBaseChange φ).obj Y)).left :=
  FinitePointBaseChange.map φ m.toImage
      ((imageGenerator m).projection ≫ (SmoothSite.base (Spec (.of k))).hom) ≫
    (imageGenerator m).fieldBaseChangeInclusion φ

instance imageProjection_isFinite :
    IsFinite ((imageGenerator m).projection ≫ (SmoothSite.base (Spec (.of k))).hom) := by
  change IsFinite ((imageGenerator m).projection ≫ 𝟙 _)
  rw [Category.comp_id]
  infer_instance

instance support_isNoetherian : IsNoetherian (support φ m) := by
  have := isFinite_toImage m
  exact FinitePointBaseChange.source_isNoetherian φ m.toImage _

instance supportMap_isFinite : IsFinite (supportMap φ m) := by
  have := isFinite_toImage m
  unfold supportMap
  infer_instance

omit [AlgebraicGeometry.IsNoetherian P] in
/-- The structural map used by the whole support is exactly the original one. -/
theorem support_structure :
    m.toImage ≫ ((imageGenerator m).projection ≫
      (SmoothSite.base (Spec (.of k))).hom) =
        m ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom Y.hom := by
  change m.toImage ≫ ((m.imageι ≫ pullback.fst _ _) ≫ 𝟙 _) = _
  simp only [Category.comp_id, ← Category.assoc, Scheme.Hom.toImage_imageι]

omit [AlgebraicGeometry.IsNoetherian P] in
/-- The full source retains its literal projection to the original ambient scheme. -/
@[reassoc]
theorem supportMap_original :
    supportMap φ m ≫
      (SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom φ))
        (SmoothSite.base (Spec (.of k))) Y).inv.left ≫
      pullback.fst (SmoothSite.product (SmoothSite.base (Spec (.of k))) Y).hom
        (Spec.map (CommRingCat.ofHom φ)) =
    pullback.fst
      (m.toImage ≫ ((imageGenerator m).projection ≫
        (SmoothSite.base (Spec (.of k))).hom))
      (Spec.map (CommRingCat.ofHom φ)) ≫ m := by
  let A := imageGenerator m
  let e := SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom φ))
    (SmoothSite.base (Spec (.of k))) Y
  have he : e.hom.left ≫ e.inv.left = 𝟙 _ := congrArg (fun h => h.left) e.hom_inv_id
  dsimp only [supportMap, FiniteCorrespondenceGenerator.fieldBaseChangeInclusion]
  simp only [Category.assoc]
  rw [← Category.assoc e.hom.left, he, Category.id_comp,
    A.fieldBaseChangeAmbientInclusion_fst,
    ← Category.assoc, FinitePointBaseChange.map_fst]
  change (_ ≫ m.toImage) ≫ m.imageι = _
  rw [Category.assoc, Scheme.Hom.toImage_imageι]

omit [AlgebraicGeometry.IsNoetherian P] in
@[reassoc (attr := simp)] theorem supportMap_original_simp :
    supportMap φ m ≫
      (SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom φ))
        (SmoothSite.base (Spec (.of k))) Y).inv.left ≫
      pullback.fst (pullback.fst (SmoothSite.base (Spec (.of k))).hom Y.hom ≫
        (SmoothSite.base (Spec (.of k))).hom)
        (Spec.map (CommRingCat.ofHom φ)) =
    pullback.fst
      (m.toImage ≫ ((imageGenerator m).projection ≫
        (SmoothSite.base (Spec (.of k))).hom))
      (Spec.map (CommRingCat.ofHom φ)) ≫ m :=
  supportMap_original φ m

omit [AlgebraicGeometry.IsNoetherian P] in
/-- The full source retains its literal projection to the changed base object. -/
@[reassoc]
theorem supportMap_base :
    supportMap φ m ≫
      pullback.fst
        ((SmoothSite.fieldBaseChange φ).obj (SmoothSite.base (Spec (.of k)))).hom
        ((SmoothSite.fieldBaseChange φ).obj Y).hom ≫
      (SmoothSite.baseChangeBaseIso (Spec.map (CommRingCat.ofHom φ))).hom.left =
    pullback.snd
      (m.toImage ≫ ((imageGenerator m).projection ≫
        (SmoothSite.base (Spec (.of k))).hom))
      (Spec.map (CommRingCat.ofHom φ)) := by
  simp only [supportMap, Category.assoc, fieldBaseChangeInclusion_fst_assoc,
    SmoothSite.baseChangeBaseIso_hom_left]
  erw [(imageGenerator m).fieldBaseChangeProjection_snd φ, FinitePointBaseChange.map_snd]

omit [AlgebraicGeometry.IsNoetherian P] in
@[reassoc (attr := simp)] theorem supportMap_base_simp :
    supportMap φ m ≫
      pullback.fst
        (pullback.snd (SmoothSite.base (Spec (.of k))).hom
          (Spec.map (CommRingCat.ofHom φ)))
        (pullback.snd Y.hom (Spec.map (CommRingCat.ofHom φ))) ≫
      pullback.snd (𝟙 (Spec (.of k))) (Spec.map (CommRingCat.ofHom φ)) =
    pullback.snd
      (m.toImage ≫ ((imageGenerator m).projection ≫
        (SmoothSite.base (Spec (.of k))).hom))
      (Spec.map (CommRingCat.ofHom φ)) :=
  supportMap_base φ m

omit [AlgebraicGeometry.IsNoetherian P] in
/-- Actual scalar extension commutes with finite pushforward of an integral finite point.
The right side retains the whole source and all new local lengths. -/
theorem toIntegralCycle_fieldBaseChange_weightedSupportImage :
    FiniteCorrespondence.toIntegralCycle
      (FiniteCorrespondence.fieldBaseChange (X := SmoothSite.base (Spec (.of k))) (Y := Y) φ
        (weightedSupportImage k P m (range_projection m))) =
      IntegralCycle.finitePushforward (supportMap φ m) (fundamentalCycle (support φ m)) := by
  have := isFinite_toImage m
  let : IsIntegral m.image := isIntegral_finiteImage m
  have hdegree : m.toImage.residueDegree (genericPoint P) =
      m.residueDegree (genericPoint P) := by
    have h := residueDegree_comp m.toImage m.imageι (genericPoint P)
    simpa only [Scheme.Hom.toImage_imageι, residueDegree_of_surjectiveOnStalks,
      one_mul] using h.symm
  have h := FinitePointBaseChange.finitePushforward_fundamentalCycle φ m.toImage
    ((imageGenerator m).projection ≫ (SmoothSite.base (Spec (.of k))).hom)
  rw [hdegree] at h
  simp only [weightedSupportImage, map_zsmul, FiniteCorrespondence.fieldBaseChange_cycle,
    toIntegralCycle_fieldBaseChangeCycle]
  unfold supportMap
  rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    h, map_zsmul]

/-- Any original correspondence with this actual finite fundamental-cycle presentation
has the same whole-source field change. -/
theorem toIntegralCycle_fieldBaseChange_of_finitePoint
    (α : FiniteCorrespondence (SmoothSite.base (Spec (.of k))).hom Y.hom)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward m (fundamentalCycle P)) :
    FiniteCorrespondence.toIntegralCycle (FiniteCorrespondence.fieldBaseChange
      (X := SmoothSite.base (Spec (.of k))) (Y := Y) φ α) =
      IntegralCycle.finitePushforward (supportMap φ m) (fundamentalCycle (support φ m)) := by
  have h := toIntegralCycle_weightedSupportImage k P m (range_projection m)
  have he : α = weightedSupportImage k P m (range_projection m) :=
    FiniteCorrespondence.toIntegralCycle_injective (hα.trans h.symm)
  rw [he]
  exact toIntegralCycle_fieldBaseChange_weightedSupportImage φ m

end Motivic.FinitePointCorrespondenceBaseChange
