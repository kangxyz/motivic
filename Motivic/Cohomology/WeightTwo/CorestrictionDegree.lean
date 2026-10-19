/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.CorestrictionHomology
public import Motivic.AlgebraicGeometry.Correspondences.Graph.IsoTransport
public import Motivic.Aglib.AlgebraicGeometry.Cycles.ScalarExtension.FiniteScalarFundamentalCycle
public import Motivic.Cohomology.WeightTwo.FieldChange

/-!
# Finite scalar extension followed by the original cycle transfer

The whole scalar-extended support is retained, with every generic local length.
The degree comes from the complete degree-length identity, including inseparable
and nonreduced scalar extensions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

universe w u

namespace Motivic.WeightTwoCorestriction
open _root_.AlgebraicGeometry.Scheme

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]

local instance scalarMap_isFinite :
    IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k E))) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The literal projection from the product of the two changed smooth objects. -/
def fieldChangeAmbientProjection (X Y : SmoothSite.overField k) :
    (SmoothSite.product ((SmoothSite.fieldBaseChange (algebraMap k E)).obj X)
      ((SmoothSite.fieldBaseChange (algebraMap k E)).obj Y)).left ⟶
        (SmoothSite.product X Y).left :=
  (SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom (algebraMap k E)))
    X Y).inv.left ≫ pullback.fst (SmoothSite.product X Y).hom
      (Spec.map (CommRingCat.ofHom (algebraMap k E)))

instance fieldChangeAmbientProjection_isFinite (X Y : SmoothSite.overField k) :
    IsFinite (fieldChangeAmbientProjection (E := E) X Y) := by
  unfold fieldChangeAmbientProjection
  infer_instance

/-- Projecting the entire changed support gives the extension degree on a generator. -/
theorem finitePushforward_fieldBaseChangeCycle
    {X Y : SmoothSite.overField k} (A : FiniteCorrespondenceGenerator X.hom Y.hom) :
    IntegralCycle.finitePushforward (fieldChangeAmbientProjection (E := E) X Y)
      (FiniteCorrespondence.toIntegralCycle (A.fieldBaseChangeCycle (algebraMap k E))) =
        (Module.finrank k E : ℤ) • FiniteCorrespondence.toIntegralCycle A.cycle := by
  have : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  have : IsNoetherian A.scheme := isNoetherian_of_finiteType A.projection
  have : IsNoetherian (pullback X.hom Y.hom) :=
    isNoetherian_of_finiteType (pullback.fst X.hom Y.hom)
  have hm : A.fieldBaseChangeInclusion (algebraMap k E) ≫
      fieldChangeAmbientProjection (E := E) X Y =
    pullback.fst (A.projection ≫ X.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap k E))) ≫ A.inclusion := by
    dsimp only [FiniteCorrespondenceGenerator.fieldBaseChangeInclusion,
      fieldChangeAmbientProjection]
    have he := congrArg (fun m => m.left)
      (SmoothSite.baseChangeProductIso
        (Spec.map (CommRingCat.ofHom (algebraMap k E))) X Y).hom_inv_id
    dsimp only [MorphismProperty.Comma.comp_left, MorphismProperty.Comma.id_left] at he
    change _ = 𝟙 _ at he
    rw [Category.assoc, ← Category.assoc _ _ (pullback.fst _ _), he]
    erw [Category.id_comp]
    exact A.fieldBaseChangeAmbientInclusion_fst (algebraMap k E)
  rw [FiniteCorrespondenceGenerator.toIntegralCycle_fieldBaseChangeCycle,
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp,
    IntegralCycle.finitePushforward_congr hm,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_scalar_fundamentalCycle, map_zsmul]
  congr 1
  change closedFundamentalCycle A.val = FiniteCorrespondence.toIntegralCycle A.cycle
  rw [closedFundamentalCycle_of_isIntegral, FiniteCorrespondenceGenerator.cycle,
    FiniteCorrespondence.toIntegralCycle_single]
  rfl

/-- The exact degree formula holds for every original signed cycle, with collisions. -/
theorem finitePushforward_fieldBaseChange
    {X Y : SmoothSite.overField k} (α : FiniteCorrespondence X.hom Y.hom) :
    IntegralCycle.finitePushforward (fieldChangeAmbientProjection (E := E) X Y)
      (FiniteCorrespondence.toIntegralCycle
        (FiniteCorrespondence.fieldBaseChange (X := X) (Y := Y) (algebraMap k E) α)) =
      (Module.finrank k E : ℤ) • FiniteCorrespondence.toIntegralCycle α := by
  classical
  induction α using Finsupp.induction_linear with
  | zero => simp only [map_zero, smul_zero]
  | add α β hα hβ => simp only [map_add, smul_add, hα, hβ]
  | single A n =>
    have hn : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hn, map_zsmul, map_zsmul, map_zsmul,
      FiniteCorrespondence.fieldBaseChange_cycle, finitePushforward_fieldBaseChangeCycle,
      map_zsmul, smul_comm]

omit [Module.Finite k E] in
/-- The canonical graph comparisons cancel against the actual scalar projection. -/
theorem graphTransportIso_ambientMap (r q : ℕ) :
    (Cor.graphTransportIso E
      (SmoothSite.baseSimplexFieldChangeIso (algebraMap k E) ⦋r⦌)
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k E)) q)).hom ≫
        ambientMap (k := k) (E := E) r q =
      fieldChangeAmbientProjection (E := E) (source k r) (target k q) := by
  let t := SmoothSite.productIso
    (SmoothSite.baseSimplexFieldChangeIso (algebraMap k E) ⦋r⦌)
    (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k E)) q)
  have ht : t.hom.left ≫ t.inv.left = 𝟙 _ :=
    congrArg (fun m => m.left) t.hom_inv_id
  change t.hom.left ≫ (t.inv.left ≫
    (SmoothSite.baseChangeProductIso (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      (source k r) (target k q)).inv.left) ≫ _ = _
  rw [← Category.assoc, ← Category.assoc, ht, Category.id_comp]
  rfl

/-- In every simplex degree the original cycle transfer after extension is the degree. -/
theorem cyclePushforward_fieldBaseChange (r q : ℕ)
    (α : Cor.mk (source k r) ⟶ Cor.mk (target k q)) :
    cyclePushforward (k := k) (E := E) r q
      ((Cor.graphFunctor E).map
        (SmoothSite.baseSimplexFieldChangeIso (algebraMap k E) ⦋r⦌).inv ≫
          (Cor.fieldBaseChange (algebraMap k E)).map α ≫ (Cor.graphFunctor E).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k E)) q).hom) =
      (Module.finrank k E : ℤ) • α := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_cyclePushforward, Cor.toIntegralCycle_graphIso_transport]
  erw [← AddMonoidHom.comp_apply
    (IntegralCycle.finitePushforward (ambientMap (k := k) (E := E) r q)),
    ← IntegralCycle.finitePushforward_comp,
    IntegralCycle.finitePushforward_congr (graphTransportIso_ambientMap r q),
    Cor.fieldBaseChange_map, finitePushforward_fieldBaseChange, map_zsmul]

open _root_.AlgebraicSimplex in
open _root_.Motivic.PresheafWithTransfers in
open WeightOnePointNorm in
open WeightOneBoundaryNorm in
/-- Every original signed point cycle has transfer after scalar extension equal to degree. -/
theorem pointPushforward_baseTorusCycleFieldChange
    (α : point k ⟶ WeightTwoSymbols.target k) :
    pointPushforward (k := k) (E := E)
      (baseTorusCycleFieldChange (algebraMap k E) 2 α) =
        (Module.finrank k E : ℤ) • α := by
  have h := cyclePushforward_fieldBaseChange (E := E) 0 2 ((zeroProductIso k).hom ≫ α)
  have hz :
      (Cor.graphFunctor E).map
          (SmoothSite.baseSimplexFieldChangeIso (algebraMap k E) ⦋0⦌).inv ≫
        (Cor.fieldBaseChange (algebraMap k E)).map ((zeroProductIso k).hom ≫ α) ≫
          (Cor.graphFunctor E).map
            (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k E)) 2).hom =
        (zeroProductIso E).hom ≫ baseTorusCycleFieldChange (algebraMap k E) 2 α := by
    apply (cancel_epi (zeroProductIso E).inv).mp
    rw [Functor.map_comp]
    simp only [← Category.assoc,
      WeightOneCohomologyFieldChange.zeroProductIso_fieldChange_inv]
    simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  rw [hz] at h
  rw [pointPushforward_apply, h, Preadditive.comp_zsmul, Iso.inv_hom_id_assoc]

/-- Transfer after scalar extension is degree multiplication on every original H22 class. -/
theorem corestriction_fieldChange (x : (motivicRawBaseComplex k 2).homology 2) :
    corestriction (k := k) (E := E)
      (HomologicalComplex.homologyMap
        (motivicRawBaseComplexMap (algebraMap k E) 2) 2 x) =
      (Module.finrank k E : ℤ) • x := by
  obtain ⟨α, rfl⟩ := WeightTwoSymbols.cycleClass_surjective k x
  rw [WeightTwoFieldChange.cycleClass_fieldChange, corestriction_cycleClass,
    pointPushforward_baseTorusCycleFieldChange, map_zsmul]

section Derived

variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1})]
variable [HasDerivedCategory.{w}
  (Sheaf (SmoothSite.nisnevichTopology (Spec (.of E))) AddCommGrpCat.{u + 1})]

/-- The canonical comparison gives the same degree formula on the original motivic group. -/
theorem motivicCorestriction_fieldChange
    (x : motivicCohomology k 2 2 (SmoothSite.base (Spec (.of k)))) :
    motivicCorestriction (k := k) (E := E)
      (motivicCohomologyFieldChange (algebraMap k E) 2 2 x) =
      (Module.finrank k E : ℤ) • x := by
  apply (motivicRawBaseEvaluationComparison k 2 2).injective
  rw [motivicCorestriction_comparison, motivicCohomologyFieldChange_rawComparison,
    corestriction_fieldChange, map_zsmul]

end Derived

end Motivic.WeightTwoCorestriction
