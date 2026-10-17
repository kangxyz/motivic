/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.FiniteFlatCurveSpecialization
public import Motivic.AlgebraicGeometry.Correspondences.FlatLeftGraphComposition
public import Motivic.AlgebraicGeometry.Cycles.FundamentalInvariance

/-!
# Finite-flat curve families as actual finite correspondences

The parameter line is literally `Spec k[X]`. The original generic local lengths
weight every component, and graph restriction is the fundamental cycle of the
whole scheme-theoretic fiber. Neither the family nor its fibers are reduced.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped BigOperators Polynomial

universe u

namespace Motivic.FiniteFlatCurveFamily

variable (k : Type u) [Field k]

/-- The literal affine parameter line with its polynomial structure map. -/
def line : SmoothSite (Spec (.of k)) := by
  let : Algebra.Smooth k k[X] := {}
  have : Smooth (Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* k[X]))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  exact SmoothSite.mk (Spec.map (CommRingCat.ofHom Polynomial.C))

/-- The field point as an object of the smooth site. -/
abbrev point : SmoothSite (Spec (.of k)) := SmoothSite.base (Spec (.of k))

/-- Evaluation at a scalar, with its literal affine-spectrum map. -/
def evaluationPoint (a : k) : point k ⟶ line k :=
  SmoothSite.homMk (FiniteFlatCurve.endpoint a) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of k))
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    ext r
    exact Polynomial.eval_C)

instance lineIntegral : IsIntegral (line k).left :=
  inferInstanceAs (IsIntegral (Spec (.of k[X])))

instance pointIntegral : IsIntegral (point k).left :=
  inferInstanceAs (IsIntegral (Spec (.of k)))

instance lineIrreducible : IrreducibleSpace (line k).left :=
  inferInstanceAs (IrreducibleSpace (Spec (.of k[X])))

instance pointIrreducible : IrreducibleSpace (point k).left :=
  inferInstanceAs (IrreducibleSpace (Spec (.of k)))

variable {k}

/-- The literal line-target ambient product. -/
abbrev ambient (Y : SmoothSite (Spec (.of k))) : Scheme.{u} :=
  pullback (line k).hom Y.hom

/-- The original reduced support of an actual generic component. -/
abbrev componentSupport {P : Scheme.{u}} (z : genericPoints P) :=
  IntegralClosedSubscheme.pointClosure z.val

section General

variable {X Y : SmoothSite (Spec (.of k))} [IrreducibleSpace X.left]
  {P : Scheme.{u}} [IsNoetherian P] (f : P ⟶ X.left) [IsFinite f]
  (j : P ⟶ pullback X.hom Y.hom) [IsClosedImmersion j]
  (hj : j ≫ pullback.fst X.hom Y.hom = f)
  (hdom : ∀ z : genericPoints P,
    Function.Surjective ((componentSupport z).val.subschemeι ≫ f))

/-- Each original component gives its actual admissible closed image. -/
def genericComponentGenerator (z : genericPoints P) :
    FiniteCorrespondenceGenerator X.hom Y.hom := by
  let C := componentSupport z
  let q := C.val.subschemeι ≫ j
  have : IsFinite (q ≫ pullback.fst X.hom Y.hom) := by
    dsimp only [q]
    rw [Category.assoc, hj]
    infer_instance
  refine ⟨(C.finiteImage j).val, (C.finiteImage j).property,
    isFinite_image_projection q (pullback.fst _ _), ?_⟩
  change Set.range (q.imageι ≫ pullback.fst _ _) ∈ irreducibleComponents _
  rw [range_image_projection]
  change Set.range ((C.val.subschemeι ≫ j) ≫ pullback.fst _ _) ∈ _
  rw [Category.assoc, hj]
  change Set.range ((componentSupport z).val.subschemeι ≫ f) ∈ _
  rw [Set.range_eq_univ.mpr (hdom z)]
  exact (irreducibleComponents_eq_singleton (X := X.left)) ▸ Set.mem_singleton _

/-- The full generic-component sum, with all original local lengths. -/
def genericFundamentalCorrespondence : Cor.mk X ⟶ Cor.mk Y := by
  classical
  let := IntegralCycle.genericPointFintype P
  exact ∑ z, (genericMultiplicity z : ℤ) • (genericComponentGenerator f j hj hdom z).cycle

/-- Forgetting admissibility retains precisely the original fundamental cycle. -/
theorem toIntegralCycle_genericFundamentalCorrespondence :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom)
      (genericFundamentalCorrespondence f j hj hdom) =
      IntegralCycle.finitePushforward j (fundamentalCycle P) := by
  classical
  let := IntegralCycle.genericPointFintype P
  rw [← IntegralCycle.ofGenericCoefficients_genericMultiplicity,
    IntegralCycle.ofGenericCoefficients_eq_sum, map_sum]
  unfold genericFundamentalCorrespondence
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [map_zsmul, FiniteCorrespondenceGenerator.cycle,
    FiniteCorrespondence.toIntegralCycle_single]
  change _ = IntegralCycle.finitePushforward j
    (Finsupp.single (componentSupport z) (genericMultiplicity z : ℤ))
  rw [IntegralCycle.finitePushforward_single, residueDegree_of_surjectiveOnStalks]
  simp only [Nat.cast_one, mul_one, Finsupp.smul_single, smul_eq_mul, mul_one]
  rfl

end General

section Point

variable {Y : SmoothSite (Spec (.of k))} {P : Scheme.{u}} [IsNoetherian P]
  (f : P ⟶ Spec (.of k)) [IsFinite f]
  (j : P ⟶ pullback (point k).hom Y.hom) [IsClosedImmersion j]
  (hj : j ≫ pullback.fst (point k).hom Y.hom = f)

omit [AlgebraicGeometry.IsNoetherian P] [IsFinite f] in
theorem point_component_surjective (z : genericPoints P) :
    Function.Surjective ((componentSupport z).val.subschemeι ≫ f) := by
  let : Subsingleton (Spec (.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  exact Function.surjective_to_subsingleton _

/-- A whole finite scheme over the field gives its full fundamental correspondence. -/
def pointFundamentalCorrespondence : Cor.mk (point k) ⟶ Cor.mk Y :=
  genericFundamentalCorrespondence f j hj (point_component_surjective f)

/-- The field-point adapter preserves all nilpotent and residue multiplicities. -/
theorem toIntegralCycle_pointFundamentalCorrespondence :
    FiniteCorrespondence.toIntegralCycle (f := (point k).hom) (g := Y.hom)
      (pointFundamentalCorrespondence f j hj) =
      IntegralCycle.finitePushforward j (fundamentalCycle P) :=
  toIntegralCycle_genericFundamentalCorrespondence f j hj (point_component_surjective f)

end Point

private theorem finitePushforward_congr {P Q : Scheme.{u}} (f g : P ⟶ Q)
    [IsFinite f] [IsFinite g] (h : f = g) (c : IntegralCycle P) :
    IntegralCycle.finitePushforward f c = IntegralCycle.finitePushforward g c := by
  cases h
  rfl

section Curve

variable {Y : SmoothSite (Spec (.of k))} {P : Scheme.{u}} [IsNoetherian P]
  (f : P ⟶ Spec (.of k[X])) [IsFinite f] [Flat f]
  (j : P ⟶ ambient Y) [IsClosedImmersion j]
  (hj : j ≫ pullback.fst (line k).hom Y.hom = f)

omit [AlgebraicGeometry.IsNoetherian P] in
/-- Flat generalization lifting makes every original component dominate the line. -/
theorem component_surjective (z : genericPoints P) :
    Function.Surjective ((componentSupport z).val.subschemeι ≫ f) :=
  surjective_pointClosure_of_finite_generalizing f (Flat.generalizingMap f) z.val z.property

/-- An actual generic component of the finite-flat curve. -/
abbrev componentGenerator (z : genericPoints P) :
    FiniteCorrespondenceGenerator (line k).hom Y.hom :=
  genericComponentGenerator f j hj (component_surjective f) z

/-- The full finite-flat family, with its original generic multiplicities. -/
def fundamentalCorrespondence : Cor.mk (line k) ⟶ Cor.mk Y :=
  genericFundamentalCorrespondence f j hj (component_surjective f)

/-- The correspondence has exactly the pushed original fundamental cycle. -/
theorem toIntegralCycle_fundamentalCorrespondence :
    FiniteCorrespondence.toIntegralCycle (f := (line k).hom) (g := Y.hom)
      (fundamentalCorrespondence f j hj) =
      IntegralCycle.finitePushforward j (fundamentalCycle P) :=
  toIntegralCycle_genericFundamentalCorrespondence f j hj (component_surjective f)

/-- The literal whole scheme-theoretic evaluation fiber. -/
abbrev fiber (a : k) : Scheme.{u} := FiniteFlatCurve.fiber f a

/-- The whole fiber maps by its original point and target coordinates. -/
def fiberInclusion (a : k) : fiber f a ⟶ pullback (point k).hom Y.hom :=
  pullback.lift (pullback.fst (FiniteFlatCurve.endpoint a) f)
    (pullback.snd (FiniteFlatCurve.endpoint a) f ≫ j ≫ pullback.snd _ _) (by
      have hbase : j ≫ pullback.snd (line k).hom Y.hom ≫ Y.hom =
          f ≫ (line k).hom := by
        rw [← pullback.condition, ← Category.assoc, hj]
      simp only [Category.assoc]
      rw [hbase, ← Category.assoc, ← pullback.condition, Category.assoc]
      exact congrArg
        (fun q => pullback.fst (FiniteFlatCurve.endpoint a) f ≫ q)
        (MorphismProperty.Over.w (evaluationPoint k a)).symm)

omit [AlgebraicGeometry.IsNoetherian P] [IsFinite f] [Flat f] [IsClosedImmersion j] in
@[reassoc (attr := simp)] theorem fiberInclusion_fst (a : k) :
    fiberInclusion f j hj a ≫ pullback.fst _ _ =
      pullback.fst (FiniteFlatCurve.endpoint a) f := pullback.lift_fst _ _ _

omit [AlgebraicGeometry.IsNoetherian P] [IsFinite f] [Flat f] [IsClosedImmersion j] in
@[reassoc (attr := simp)] theorem fiberInclusion_snd (a : k) :
    fiberInclusion f j hj a ≫ pullback.snd _ _ =
      pullback.snd (FiniteFlatCurve.endpoint a) f ≫ j ≫ pullback.snd _ _ :=
  pullback.lift_snd _ _ _

instance fiberInclusion_closed (a : k) : IsClosedImmersion (fiberInclusion f j hj a) := by
  have : IsFinite (fiberInclusion f j hj a ≫ pullback.fst _ _) := by
    rw [fiberInclusion_fst]
    infer_instance
  have : IsFinite (fiberInclusion f j hj a) := IsFinite.of_comp _ (pullback.fst _ _)
  apply (IsClosedImmersion.iff_isFinite_and_mono _).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro W g h heq
  have hfst := congrArg (fun q => q ≫ pullback.fst _ _) heq
  have hsnd := congrArg (fun q => q ≫ pullback.snd _ _) heq
  simp only [Category.assoc, fiberInclusion_fst] at hfst
  simp only [Category.assoc, fiberInclusion_snd] at hsnd
  apply pullback.hom_ext hfst
  apply (cancel_mono j).mp
  apply pullback.hom_ext
  · simp only [Category.assoc, hj]
    rw [← pullback.condition]
    simpa only [Category.assoc] using
      congrArg (fun q => q ≫ FiniteFlatCurve.endpoint a) hfst
  · simpa only [Category.assoc] using hsnd

/-- Closed images identify each original reduced component with its support. -/
def componentSchemeIso (z : genericPoints P) :
    (componentSupport z).val.subscheme ≅ (componentGenerator f j hj z).scheme :=
  asIso ((componentSupport z).val.subschemeι ≫ j).toImage

omit [AlgebraicGeometry.IsNoetherian P] in
@[reassoc (attr := simp)] theorem componentSchemeIso_hom_projection (z : genericPoints P) :
    (componentSchemeIso f j hj z).hom ≫ (componentGenerator f j hj z).projection =
      (componentSupport z).val.subschemeι ≫ f := by
  change ((componentSupport z).val.subschemeι ≫ j).toImage ≫
    ((componentSupport z).val.subschemeι ≫ j).imageι ≫ pullback.fst _ _ = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, Category.assoc, hj]

omit [AlgebraicGeometry.IsNoetherian P] in
@[reassoc (attr := simp)] theorem componentSchemeIso_hom_target (z : genericPoints P) :
    (componentSchemeIso f j hj z).hom ≫ (componentGenerator f j hj z).targetProjection =
      (componentSupport z).val.subschemeι ≫ j ≫ pullback.snd _ _ := by
  change ((componentSupport z).val.subschemeι ≫ j).toImage ≫
    ((componentSupport z).val.subschemeι ≫ j).imageι ≫ pullback.snd _ _ = _
  rw [← Category.assoc, Scheme.Hom.toImage_imageι, Category.assoc]

instance componentGenerator_flat (z : genericPoints P) :
    Flat (componentGenerator f j hj z).projection := by
  have : Flat ((componentSupport z).val.subschemeι ≫ f) :=
    finiteFlatCurve_component_flat f z
  have heq : (componentGenerator f j hj z).projection =
      (componentSchemeIso f j hj z).inv ≫ (componentSupport z).val.subschemeι ≫ f := by
    apply (cancel_epi (componentSchemeIso f j hj z).hom).mp
    simp only [Iso.hom_inv_id_assoc, componentSchemeIso_hom_projection]
  rw [heq]
  infer_instance

/-- The original component's full evaluation fiber. -/
abbrev componentFiber (z : genericPoints P) (a : k) : Scheme.{u} :=
  FiniteFlatCurve.fiber ((componentSupport z).val.subschemeι ≫ f) a

/-- The canonical closed map from an original component fiber into the whole fiber. -/
abbrev componentFiberInclusion (z : genericPoints P) (a : k) :
    componentFiber f z a ⟶ fiber f a :=
  FiniteFlatCurve.fiberMap f a (componentSupport z).val.subschemeι

/-- The component-image isomorphism induces the exact graph-pullback comparison. -/
def componentFiberIso (z : genericPoints P) (a : k) :
    componentFiber f z a ≅ (componentGenerator f j hj z).graphPullback
      (evaluationPoint k a).left :=
  asIso (pullback.map _ _ _ _ (𝟙 _) (componentSchemeIso f j hj z).hom (𝟙 _)
    (by simp only [Category.comp_id, Category.id_comp]; rfl)
    (by simp only [Category.comp_id, componentSchemeIso_hom_projection]))

omit [AlgebraicGeometry.IsNoetherian P] in
/-- The comparison retains both original coordinates of the component fiber. -/
theorem componentFiberIso_hom_inclusion (z : genericPoints P) (a : k) :
    (componentFiberIso f j hj z a).hom ≫
        (componentGenerator f j hj z).graphPullbackMap (evaluationPoint k a).left
          (MorphismProperty.Over.w (evaluationPoint k a)) =
      componentFiberInclusion f z a ≫ fiberInclusion f j hj a := by
  apply pullback.hom_ext
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_fst,
      fiberInclusion_fst, componentFiberIso, asIso_hom, componentFiberInclusion,
      FiniteFlatCurve.fiberMap, pullback.map, pullback.lift_fst, Category.comp_id]
  · simp only [Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_snd,
      fiberInclusion_snd, componentFiberIso, asIso_hom, componentFiberInclusion,
      FiniteFlatCurve.fiberMap, pullback.map, pullback.lift_snd_assoc,
      componentSchemeIso_hom_target]

/-- Restricting one actual component gives its entire, possibly nonreduced fiber. -/
theorem component_graph_restriction (z : genericPoints P) (a : k) :
    FiniteCorrespondence.toIntegralCycle (f := (point k).hom) (g := Y.hom)
      ((Cor.graphFunctor k).map (evaluationPoint k a) ≫
        (show Cor.mk (line k) ⟶ Cor.mk Y from (componentGenerator f j hj z).cycle)) =
      IntegralCycle.finitePushforward (componentFiberInclusion f z a ≫ fiberInclusion f j hj a)
        (fundamentalCycle (componentFiber f z a)) := by
  rw [FiniteCorrespondenceGenerator.toIntegralCycle_graphFunctor_comp]
  rw [← finitePushforward_fundamentalCycle (componentFiberIso f j hj z a).hom,
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  exact finitePushforward_congr _ _ (componentFiberIso_hom_inclusion f j hj z a) _

/-- Actual graph restriction is the pushed fundamental cycle of the WHOLE fiber. -/
theorem toIntegralCycle_graph_restriction (a : k) :
    FiniteCorrespondence.toIntegralCycle (f := (point k).hom) (g := Y.hom)
      ((Cor.graphFunctor k).map (evaluationPoint k a) ≫ fundamentalCorrespondence f j hj) =
      IntegralCycle.finitePushforward (fiberInclusion f j hj a)
        (fundamentalCycle (fiber f a)) := by
  classical
  let := IntegralCycle.genericPointFintype P
  rw [AlgebraicGeometry.finiteFlatCurve_fundamentalCycle_specialization f a, map_sum]
  simp only [fundamentalCorrespondence, genericFundamentalCorrespondence,
    Preadditive.comp_sum, map_sum]
  apply Finset.sum_congr rfl
  intro z _
  change FiniteCorrespondence.toIntegralCycle (f := (point k).hom) (g := Y.hom)
    ((Cor.graphFunctor k).map (evaluationPoint k a) ≫
      ((genericMultiplicity z : ℤ) •
        (show Cor.mk (line k) ⟶ Cor.mk Y from (componentGenerator f j hj z).cycle))) = _
  rw [Preadditive.comp_zsmul, map_zsmul, component_graph_restriction,
    map_zsmul, IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply]

end Curve

end Motivic.FiniteFlatCurveFamily
