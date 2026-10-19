/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Spec.PolynomialQuotient.TwoUnitFamily
public import Motivic.Aglib.RingTheory.Polynomial.Interpolation.TwoUnitDeformation
public import Motivic.Cohomology.WeightTwo.CubicBoundary

/-!
# Whole endpoint cycles for monic two-unit deformations

The auxiliary root coordinate is retained in a closed embedding into
`A¹ × Gm²`. The existing finite-flat curve correspondence is then composed
with the graph of the projection to `Gm²`. This keeps all local lengths and
residue degrees, also when the two unit coordinates identify different points.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open Polynomial.TwoUnitPolynomialFamily
open AlgebraicGeometry.FiniteTwoUnitPolynomialFamily
open scoped BigOperators

universe u

namespace Motivic.WeightTwoMonicDeformation
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite

open WeightTwoCubicBoundary (pairMap pairMap_structure pairMap_comp simplexLineMap
  evaluationPoint_simplexLineMap)

variable {k : Type u} [Field k]

/-- The smooth target retaining the auxiliary affine root coordinate. -/
def retainedTarget (k : Type u) [Field k] : SmoothSite (Spec (.of k)) :=
  SmoothSite.product (AffineLineField.line k) (SmoothSite.torusPower (.of k) 2)

/-- The genuine smooth-site map forgetting only the auxiliary coordinate. -/
def forgetRoot (k : Type u) [Field k] :
    retainedTarget k ⟶ SmoothSite.torusPower (.of k) 2 :=
  SmoothSite.productSnd _ _

/-- The retained root together with the arbitrary original two units. -/
def targetMap (f : k[X][X]) (a b : (AdjoinRoot f)ˣ) :
    familyScheme f ⟶ (retainedTarget k).left :=
  pullback.lift (rootMap f) (pairMap (constantMap f) a b) (by
    rw [pairMap_structure]
    exact rootMap_structure f)

@[reassoc (attr := simp)] theorem targetMap_root (f : k[X][X])
    (a b : (AdjoinRoot f)ˣ) :
    targetMap f a b ≫ pullback.fst _ _ = rootMap f := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem targetMap_pair (f : k[X][X])
    (a b : (AdjoinRoot f)ˣ) :
    targetMap f a b ≫ pullback.snd _ _ = pairMap (constantMap f) a b :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)] theorem targetMap_structure (f : k[X][X])
    (a b : (AdjoinRoot f)ˣ) :
    targetMap f a b ≫ (retainedTarget k).hom =
      Spec.map (CommRingCat.ofHom (constantMap f)) := by
  change targetMap f a b ≫ pullback.fst _ _ ≫ _ = _
  rw [← Category.assoc, targetMap_root]
  exact rootMap_structure f

/-- The ambient keeps parameter, root, and both unit coordinates. -/
abbrev ambient (k : Type u) [Field k] : Scheme.{u} :=
  AffineLineField.ambient (retainedTarget k)

/-- The full family with its original four coordinates. -/
def inclusion (f : k[X][X]) (a b : (AdjoinRoot f)ˣ) : familyScheme f ⟶ ambient k :=
  pullback.lift (projection f) (targetMap f a b) (by
    rw [targetMap_structure]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    rfl)

@[reassoc (attr := simp)] theorem inclusion_fst (f : k[X][X])
    (a b : (AdjoinRoot f)ˣ) :
    inclusion f a b ≫ pullback.fst _ _ = projection f := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem inclusion_snd (f : k[X][X])
    (a b : (AdjoinRoot f)ˣ) :
    inclusion f a b ≫ pullback.snd _ _ = targetMap f a b := pullback.lift_snd _ _ _

/-- Retaining the root makes the entire original family a closed subscheme. -/
theorem inclusion_closed {f : k[X][X]} (hf : f.Monic) (a b : (AdjoinRoot f)ˣ) :
    IsClosedImmersion (inclusion f a b) := by
  apply closedImmersion_of_coordinates hf (inclusion f a b)
    (pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _)
  · exact inclusion_fst f a b
  · rw [inclusion_snd_assoc, targetMap_root]

/-- The full endpoint quotient's retained root. -/
def polynomialRootMap (p : k[X]) : Spec (.of (AdjoinRoot p)) ⟶ Spec (.of k[X]) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.mk p))

instance polynomialRootMap_closed (p : k[X]) : IsClosedImmersion (polynomialRootMap p) := by
  apply IsClosedImmersion.spec_of_surjective
  exact AdjoinRoot.mk_surjective

@[reassoc (attr := simp)] theorem polynomialRootMap_structure (p : k[X]) :
    polynomialRootMap p ≫ Spec.map (CommRingCat.ofHom (C : k →+* k[X])) =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of p)) := by
  rw [polynomialRootMap, ← Spec.map_comp]
  rfl

/-- The full endpoint quotient mapped by its root and actual two units. -/
def polynomialTargetMap (p : k[X]) (a b : (AdjoinRoot p)ˣ) :
    Spec (.of (AdjoinRoot p)) ⟶ (retainedTarget k).left :=
  pullback.lift (polynomialRootMap p) (pairMap (AdjoinRoot.of p) a b) (by
    rw [pairMap_structure]
    exact polynomialRootMap_structure p)

@[reassoc (attr := simp)] theorem polynomialTargetMap_root (p : k[X])
    (a b : (AdjoinRoot p)ˣ) :
    polynomialTargetMap p a b ≫ pullback.fst _ _ = polynomialRootMap p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem polynomialTargetMap_pair (p : k[X])
    (a b : (AdjoinRoot p)ˣ) :
    polynomialTargetMap p a b ≫ pullback.snd _ _ = pairMap (AdjoinRoot.of p) a b :=
  pullback.lift_snd _ _ _

/-- The original point-target ambient with retained root. -/
abbrev pointAmbient (k : Type u) [Field k] : Scheme.{u} :=
  pullback (SmoothSite.base (Spec (.of k))).hom (retainedTarget k).hom

/-- All endpoint components and nilpotents enter the same literal closed inclusion. -/
def polynomialInclusion (p : k[X]) (a b : (AdjoinRoot p)ˣ) :
    Spec (.of (AdjoinRoot p)) ⟶ pointAmbient k :=
  pullback.lift (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p)))
    (polynomialTargetMap p a b) (by
      change Spec.map _ ≫ 𝟙 _ = _ ≫ pullback.fst _ _ ≫ _
      rw [Category.comp_id, ← Category.assoc, polynomialTargetMap_root]
      exact (polynomialRootMap_structure p).symm)

@[reassoc (attr := simp)] theorem polynomialInclusion_fst (p : k[X])
    (a b : (AdjoinRoot p)ˣ) :
    polynomialInclusion p a b ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of p)) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem polynomialInclusion_snd (p : k[X])
    (a b : (AdjoinRoot p)ˣ) :
    polynomialInclusion p a b ≫ pullback.snd _ _ = polynomialTargetMap p a b :=
  pullback.lift_snd _ _ _

instance polynomialInclusion_closed (p : k[X]) (a b : (AdjoinRoot p)ˣ) :
    IsClosedImmersion (polynomialInclusion p a b) := by
  let q := pullback.snd (SmoothSite.base (Spec (.of k))).hom (retainedTarget k).hom ≫
    pullback.fst (AffineLineField.line k).hom (SmoothSite.torusPower (.of k) 2).hom
  have : IsSeparated q := by dsimp only [q]; infer_instance
  have : IsClosedImmersion (polynomialInclusion p a b ≫ q) := by
    dsimp only [q]
    rw [polynomialInclusion_snd_assoc, polynomialTargetMap_root]
    infer_instance
  exact IsClosedImmersion.of_comp (polynomialInclusion p a b) q

/-- The whole endpoint cycle before forgetting its auxiliary coordinate. -/
def retainedPolynomialCycle (p : k[X]) (hp : p.Monic) (a b : (AdjoinRoot p)ˣ) :
    WeightOnePointNorm.point k ⟶ Cor.mk (retainedTarget k) :=
  letI := WeightTwoCubicBoundary.polynomialProjection_finite hp
  FiniteFlatCurveFamily.pointFundamentalCorrespondence
    (Spec.map (CommRingCat.ofHom (AdjoinRoot.of p))) (polynomialInclusion p a b)
    (polynomialInclusion_fst p a b)

/-- Its actual integral cycle has every original generic local length. -/
theorem toIntegralCycle_retainedPolynomialCycle (p : k[X]) (hp : p.Monic)
    (a b : (AdjoinRoot p)ˣ) :
    FiniteCorrespondence.toIntegralCycle (retainedPolynomialCycle p hp a b) =
      IntegralCycle.finitePushforward (polynomialInclusion p a b)
        (fundamentalCycle (Spec (.of (AdjoinRoot p)))) := by
  let := WeightTwoCubicBoundary.polynomialProjection_finite hp
  exact FiniteFlatCurveFamily.toIntegralCycle_pointFundamentalCorrespondence _ _ _

/-- The full two-unit endpoint cycle, including colliding images and residue degrees. -/
def polynomialCycle (p : k[X]) (hp : p.Monic) (a b : (AdjoinRoot p)ˣ) :
    WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k :=
  retainedPolynomialCycle p hp a b ≫ (Cor.graphFunctor k).map (forgetRoot k)

/-- The original finite-flat family in the retained-coordinate smooth target. -/
def retainedCorrespondence (f : k[X][X]) (hf : f.Monic) (a b : (AdjoinRoot f)ˣ) :
    Cor.mk (AffineLineField.line k) ⟶ Cor.mk (retainedTarget k) :=
  letI := projection_finite hf
  letI := projection_flat hf
  letI := inclusion_closed hf a b
  FiniteFlatCurveFamily.fundamentalCorrespondence (projection f) (inclusion f a b)
    (inclusion_fst f a b)

/-- Forgetting the auxiliary root is actual graph composition. -/
def fundamentalCorrespondence (f : k[X][X]) (hf : f.Monic) (a b : (AdjoinRoot f)ˣ) :
    Cor.mk (AffineLineField.line k) ⟶ WeightTwoSymbols.target k :=
  retainedCorrespondence f hf a b ≫ (Cor.graphFunctor k).map (forgetRoot k)

/-- Specialization of a chosen global unit on the whole family. -/
def endpointUnit (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) (a : (AdjoinRoot f)ˣ) : (AdjoinRoot p)ˣ :=
  Units.map (endpoint f s p hp).toMonoidHom a

@[simp] theorem endpointUnit_val (f : k[X][X]) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) (a : (AdjoinRoot f)ˣ) :
    (endpointUnit f s p hp a : AdjoinRoot p) = endpoint f s p hp a := rfl

/-- Scalar specialization preserves the retained root and both actual units. -/
theorem endpoint_targetMap (f : k[X][X]) (a b : (AdjoinRoot f)ˣ)
    (s : k) (p : k[X]) (hp : f.map (evalRingHom s) = p) :
    Spec.map (CommRingCat.ofHom (endpoint f s p hp)) ≫ targetMap f a b =
      polynomialTargetMap p (endpointUnit f s p hp a) (endpointUnit f s p hp b) := by
  apply pullback.hom_ext
  · rw [Category.assoc, targetMap_root, polynomialTargetMap_root]
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply Polynomial.ringHom_ext
    · intro r
      change endpoint f s p hp (eval₂ (constantMap f) (AdjoinRoot.root f) (C r)) =
        AdjoinRoot.mk p (C r)
      rw [eval₂_C, AdjoinRoot.mk_C]
      change endpoint f s p hp (AdjoinRoot.of f (C r)) = AdjoinRoot.of p r
      rw [endpoint_of, eval_C]
    · change endpoint f s p hp (eval₂ (constantMap f) (AdjoinRoot.root f) X) =
        AdjoinRoot.mk p X
      rw [eval₂_X, AdjoinRoot.mk_X, endpoint_root]
  · rw [Category.assoc, targetMap_pair, polynomialTargetMap_pair]
    apply pairMap_comp
    · ext r
      change endpoint f s p hp (AdjoinRoot.of f (C r)) = AdjoinRoot.of p r
      rw [endpoint_of, eval_C]
    · rfl
    · rfl

/-- The full scheme-theoretic fiber in the retained-coordinate ambient. -/
def fiberInclusion (f : k[X][X]) (a b : (AdjoinRoot f)ˣ) (s : k) :
    fiber f s ⟶ pointAmbient k :=
  FiniteFlatCurveFamily.fiberInclusion (projection f) (inclusion f a b)
    (inclusion_fst f a b) s

@[reassoc (attr := simp)] theorem fiberInclusion_fst (f : k[X][X])
    (a b : (AdjoinRoot f)ˣ) (s : k) :
    fiberInclusion f a b s ≫ pullback.fst _ _ =
      pullback.fst (FiniteFlatCurve.endpoint s) (projection f) :=
  FiniteFlatCurveFamily.fiberInclusion_fst _ _ _ _

@[reassoc (attr := simp)] theorem fiberInclusion_snd (f : k[X][X])
    (a b : (AdjoinRoot f)ˣ) (s : k) :
    fiberInclusion f a b s ≫ pullback.snd _ _ =
      pullback.snd (FiniteFlatCurve.endpoint s) (projection f) ≫ targetMap f a b := by
  rw [fiberInclusion, FiniteFlatCurveFamily.fiberInclusion_snd]
  exact congrArg (fun q => pullback.snd (FiniteFlatCurve.endpoint s) (projection f) ≫ q)
    (inclusion_snd f a b)

/-- The whole fiber remains closed because the auxiliary root was retained. -/
theorem fiberInclusion_closed {f : k[X][X]} (hf : f.Monic)
    (a b : (AdjoinRoot f)ˣ) (s : k) : IsClosedImmersion (fiberInclusion f a b s) := by
  let := projection_finite hf
  let := projection_flat hf
  let := inclusion_closed hf a b
  exact FiniteFlatCurveFamily.fiberInclusion_closed _ _ _ _

/-- The full fiber comparison retains all three target coordinates. -/
theorem fiberPolynomialSchemeIso_inv_inclusion
    (f : k[X][X]) (a b : (AdjoinRoot f)ˣ) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) :
    (fiberPolynomialSchemeIso f s p hp).inv ≫ fiberInclusion f a b s =
      polynomialInclusion p (endpointUnit f s p hp a) (endpointUnit f s p hp b) := by
  apply pullback.hom_ext
  · rw [Category.assoc, fiberInclusion_fst, polynomialInclusion_fst,
      fiberPolynomialSchemeIso_inv_fst]
  · rw [Category.assoc, fiberInclusion_snd, polynomialInclusion_snd,
      ← Category.assoc, fiberPolynomialSchemeIso_inv_snd, endpoint_targetMap]

private theorem finitePushforward_congr {P Q : Scheme.{u}} (f g : P ⟶ Q)
    [IsFinite f] [IsFinite g] (h : f = g) (c : IntegralCycle P) :
    IntegralCycle.finitePushforward f c = IntegralCycle.finitePushforward g c := by
  cases h
  rfl

/-- Graph restriction is the full endpoint cycle, prior to forgetting the root. -/
theorem retained_graph_restriction (f : k[X][X]) (hf : f.Monic)
    (a b : (AdjoinRoot f)ˣ) (s : k) (p : k[X])
    (hp : f.map (evalRingHom s) = p) (hpm : p.Monic) :
    (Cor.graphFunctor k).map (AffineLineField.evaluationPoint k s) ≫
        retainedCorrespondence f hf a b =
      retainedPolynomialCycle p hpm (endpointUnit f s p hp a) (endpointUnit f s p hp b) := by
  let := projection_finite hf
  let := projection_flat hf
  let := inclusion_closed hf a b
  let := fiberInclusion_closed hf a b s
  apply FiniteCorrespondence.toIntegralCycle_injective
  refine (FiniteFlatCurveFamily.toIntegralCycle_graph_restriction (projection f)
    (inclusion f a b) (inclusion_fst f a b) s).trans ?_
  refine Eq.trans ?_ (toIntegralCycle_retainedPolynomialCycle p hpm
    (endpointUnit f s p hp a) (endpointUnit f s p hp b)).symm
  change IntegralCycle.finitePushforward (fiberInclusion f a b s)
    (fundamentalCycle (fiber f s)) = _
  rw [← finitePushforward_fundamentalCycle (fiberPolynomialSchemeIso f s p hp).inv,
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  exact finitePushforward_congr _ _
    (fiberPolynomialSchemeIso_inv_inclusion f a b s p hp) _

/-- Graph projection preserves the full restriction, including colliding images. -/
theorem graph_restriction (f : k[X][X]) (hf : f.Monic) (a b : (AdjoinRoot f)ˣ)
    (s : k) (p : k[X]) (hp : f.map (evalRingHom s) = p) (hpm : p.Monic) :
    (Cor.graphFunctor k).map (AffineLineField.evaluationPoint k s) ≫
        fundamentalCorrespondence f hf a b =
      polynomialCycle p hpm (endpointUnit f s p hp a) (endpointUnit f s p hp b) := by
  rw [fundamentalCorrespondence, ← Category.assoc, retained_graph_restriction]
  rfl

/-- The genuine singular one-simplex from the original finite-flat family. -/
def singularCorrespondence (f : k[X][X]) (hf : f.Monic) (a b : (AdjoinRoot f)ˣ) :
    Cor.simplexProduct (WeightOnePointNorm.point k) 1 ⟶ WeightTwoSymbols.target k :=
  (WeightOneBoundaryNorm.simplexProductIso k 1).hom ≫
    (Cor.graphFunctor k).map (simplexLineMap k) ≫ fundamentalCorrespondence f hf a b

/-- The actual first singular face is the entire zero fiber. -/
theorem singularCorrespondence_face_zero (f : k[X][X]) (hf : f.Monic)
    (a b : (AdjoinRoot f)ˣ) (p : k[X]) (hp : f.map (evalRingHom 0) = p)
    (hpm : p.Monic) :
    (WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 0 ≫
          singularCorrespondence f hf a b =
      polynomialCycle p hpm (endpointUnit f 0 p hp a) (endpointUnit f 0 p hp b) := by
  rw [← Category.assoc, WeightOneBoundaryNorm.zeroProductIso_inv_face]
  simp only [singularCorrespondence, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Functor.map_comp, WeightOneBoundaryNorm.facePoint_zero,
    evaluationPoint_simplexLineMap]
  exact graph_restriction f hf a b 0 p hp hpm

/-- The actual second singular face is the entire one fiber. -/
theorem singularCorrespondence_face_one (f : k[X][X]) (hf : f.Monic)
    (a b : (AdjoinRoot f)ˣ) (p : k[X]) (hp : f.map (evalRingHom 1) = p)
    (hpm : p.Monic) :
    (WeightOneBoundaryNorm.zeroProductIso k).inv ≫
        (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ 1 ≫
          singularCorrespondence f hf a b =
      polynomialCycle p hpm (endpointUnit f 1 p hp a) (endpointUnit f 1 p hp b) := by
  rw [← Category.assoc, WeightOneBoundaryNorm.zeroProductIso_inv_face]
  simp only [singularCorrespondence, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Functor.map_comp, WeightOneBoundaryNorm.facePoint_one,
    evaluationPoint_simplexLineMap]
  exact graph_restriction f hf a b 1 p hp hpm

/-- Equality in actual raw `H²²` of the two full endpoint cycles. -/
theorem cycleClass_endpoints (f : k[X][X]) (hf : f.Monic) (a b : (AdjoinRoot f)ˣ)
    (p q : k[X]) (hp : f.map (evalRingHom 0) = p) (hq : f.map (evalRingHom 1) = q)
    (hpm : p.Monic) (hqm : q.Monic) :
    WeightTwoSymbols.cycleClass k
        (polynomialCycle p hpm (endpointUnit f 0 p hp a) (endpointUnit f 0 p hp b)) =
      WeightTwoSymbols.cycleClass k
        (polynomialCycle q hqm (endpointUnit f 1 q hq a) (endpointUnit f 1 q hq b)) := by
  have h := WeightTwoSymbols.cycleClass_endpoints k (singularCorrespondence f hf a b)
  rw [singularCorrespondence_face_zero f hf a b p hp hpm,
    singularCorrespondence_face_one f hf a b q hq hqm] at h
  exact h

open Polynomial.TwoUnitMonicDeformation

/-- The zero specialization is the original polynomial, with its full structure. -/
theorem deformation_specialize_zero (p A B : k[X]) (γ : k) :
    (family p A B γ).map (evalRingHom 0) = p := by
  rw [specialize, endpointPolynomial_zero]

/-- The first coordinate of the original zero endpoint. -/
def zeroFirstUnit (p A B : k[X]) (γ : k) (hcop : IsCoprime p (A * B)) :
    (AdjoinRoot p)ˣ :=
  endpointUnit (family p A B γ) 0 p (deformation_specialize_zero p A B γ)
    (firstUnit p A B γ hcop)

/-- The second coordinate of the original zero endpoint. -/
def zeroSecondUnit (p A B : k[X]) (γ : k) (hcop : IsCoprime p (A * B)) :
    (AdjoinRoot p)ˣ :=
  endpointUnit (family p A B γ) 0 p (deformation_specialize_zero p A B γ)
    (secondUnit p A B γ hcop)

/-- The first coordinate on the whole one endpoint. -/
def oneFirstUnit (p A B : k[X]) (γ : k) (hcop : IsCoprime p (A * B)) :
    (AdjoinRoot (endpointPolynomial p A B γ 1))ˣ :=
  endpointUnit (family p A B γ) 1 (endpointPolynomial p A B γ 1) (specialize p A B γ 1)
    (firstUnit p A B γ hcop)

/-- The second coordinate on the whole one endpoint. -/
def oneSecondUnit (p A B : k[X]) (γ : k) (hcop : IsCoprime p (A * B)) :
    (AdjoinRoot (endpointPolynomial p A B γ 1))ˣ :=
  endpointUnit (family p A B γ) 1 (endpointPolynomial p A B γ 1) (specialize p A B γ 1)
    (secondUnit p A B γ hcop)

@[simp] theorem zeroFirstUnit_val (p A B : k[X]) (γ : k)
    (hcop : IsCoprime p (A * B)) :
    (zeroFirstUnit p A B γ hcop : AdjoinRoot p) = AdjoinRoot.mk p A := by
  simp only [zeroFirstUnit, endpointUnit_val, firstUnit_val, endpoint_coordinate]

@[simp] theorem zeroSecondUnit_val (p A B : k[X]) (γ : k)
    (hcop : IsCoprime p (A * B)) :
    (zeroSecondUnit p A B γ hcop : AdjoinRoot p) = AdjoinRoot.mk p B := by
  simp only [zeroSecondUnit, endpointUnit_val, secondUnit_val, endpoint_coordinate]

@[simp] theorem oneFirstUnit_val (p A B : k[X]) (γ : k)
    (hcop : IsCoprime p (A * B)) :
    (oneFirstUnit p A B γ hcop : AdjoinRoot (endpointPolynomial p A B γ 1)) =
      AdjoinRoot.mk (endpointPolynomial p A B γ 1) A := by
  simp only [oneFirstUnit, endpointUnit_val, firstUnit_val, endpoint_coordinate]

@[simp] theorem oneSecondUnit_val (p A B : k[X]) (γ : k)
    (hcop : IsCoprime p (A * B)) :
    (oneSecondUnit p A B γ hcop : AdjoinRoot (endpointPolynomial p A B γ 1)) =
      AdjoinRoot.mk (endpointPolynomial p A B γ 1) B := by
  simp only [oneSecondUnit, endpointUnit_val, secondUnit_val, endpoint_coordinate]

/-- The full initial polynomial quotient cycle under its actual polynomial units. -/
def zeroCycle (p A B : k[X]) (γ : k) (hp : p.Monic)
    (hcop : IsCoprime p (A * B)) :
    WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k :=
  polynomialCycle p hp (zeroFirstUnit p A B γ hcop) (zeroSecondUnit p A B γ hcop)

/-- The whole deformed endpoint cycle, without discarding repeated or colliding factors. -/
def oneCycle (p A B : k[X]) (γ : k) (hp : p.Monic)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) (hcop : IsCoprime p (A * B)) :
    WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k :=
  polynomialCycle (endpointPolynomial p A B γ 1)
    (endpointPolynomial_monic p A B γ 1 hp hdeg)
    (oneFirstUnit p A B γ hcop) (oneSecondUnit p A B γ hcop)

/-- The actual finite monic two-unit deformation gives equality of full raw `H²²`
endpoint classes. Neither endpoint is reduced or split into selected components. -/
theorem monicDeformation_cycleClass_endpoints (p A B : k[X]) (γ : k) (hp : p.Monic)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) (hcop : IsCoprime p (A * B)) :
    WeightTwoSymbols.cycleClass k (zeroCycle p A B γ hp hcop) =
      WeightTwoSymbols.cycleClass k (oneCycle p A B γ hp hdeg hcop) :=
  cycleClass_endpoints (family p A B γ) (family_monic p A B γ hp hdeg)
    (firstUnit p A B γ hcop) (secondUnit p A B γ hcop)
    p (endpointPolynomial p A B γ 1) (deformation_specialize_zero p A B γ)
    (specialize p A B γ 1) hp (endpointPolynomial_monic p A B γ 1 hp hdeg)

/-- For an irreducible input the balanced-degree hypothesis supplies both units,
so the endpoint relation needs no additional geometric admissibility assumptions. -/
theorem irreducible_cycleClass_endpoints (p A B : k[X]) (γ : k) (hp : p.Monic)
    (hi : Irreducible p) (hA : A ≠ 0) (hB : B ≠ 0)
    (hdeg : A.natDegree + B.natDegree < p.natDegree) :
    WeightTwoSymbols.cycleClass k
        (zeroCycle p A B γ hp (isCoprime_product hi hA hB hdeg)) =
      WeightTwoSymbols.cycleClass k
        (oneCycle p A B γ hp hdeg (isCoprime_product hi hA hB hdeg)) :=
  monicDeformation_cycleClass_endpoints p A B γ hp hdeg (isCoprime_product hi hA hB hdeg)

end Motivic.WeightTwoMonicDeformation
