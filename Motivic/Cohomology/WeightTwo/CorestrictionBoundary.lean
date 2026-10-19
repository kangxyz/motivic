/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.Corestriction
public import Motivic.Cohomology.WeightTwo.CorestrictionSupport
public import Motivic.Cohomology.SuslinVoevodsky.ScalarExtensionSimplexEndpoint
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Endpoints.FiniteCurvePushforwardSpecialization
public import Motivic.Aglib.AlgebraicGeometry.BaseChange.PolynomialFiber
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.LeftComposition

/-!
# Actual one-simplex endpoints under finite field corestriction

Every graph endpoint is the full scheme-theoretic fiber. Its nonreduced local
multiplicities and each original finite-support residue degree are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped Simplicial Polynomial

universe u

namespace Motivic.WeightTwoCorestriction
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- The literal product coface before applying the graph functor. -/
def sourceFace (F : Type u) [Field F] (i : Fin 2) : source F 0 ⟶ source F 1 :=
  SmoothSite.productMap (𝟙 _) ((_root_.AlgebraicSimplex.cosimplicialSmoothSite F).δ i)

/-- The actual closed endpoint map on the source-target ambient scheme. -/
def ambientFace (F : Type u) [Field F] (q : ℕ) (i : Fin 2) :
    (SmoothSite.product (source F 0) (target F q)).left ⟶
      (SmoothSite.product (source F 1) (target F q)).left :=
  (SmoothSite.productMap (sourceFace F i) (𝟙 (target F q))).left

instance ambientFace_isClosedImmersion (F : Type u) [Field F] (q : ℕ) (i : Fin 2) :
    IsClosedImmersion (ambientFace F q i) := by
  let d : SmoothSite.product (source F 1) (target F q) ⟶
      SmoothSite.product (source F 0) (target F q) :=
    SmoothSite.productMap
      (SmoothSite.productMap (𝟙 _) ((_root_.AlgebraicSimplex.cosimplicialSmoothSite F).σ 0))
      (𝟙 _)
  have : IsSeparated (d.left ≫ (SmoothSite.product (source F 0) (target F q)).hom) := by
    rw [MorphismProperty.Over.w]
    infer_instance
  have : IsSeparated d.left := IsSeparated.of_comp _
    (SmoothSite.product (source F 0) (target F q)).hom
  have hc : (_root_.AlgebraicSimplex.cosimplicialSmoothSite F).δ i ≫
      (_root_.AlgebraicSimplex.cosimplicialSmoothSite F).σ (0 : Fin 1) = 𝟙 _ := by
    fin_cases i
    · exact (_root_.AlgebraicSimplex.cosimplicialSmoothSite F).δ_comp_σ_self (i := 0)
    · exact (_root_.AlgebraicSimplex.cosimplicialSmoothSite F).δ_comp_σ_succ (i := 0)
  change _ = 𝟙 (_root_.AlgebraicSimplex.smoothSiteObj F 0) at hc
  have h : ambientFace F q i ≫ d.left = 𝟙 _ := by
    change (SmoothSite.productMap (sourceFace F i) (𝟙 _) ≫ d).left = _
    dsimp only [d, sourceFace]
    rw [← SmoothSite.productMap_comp, ← SmoothSite.productMap_comp,
      Category.id_comp, hc]
    simp only [Category.id_comp, SmoothSite.productMap_id]
    rfl
  have : IsClosedImmersion (ambientFace F q i ≫ d.left) := by rw [h]; infer_instance
  exact IsClosedImmersion.of_comp _ d.left

/-- The canonical ambient comparison preserves the actual simplex coface. -/
theorem ambientIso_face (q : ℕ) (i : Fin 2) :
    (SmoothSite.fieldBaseChange (algebraMap k E)).map
        (SmoothSite.productMap (sourceFace k i) (𝟙 (target k q))) ≫
      (ambientIso (k := k) (E := E) 1 q).hom =
    (ambientIso (k := k) (E := E) 0 q).hom ≫
      SmoothSite.productMap (sourceFace E i) (𝟙 (target E q)) := by
  dsimp only [ambientIso, Iso.trans_hom, SmoothSite.productIso_hom,
    SmoothSite.fieldBaseChange]
  rw [← Category.assoc, SmoothSite.baseChangeProductIso_naturality]
  simp only [Category.assoc, ← SmoothSite.productMap_comp, Category.comp_id]
  have hi := (SmoothSite.baseChange
    (Spec.map (CommRingCat.ofHom (algebraMap k E)))).map_id (target k q)
  rw [hi, Category.id_comp]
  exact congrArg (fun f => (SmoothSite.baseChangeProductIso
    (Spec.map (CommRingCat.ofHom (algebraMap k E))) (source k 0) (target k q)).hom ≫
      SmoothSite.productMap f
        (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k E)) q).hom)
    (SmoothSite.baseSimplexFieldChangeIso_naturality (algebraMap k E)
      (SimplexCategory.δ i))

/-- The coefficient projection commutes with the literal ambient endpoint. -/
theorem ambientMap_face (q : ℕ) (i : Fin 2) :
    ambientFace E q i ≫ ambientMap (k := k) (E := E) 1 q =
      ambientMap (k := k) (E := E) 0 q ≫ ambientFace k q i := by
  have h : SmoothSite.productMap (sourceFace E i) (𝟙 (target E q)) ≫
      (ambientIso (k := k) (E := E) 1 q).inv =
    (ambientIso (k := k) (E := E) 0 q).inv ≫
      (SmoothSite.fieldBaseChange (algebraMap k E)).map
        (SmoothSite.productMap (sourceFace k i) (𝟙 (target k q))) := by
    apply (cancel_mono (ambientIso (k := k) (E := E) 1 q).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [ambientIso_face, Iso.inv_hom_id_assoc]
  have hs := congrArg (fun f => f.left) h
  dsimp only [MorphismProperty.Comma.comp_left] at hs
  unfold ambientMap ambientFace
  rw [← Category.assoc, hs, Category.assoc]
  exact (congrArg (fun f => (ambientIso (k := k) (E := E) 0 q).inv.left ≫ f)
    (SmoothSite.baseChange_map_fst (Spec.map (CommRingCat.ofHom (algebraMap k E)))
      (SmoothSite.productMap (sourceFace k i) (𝟙 (target k q))))).trans
        (Category.assoc _ _ _).symm

/-- Sending the graph fiber back into degree one retains its original support map. -/
theorem graphPullbackMap_ambientFace (F : Type u) [Field F] (q : ℕ)
    (A : FiniteCorrespondenceGenerator (source F 1).hom (target F q).hom) (i : Fin 2) :
    A.graphPullbackMap (sourceFace F i).left (MorphismProperty.Over.w (sourceFace F i)) ≫
      ambientFace F q i =
        pullback.snd (sourceFace F i).left A.projection ≫ A.inclusion := by
  apply pullback.hom_ext
  · have hp := congrArg (fun f => f.left)
      (SmoothSite.productMap_fst (sourceFace F i) (𝟙 (target F q)))
    dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productFst,
      SmoothSite.homMk_left] at hp
    rw [Category.assoc]
    change _ ≫ (SmoothSite.productMap (sourceFace F i) (𝟙 _)).left ≫ _ = _
    rw [hp, ← Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_fst]
    exact pullback.condition
  · have hp := congrArg (fun f => f.left)
      (SmoothSite.productMap_snd (sourceFace F i) (𝟙 (target F q)))
    dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productSnd,
      SmoothSite.homMk_left] at hp
    rw [Category.assoc]
    change _ ≫ (SmoothSite.productMap (sourceFace F i) (𝟙 _)).left ≫ _ = _
    rw [hp]
    change _ ≫ (pullback.snd (source F 0).hom (target F q).hom ≫ 𝟙 _) = _
    rw [Category.comp_id, FiniteCorrespondenceGenerator.graphPullbackMap_snd]
    rfl

open FiniteFlatCurve ScalarExtensionEndpointFiber

/-- Whole scalar-restricted endpoint cycles push with the original generic degree.
The finite map between the integral curves has no flatness hypothesis. -/
theorem finitePushforward_scalar_endpoint {C D T : Scheme.{u}}
    [IsIntegral C] [IsIntegral D]
    (f : D ⟶ Spec (.of k[X])) [IsFinite f] [Surjective f]
    (j : C ⟶ D) [IsFinite j] [Surjective j]
    (e : C ⟶ Spec (.of E[X]))
    (h : e ≫ coefficientMap (algebraMap k E) = j ≫ f)
    (g : D ⟶ T) [IsFinite g] (a : k) :
    let : IsNoetherian D := isNoetherian_of_finiteType f
    let : IsNoetherian C := isNoetherian_of_finiteType j
    IntegralCycle.finitePushforward
        (fiberInclusion e (algebraMap k E a) ≫ j ≫ g)
        (fundamentalCycle (fiber e (algebraMap k E a))) =
      (j.residueDegree (genericPoint C) : ℤ) •
        IntegralCycle.finitePushforward (fiberInclusion f a ≫ g)
          (fundamentalCycle (fiber f a)) := by
  let : IsNoetherian D := isNoetherian_of_finiteType f
  let : IsNoetherian C := isNoetherian_of_finiteType j
  have hs := finitePushforward_fiberInclusion (algebraMap k E) e a (j ≫ g)
  have hs' : IntegralCycle.finitePushforward
      (fiberInclusion (j ≫ f) a ≫ j ≫ g)
      (fundamentalCycle (fiber (j ≫ f) a)) =
    IntegralCycle.finitePushforward
      (fiberInclusion e (algebraMap k E a) ≫ j ≫ g)
      (fundamentalCycle (fiber e (algebraMap k E a))) := by
    exact (congrArg (fun p : C ⟶ Spec (.of k[X]) =>
      IntegralCycle.finitePushforward (fiberInclusion p a ≫ j ≫ g)
        (fundamentalCycle (fiber p a))) h).symm.trans hs
  dsimp only
  rw [← hs']
  have hf := finiteCurve_finitePushforward_fiber f j a
  have hp := congrArg (IntegralCycle.finitePushforward (fiberInclusion f a ≫ g)) hf
  rw [map_zsmul] at hp
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp] at hp
  simpa only [fiberMap_inclusion_assoc] using hp

open ScalarExtensionSimplexEndpoint (sourceChart0 sourceChart1 chartFiberIso)

local instance source_noetherian (F : Type u) [Field F] (r : ℕ) :
    IsNoetherian ((𝟭 Scheme).obj (source F r).left) :=
  inferInstanceAs (IsNoetherian (source F r).left)

local instance source_irreducible (F : Type u) [Field F] (r : ℕ) :
    IrreducibleSpace ((𝟭 Scheme).obj (source F r).left) :=
  inferInstanceAs (IrreducibleSpace (source F r).left)

local instance generator_noetherian (F : Type u) [Field F] (q : ℕ)
    (A : FiniteCorrespondenceGenerator (source F 1).hom (target F q).hom) :
    IsNoetherian A.scheme := isNoetherian_of_finiteType A.projection

local instance generator_projection_surjective (F : Type u) [Field F] (q : ℕ)
    (A : FiniteCorrespondenceGenerator (source F 1).hom (target F q).hom) :
    Surjective A.projection := ⟨A.projection_surjective⟩

/-- Every actual integral one-simplex support is flat over its original parameter. -/
theorem generator_projection_flat (F : Type u) [Field F] (q : ℕ)
    (A : FiniteCorrespondenceGenerator (source F 1).hom (target F q).hom) :
    Flat A.projection := by
  let : Flat (A.projection ≫ (sourceChart1 F).hom) :=
    finiteCurve_flat_of_integral_surjective _
  have h : A.projection = (A.projection ≫ (sourceChart1 F).hom) ≫
      (sourceChart1 F).inv := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

instance sourceFace_isClosedImmersion (F : Type u) [Field F] (i : Fin 2) :
    IsClosedImmersion (sourceFace F i).left := by
  have h : (sourceFace F i).left = (sourceChart0 F).hom ≫
      endpoint (i.val : F) ≫ (sourceChart1 F).inv := by
    apply (cancel_mono (sourceChart1 F).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact ScalarExtensionSimplexEndpoint.faceMap_chart F i
  rw [h]
  infer_instance

private theorem finitePushforward_congr_hom {P Q : Scheme.{u}} (f g : P ⟶ Q)
    [IsFinite f] [IsFinite g] (h : f = g) :
    IntegralCycle.finitePushforward f = IntegralCycle.finitePushforward g := by
  cases h
  rfl

/-- The original graph endpoint, embedded back in degree one, is exactly the
whole literal Cartier fiber with all its original local lengths. -/
theorem toIntegralCycle_face_push (F : Type u) [Field F] (q : ℕ)
    (A : FiniteCorrespondenceGenerator (source F 1).hom (target F q).hom) (i : Fin 2) :
    IntegralCycle.finitePushforward (ambientFace F q i)
      (FiniteCorrespondence.toIntegralCycle
        (f := (source F 0).hom) (g := (target F q).hom)
        ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point F)).δ i ≫
          (show Cor.mk (source F 1) ⟶ Cor.mk (target F q) from A.cycle))) =
    IntegralCycle.finitePushforward
      (fiberInclusion (A.projection ≫ (sourceChart1 F).hom) (i.val : F) ≫ A.inclusion)
      (fundamentalCycle (fiber (A.projection ≫ (sourceChart1 F).hom) (i.val : F))) := by
  let : Flat A.projection := generator_projection_flat F q A
  change IntegralCycle.finitePushforward (ambientFace F q i)
    (FiniteCorrespondence.toIntegralCycle (f := (source F 0).hom) (g := (target F q).hom)
      ((Cor.graphFunctor F).map (sourceFace F i) ≫
        (show Cor.mk (source F 1) ⟶ Cor.mk (target F q) from A.cycle))) = _
  have hh := FiniteCorrespondenceGenerator.toIntegralCycle_graphFunctor_comp F
    (X := source F 0) (Y := source F 1) (Z := target F q) A (sourceFace F i)
  rw [hh]
  change ((IntegralCycle.finitePushforward (ambientFace F q i)).comp
    (IntegralCycle.finitePushforward
      (A.graphPullbackMap (sourceFace F i).left (MorphismProperty.Over.w (sourceFace F i)))))
      (fundamentalCycle (A.graphPullback (sourceFace F i).left)) = _
  rw [← IntegralCycle.finitePushforward_comp,
    finitePushforward_congr_hom _ _ (graphPullbackMap_ambientFace F q A i)]
  have h := finitePushforward_fundamentalCycle (chartFiberIso F A.projection i).hom
  have hp := congrArg (IntegralCycle.finitePushforward
    (fiberInclusion (A.projection ≫ (sourceChart1 F).hom) (i.val : F) ≫ A.inclusion)) h
  rw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp] at hp
  change @Eq (IntegralCycle (pullback (source F 1).hom (target F q).hom)) _ _
  simp only [ScalarExtensionSimplexEndpoint.chartFiberIso_hom_inclusion_assoc] at hp
  exact hp

variable [Module.Finite k E]

/-- Every original integral support has endpoint pushforward with its own generic
residue degree, including all branches and nonreduced endpoint multiplicities. -/
theorem finitePushforward_face_generator (q : ℕ)
    (A : FiniteCorrespondenceGenerator (source E 1).hom (target E q).hom) (i : Fin 2) :
    IntegralCycle.finitePushforward (ambientMap (k := k) (E := E) 0 q)
      (FiniteCorrespondence.toIntegralCycle
        (f := (source E 0).hom) (g := (target E q).hom)
        ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point E)).δ i ≫
          (show Cor.mk (source E 1) ⟶ Cor.mk (target E q) from A.cycle))) =
      ((ambientMap (k := k) (E := E) 1 q).residueDegree A.point : ℤ) •
        FiniteCorrespondence.toIntegralCycle
          (f := (source k 0).hom) (g := (target k q).hom)
          ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ i ≫
            (show Cor.mk (source k 1) ⟶ Cor.mk (target k q) from
              (imageGenerator (k := k) 1 q A).cycle)) := by
  let B := imageGenerator (k := k) 1 q A
  let j := supportMap (k := k) 1 q A
  have he : (A.projection ≫ (sourceChart1 E).hom) ≫ coefficientMap (algebraMap k E) =
      j ≫ (B.projection ≫ (sourceChart1 k).hom) := by
    symm
    change supportMap (k := k) 1 q A ≫
      ((imageGenerator (k := k) 1 q A).projection ≫ (sourceChart1 k).hom) = _
    rw [← Category.assoc, supportMap_projection, Category.assoc]
    exact (congrArg (fun f => A.projection ≫ f)
      (ScalarExtensionSimplexEndpoint.sourceScalarMap_chart1 (algebraMap k E))).trans
        (Category.assoc _ _ _).symm
  apply IntegralCycle.finitePushforward_injective_of_isClosedImmersion (ambientFace k q i)
  rw [map_zsmul, toIntegralCycle_face_push]
  have hc : (IntegralCycle.finitePushforward (ambientFace k q i)).comp
      (IntegralCycle.finitePushforward (ambientMap (k := k) (E := E) 0 q)) =
    (IntegralCycle.finitePushforward (ambientMap (k := k) (E := E) 1 q)).comp
      (IntegralCycle.finitePushforward (ambientFace E q i)) := by
    rw [← IntegralCycle.finitePushforward_comp, ← IntegralCycle.finitePushforward_comp]
    exact finitePushforward_congr_hom _ _ (ambientMap_face q i).symm
  rw [← AddMonoidHom.comp_apply, hc, AddMonoidHom.comp_apply, toIntegralCycle_face_push]
  change ((IntegralCycle.finitePushforward (ambientMap (k := k) (E := E) 1 q)).comp
    (IntegralCycle.finitePushforward
      (fiberInclusion (A.projection ≫ (sourceChart1 E).hom) (i.val : E) ≫ A.inclusion)))
        (fundamentalCycle (fiber (A.projection ≫ (sourceChart1 E).hom) (i.val : E))) = _
  rw [← IntegralCycle.finitePushforward_comp]
  have hp := finitePushforward_scalar_endpoint
    (B.projection ≫ (sourceChart1 k).hom) j
    (A.projection ≫ (sourceChart1 E).hom) he B.inclusion (i.val : k)
  dsimp only at hp
  have ha : algebraMap k E (i.val : k) = (i.val : E) := map_natCast _ _
  have hcast := congrArg (fun a : E => IntegralCycle.finitePushforward
    (fiberInclusion (A.projection ≫ (sourceChart1 E).hom) a ≫ j ≫ B.inclusion)
      (fundamentalCycle (fiber (A.projection ≫ (sourceChart1 E).hom) a))) ha
  have hp' := hcast.symm.trans hp
  change @Eq (IntegralCycle (pullback (source k 1).hom (target k q).hom)) _ _
  simp only [j, B, supportMap_inclusion, supportMap_residueDegree] at hp'
  simp only [Category.assoc]
  exact hp'

/-- Finite field corestriction commutes with each actual one-simplex graph
endpoint on every signed correspondence. -/
theorem cyclePushforward_face (q : ℕ) (i : Fin 2)
    (α : Cor.simplexProduct (WeightOnePointNorm.point E) 1 ⟶ Cor.mk (target E q)) :
    cyclePushforward (k := k) (E := E) 0 q
      ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point E)).δ i ≫ α) =
    (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ i ≫
      cyclePushforward (k := k) (E := E) 1 q α := by
  have h : (cyclePushforward (k := k) (E := E) 0 q).comp
      (Preadditive.leftComp (Cor.mk (target E q))
        ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point E)).δ i)) =
    (Preadditive.leftComp (Cor.mk (target k q))
      ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ i)).comp
        (cyclePushforward (k := k) (E := E) 1 q) := by
    apply Finsupp.addHom_ext'
    intro A
    change FiniteCorrespondenceGenerator (source E 1).hom (target E q).hom at A
    apply AddMonoidHom.ext_int
    change cyclePushforward (k := k) (E := E) 0 q
      ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point E)).δ i ≫
        (show Cor.mk (source E 1) ⟶ Cor.mk (target E q) from A.cycle)) =
      (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ i ≫
        cyclePushforward (k := k) (E := E) 1 q A.cycle
    apply FiniteCorrespondence.toIntegralCycle_injective
    have hp : cyclePushforward (k := k) (E := E) 1 q A.cycle =
        ((ambientMap (k := k) (E := E) 1 q).residueDegree A.point : ℤ) •
          (show Cor.mk (source k 1) ⟶ Cor.mk (target k q) from
            (imageGenerator (k := k) 1 q A).cycle) := by
      change cyclePushforward (k := k) (E := E) 1 q (Finsupp.single A 1) =
        ((ambientMap (k := k) (E := E) 1 q).residueDegree A.point : ℤ) •
          (Finsupp.single (imageGenerator (k := k) 1 q A) 1 :
            FiniteCorrespondence (source k 1).hom (target k q).hom)
      rw [cyclePushforward_single, one_mul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [toIntegralCycle_cyclePushforward, finitePushforward_face_generator,
      hp, Preadditive.comp_zsmul, map_zsmul]
  exact DFunLike.congr_fun h α

end Motivic.WeightTwoCorestriction
