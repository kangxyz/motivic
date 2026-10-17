/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoCorestrictionHomology
public import Motivic.Cohomology.Motivic.WeightTwoMixedNorm
public import Motivic.Cohomology.Motivic.WeightTwoFieldChange
public import Motivic.Aglib.AlgebraicGeometry.CorrespondenceIsoTransport

/-!
# Mixed finite-transfer formulas for actual weight-two point cycles

The literal scalar projection sends rational graphs to the whole finite point,
including its original residue degree. Removing the zero simplex and adjoining
a fixed coordinate are actual scheme maps, before passage to raw homology.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

universe u

namespace Motivic.WeightTwoCorestriction

open WeightOnePointNorm WeightOneBoundaryNorm

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

local instance base_integral (F : Type u) [Field F] :
    IsIntegral (SmoothSite.base (Spec (.of F))).left := inferInstanceAs (IsIntegral (Spec (.of F)))

/-- The original smooth-site isomorphism removing the zero simplex. -/
def zeroSourceIso (F : Type u) [Field F] : source F 0 ≅ SmoothSite.base (Spec (.of F)) :=
  baseProductIso F (AlgebraicSimplex.smoothSiteObj F 0) ≪≫ zeroSimplexIso F

/-- The actual graph map into the source-target product. -/
def graphEmbedding {F : Type u} [Field F] {X Y : SmoothSite (Spec (.of F))}
    (f : X ⟶ Y) : X.left ⟶ (SmoothSite.product X Y).left :=
  pullback.lift (𝟙 _) f.left (by simp)

@[reassoc (attr := simp)]
theorem graphEmbedding_fst {F : Type u} [Field F] {X Y : SmoothSite (Spec (.of F))}
    (f : X ⟶ Y) : graphEmbedding f ≫ pullback.fst X.hom Y.hom = 𝟙 _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem graphEmbedding_snd {F : Type u} [Field F] {X Y : SmoothSite (Spec (.of F))}
    (f : X ⟶ Y) : graphEmbedding f ≫ pullback.snd X.hom Y.hom = f.left :=
  pullback.lift_snd _ _ _

instance graphEmbedding_closed {F : Type u} [Field F]
    {X Y : SmoothSite (Spec (.of F))} (f : X ⟶ Y) : IsClosedImmersion (graphEmbedding f) := by
  have : IsSeparated (pullback.fst X.hom Y.hom) := inferInstance
  have : IsClosedImmersion (graphEmbedding f ≫ pullback.fst X.hom Y.hom) := by
    rw [graphEmbedding_fst]
    infer_instance
  exact IsClosedImmersion.of_comp _ (pullback.fst X.hom Y.hom)

/-- An integral graph carries precisely the full source fundamental cycle. -/
theorem toIntegralCycle_graph {F : Type u} [Field F]
    {X Y : SmoothSite (Spec (.of F))} [IsIntegral X.left] (f : X ⟶ Y) :
    FiniteCorrespondence.toIntegralCycle (f := X.hom) (g := Y.hom) ((Cor.graphFunctor F).map f) =
      IntegralCycle.finitePushforward (graphEmbedding f) (fundamentalCycle X.left) := by
  let : IsNoetherian ((𝟭 Scheme).obj X.left) := inferInstanceAs (IsNoetherian X.left)
  let A := graphGeneratorOver f.left (MorphismProperty.Over.w f)
  let : IsNoetherian A.scheme := isNoetherian_of_finiteType A.projection
  let : IsNoetherian (pullback X.hom Y.hom) :=
    isNoetherian_of_finiteType (pullback.fst X.hom Y.hom)
  have he : inv A.projection ≫ A.inclusion = graphEmbedding f := by
    apply pullback.hom_ext
    · change inv A.projection ≫ A.projection = _
      simp only [IsIso.inv_hom_id, graphEmbedding_fst]
    · change inv A.projection ≫ A.targetProjection = _
      rw [← graphGeneratorOver_projection_target f.left (MorphismProperty.Over.w f)]
      change inv A.projection ≫ (A.projection ≫ f.left) = _
      rw [IsIso.inv_hom_id_assoc, graphEmbedding_snd]
  change FiniteCorrespondence.toIntegralCycle
    (componentGraphCycleOver f.left (MorphismProperty.Over.w f)) = _
  rw [componentGraphCycleOver_eq_graphGeneratorOver_cycle,
    FiniteCorrespondenceGenerator.cycle, FiniteCorrespondence.toIntegralCycle_single]
  have hfund : IntegralCycle.finitePushforward A.inclusion (fundamentalCycle A.scheme) =
      Finsupp.single A.toIntegralClosedSubscheme 1 :=
    closedFundamentalCycle_of_isIntegral A.val
  rw [← hfund]
  rw [← finitePushforward_fundamentalCycle (inv A.projection),
    ← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp,
    IntegralCycle.finitePushforward_congr he]
  rfl

/-- The actual scalar projection on the torus target. -/
def torusMap (q : ℕ) : (target E q).left ⟶ (target k q).left :=
  (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k E)) q).inv.left ≫
    pullback.fst (target k q).hom (Spec.map (CommRingCat.ofHom (algebraMap k E)))

@[reassoc (attr := simp)]
theorem ambientMap_snd (r q : ℕ) :
    ambientMap (k := k) (E := E) r q ≫
      pullback.snd (source k r).hom (target k q).hom =
    pullback.snd (source E r).hom (target E q).hom ≫ torusMap (k := k) (E := E) q := by
  let φ := Spec.map (CommRingCat.ofHom (algebraMap k E))
  have h := congrArg (fun f => f.left)
    (SmoothSite.baseChangeProductIso_inv_snd φ (source k r) (target k q))
  have h' := congrArg (fun f => f.left)
    (SmoothSite.productMap_snd
      (SmoothSite.baseSimplexFieldChangeIso (algebraMap k E) ⦋r⦌).inv
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k E)) q).inv)
  dsimp only [MorphismProperty.Comma.comp_left, SmoothSite.productSnd,
    SmoothSite.homMk_left] at h h'
  dsimp only [ambientMap, ambientIso, Iso.trans_inv, MorphismProperty.Comma.comp_left,
    SmoothSite.productIso_inv, torusMap]
  have hn := SmoothSite.baseChange_map_fst φ (SmoothSite.productSnd (source k r) (target k q))
  dsimp only [SmoothSite.productSnd, SmoothSite.homMk_left] at hn
  simp only [Category.assoc]
  have hh := congrArg (fun f => f ≫ pullback.fst (target k q).hom φ) h
  rw [Category.assoc] at hh
  rw [← hn, hh]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f => f ≫ pullback.fst (target k q).hom φ) h').trans
      (Category.assoc _ _ _))

/-- Every target coordinate is the original Laurent coefficient projection. -/
@[reassoc (attr := simp)]
theorem torusMap_coordinate (q : ℕ) (i : Fin q) :
    torusMap (k := k) (E := E) q ≫ (SmoothSite.torusCoordinate (.of k) q i).left =
      (SmoothSite.torusCoordinate (.of E) q i).left ≫
        Spec.map (CommRingCat.PolynomialLaurent.laurentMap
          (CommRingCat.ofHom (algebraMap k E))) := by
  let c := CommRingCat.ofHom (algebraMap k E)
  let t := SmoothSite.torusPowerBaseChangeIso c q
  apply (cancel_epi t.hom.left).mp
  have hc := congrArg (fun f => f.left) (SmoothSite.torusPowerBaseChangeIso_coordinate c q i)
  dsimp only [MorphismProperty.Comma.comp_left] at hc
  change t.hom.left ≫ (t.inv.left ≫ _ ≫ _) = t.hom.left ≫ _ ≫ _
  have hi : t.hom.left ≫ t.inv.left = 𝟙 _ := congrArg (fun f => f.left) t.hom_inv_id
  rw [← Category.assoc, ← Category.assoc, hi, Category.id_comp,
    ← Category.assoc, hc, Category.assoc, SmoothSite.torusBaseChangeIso_hom_coefficientMap]
  exact (SmoothSite.baseChange_map_fst _ (SmoothSite.torusCoordinate (.of k) q i)).symm

@[reassoc (attr := simp)]
theorem torusMap_projection (q : ℕ) :
    torusMap (k := k) (E := E) q ≫ (target k q).hom =
      (target E q).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  unfold torusMap
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    (MorphismProperty.Over.w
      (SmoothSite.torusPowerBaseChangeIso (CommRingCat.ofHom (algebraMap k E)) q).inv)

@[reassoc (attr := simp)]
theorem sourceMap_projection (r : ℕ) :
    sourceMap (k := k) (E := E) r ≫ (source k r).hom =
      (source E r).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  unfold sourceMap
  rw [Category.assoc, pullback.condition, ← Category.assoc]
  exact congrArg (fun f => f ≫ Spec.map (CommRingCat.ofHom (algebraMap k E)))
    (MorphismProperty.Over.w (SmoothSite.baseSimplexFieldChangeIso (algebraMap k E) ⦋r⦌).inv)

/-- The original two-coordinate point over the base, before taking its image. -/
def scalarPoint (f : SmoothSite.base (Spec (.of E)) ⟶ target E 2) :
    Spec (.of E) ⟶ (SmoothSite.product (SmoothSite.base (Spec (.of k))) (target k 2)).left :=
  pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k E)))
    (f.left ≫ torusMap (k := k) 2) (by
      change _ ≫ 𝟙 _ = _
      rw [Category.comp_id, Category.assoc, torusMap_projection, ← Category.assoc,
        MorphismProperty.Over.w]
      change _ = 𝟙 _ ≫ _
      exact (Category.id_comp _).symm)

@[reassoc (attr := simp)]
theorem scalarPoint_fst (f : SmoothSite.base (Spec (.of E)) ⟶ target E 2) :
    scalarPoint (k := k) f ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom (target k 2).hom =
        Spec.map (CommRingCat.ofHom (algebraMap k E)) := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem scalarPoint_snd (f : SmoothSite.base (Spec (.of E)) ⟶ target E 2) :
    scalarPoint (k := k) f ≫
      pullback.snd (SmoothSite.base (Spec (.of k))).hom (target k 2).hom =
        f.left ≫ torusMap (k := k) 2 := pullback.lift_snd _ _ _

variable [Module.Finite k E]

instance scalarPoint_finite (f : SmoothSite.base (Spec (.of E)) ⟶ target E 2) :
    IsFinite (scalarPoint (k := k) f) := by
  have : IsFinite (scalarPoint (k := k) f ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom (target k 2).hom) := by
    rw [scalarPoint_fst]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  exact IsFinite.of_comp _
    (pullback.fst (SmoothSite.base (Spec (.of k))).hom (target k 2).hom)

omit [Module.Finite k E] in
/-- The zero-simplex removal keeps precisely the original source and target projections. -/
theorem scalarPoint_zero_transport (f : SmoothSite.base (Spec (.of E)) ⟶ target E 2) :
    (zeroSourceIso E).inv.left ≫ graphEmbedding ((zeroSourceIso E).hom ≫ f) ≫
      ambientMap (k := k) (E := E) 0 2 ≫
        (Cor.graphTransportIso k (zeroSourceIso k) (Iso.refl (target k 2))).hom =
      scalarPoint (k := k) f := by
  apply pullback.hom_ext
  · simp only [Category.assoc, Cor.graphTransportIso_hom_fst, ambientMap_fst_assoc,
      graphEmbedding_fst_assoc, scalarPoint_fst]
    have hk : (zeroSourceIso k).hom.left = (source k 0).hom := by
      have h := MorphismProperty.Over.w (zeroSourceIso k).hom
      exact (Category.comp_id _).symm.trans h
    rw [hk, sourceMap_projection]
    rw [← Category.assoc, MorphismProperty.Over.w]
    exact Category.id_comp _
  · simp only [Category.assoc, Cor.graphTransportIso_hom_snd, Iso.refl_hom,
      ambientMap_snd_assoc,
      graphEmbedding_snd_assoc, scalarPoint_snd, MorphismProperty.Comma.comp_left]
    have he : (zeroSourceIso E).inv.left ≫ (zeroSourceIso E).hom.left = 𝟙 _ :=
      congrArg (fun f => f.left) (zeroSourceIso E).inv_hom_id
    rw [← Category.assoc, ← Category.assoc, he, Category.id_comp]
    change f.left ≫ torusMap (k := k) 2 ≫ 𝟙 _ = _
    rw [Category.comp_id]

/-- A transferred rational graph is the whole pushed point, with its full multiplicity. -/
theorem toIntegralCycle_pointPushforward_graph
    (f : SmoothSite.base (Spec (.of E)) ⟶ target E 2) :
    FiniteCorrespondence.toIntegralCycle (f := (SmoothSite.base (Spec (.of k))).hom)
      (g := (target k 2).hom) (pointPushforward (k := k) ((Cor.graphFunctor E).map f)) =
        IntegralCycle.finitePushforward (scalarPoint (k := k) f)
          (fundamentalCycle (Spec (.of E))) := by
  rw [pointPushforward_apply]
  change FiniteCorrespondence.toIntegralCycle
    (f := (SmoothSite.base (Spec (.of k))).hom) (g := (target k 2).hom)
    ((Cor.graphFunctor k).map (zeroSourceIso k).inv ≫
      cyclePushforward (k := k) 0 2
        ((Cor.graphFunctor E).map (zeroSourceIso E).hom ≫ (Cor.graphFunctor E).map f)) = _
  rw [Cor.toIntegralCycle_graphIso_comp, toIntegralCycle_cyclePushforward,
    ← Functor.map_comp, toIntegralCycle_graph]
  rw [← finitePushforward_fundamentalCycle (zeroSourceIso E).inv.left]
  simp only [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  erw [← AddMonoidHom.comp_apply, ← IntegralCycle.finitePushforward_comp]
  simp only [Category.assoc]
  rw [IntegralCycle.finitePushforward_congr (scalarPoint_zero_transport f)]
  rfl

omit [Module.Finite k E] in
/-- Scheme maps to a torus power are determined by their scalar and coordinate maps. -/
theorem torusPower_scheme_hom_ext {W : Scheme.{u}} (q : ℕ)
    {f g : W ⟶ (target k q).left}
    (hb : f ≫ (target k q).hom = g ≫ (target k q).hom)
    (hc : ∀ i, f ≫ (SmoothSite.torusCoordinate (.of k) q i).left =
      g ≫ (SmoothSite.torusCoordinate (.of k) q i).left) : f = g := by
  induction q with
  | zero => exact (Category.comp_id f).symm.trans (hb.trans (Category.comp_id g))
  | succ q ih =>
    apply pullback.hom_ext
    · exact hc 0
    · apply ih
      · have hs : pullback.snd (SmoothSite.torus (.of k)).hom (target k q).hom ≫
            (target k q).hom = (target k (q + 1)).hom :=
          MorphismProperty.Over.w (SmoothSite.productSnd (SmoothSite.torus (.of k)) (target k q))
        rw [Category.assoc, hs, Category.assoc, hs]
        exact hb
      · intro i
        have h := hc i.succ
        change f ≫ ((SmoothSite.productSnd (SmoothSite.torus (.of k)) (target k q)).left ≫
          (SmoothSite.torusCoordinate (.of k) q i).left) = _ at h
        exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)

omit [Module.Finite k E] in
/-- An extension-field rational unit retains its literal Laurent evaluation over the base. -/
theorem rationalTorusPoint_scalar (b : Eˣ) :
    (rationalTorusPoint E b).left ≫
      Spec.map (CommRingCat.PolynomialLaurent.laurentMap
        (CommRingCat.ofHom (algebraMap k E))) =
      WeightOneFinitePointNorm.unitTorusPoint (k := k) b := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply CommRingCat.PolynomialLaurent.laurent_hom_ext
  · intro r
    change LaurentPolynomial.eval₂ (RingHom.id E) b
      (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom (algebraMap k E))
        (LaurentPolynomial.C r)) = LaurentPolynomial.eval₂ (algebraMap k E) b
          (LaurentPolynomial.C r)
    rw [CommRingCat.PolynomialLaurent.laurentMap_C]
    simp only [LaurentPolynomial.eval₂_C, RingHom.id_apply]
    rfl
  · change LaurentPolynomial.eval₂ (RingHom.id E) b
      (CommRingCat.PolynomialLaurent.laurentMap (CommRingCat.ofHom (algebraMap k E))
        (LaurentPolynomial.T 1)) = LaurentPolynomial.eval₂ (algebraMap k E) b
          (LaurentPolynomial.T 1)
    rw [CommRingCat.PolynomialLaurent.laurentMap_T]
    simp only [LaurentPolynomial.eval₂_T]

/-- A fixed-coordinate torus section is a genuine closed immersion. -/
instance prependUnit_closed (F : Type u) [Field F] (a : Fˣ) :
    IsClosedImmersion (WeightTwoSymbols.prependUnit F a).left := by
  let d := (SmoothSite.torusCoordinate (.of F) 2 1).left
  have : IsSeparated (d ≫ (SmoothSite.torus (.of F)).hom) := by
    rw [MorphismProperty.Over.w]
    infer_instance
  have : IsSeparated d := IsSeparated.of_comp _ (SmoothSite.torus (.of F)).hom
  have h : (WeightTwoSymbols.prependUnit F a).left ≫ d =
      (SmoothSite.torusPowerOneIso (.of F)).hom.left :=
    congrArg (fun f => f.left)
      (SmoothSite.torusPowerLift_coordinate (.of F) 2
        ![SmoothSite.torusPowerToBase (.of F) 1 ≫ rationalTorusPoint F a,
          SmoothSite.torusCoordinate (.of F) 1 0] 1)
  have : IsClosedImmersion ((WeightTwoSymbols.prependUnit F a).left ≫ d) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _ d

/-- Appending a fixed coordinate is also a genuine closed immersion. -/
instance appendUnit_closed (F : Type u) [Field F] (a : Fˣ) :
    IsClosedImmersion (WeightTwoSymbols.appendUnit F a).left := by
  let d := (SmoothSite.torusCoordinate (.of F) 2 0).left
  have : IsSeparated (d ≫ (SmoothSite.torus (.of F)).hom) := by
    rw [MorphismProperty.Over.w]
    infer_instance
  have : IsSeparated d := IsSeparated.of_comp _ (SmoothSite.torus (.of F)).hom
  have h : (WeightTwoSymbols.appendUnit F a).left ≫ d =
      (SmoothSite.torusPowerOneIso (.of F)).hom.left :=
    congrArg (fun f => f.left)
      (SmoothSite.torusPowerLift_coordinate (.of F) 2
        ![SmoothSite.torusCoordinate (.of F) 1 0,
          SmoothSite.torusPowerToBase (.of F) 1 ≫ rationalTorusPoint F a] 0)
  have : IsClosedImmersion ((WeightTwoSymbols.appendUnit F a).left ≫ d) := by
    rw [h]
    infer_instance
  exact IsClosedImmersion.of_comp _ d

omit [Module.Finite k E] in
/-- The first product projection and every torus coordinate determine the whole point. -/
theorem pointAmbient_hom_ext {W : Scheme.{u}}
    {f g : W ⟶ (SmoothSite.product (SmoothSite.base (Spec (.of k))) (target k 2)).left}
    (hb : f ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom (target k 2).hom =
      g ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom (target k 2).hom)
    (hc : ∀ i, f ≫ pullback.snd (SmoothSite.base (Spec (.of k))).hom (target k 2).hom ≫
        (SmoothSite.torusCoordinate (.of k) 2 i).left =
      g ≫ pullback.snd (SmoothSite.base (Spec (.of k))).hom (target k 2).hom ≫
        (SmoothSite.torusCoordinate (.of k) 2 i).left) : f = g := by
  apply pullback.hom_ext
  · exact hb
  · apply torusPower_scheme_hom_ext 2
    · rw [Category.assoc, ← pullback.condition, ← Category.assoc, hb,
        Category.assoc, pullback.condition, ← Category.assoc]
    · intro i
      exact (Category.assoc _ _ _).trans ((hc i).trans (Category.assoc _ _ _).symm)

omit [Module.Finite k E] in
@[reassoc (attr := simp)]
theorem scalarPoint_coordinate (f : SmoothSite.base (Spec (.of E)) ⟶ target E 2)
    (i : Fin 2) : scalarPoint (k := k) f ≫
      pullback.snd (SmoothSite.base (Spec (.of k))).hom (target k 2).hom ≫
        (SmoothSite.torusCoordinate (.of k) 2 i).left =
      f.left ≫ (SmoothSite.torusCoordinate (.of E) 2 i).left ≫
        Spec.map (CommRingCat.PolynomialLaurent.laurentMap
          (CommRingCat.ofHom (algebraMap k E))) := by
  rw [scalarPoint_snd_assoc, torusMap_coordinate]

@[reassoc (attr := simp)]
theorem rationalPair_coordinate_left (F : Type u) [Field F] (a b : Fˣ) :
    (WeightTwoSymbols.rationalPair F a b).left ≫
      (SmoothSite.torusCoordinate (.of F) 2 0).left = (rationalTorusPoint F a).left :=
  congrArg (fun f => f.left) (SmoothSite.torusPowerLift_coordinate (.of F) 2
    ![rationalTorusPoint F a, rationalTorusPoint F b] 0)

@[reassoc (attr := simp)]
theorem rationalPair_coordinate_right (F : Type u) [Field F] (a b : Fˣ) :
    (WeightTwoSymbols.rationalPair F a b).left ≫
      (SmoothSite.torusCoordinate (.of F) 2 1).left = (rationalTorusPoint F b).left :=
  congrArg (fun f => f.left) (SmoothSite.torusPowerLift_coordinate (.of F) 2
    ![rationalTorusPoint F a, rationalTorusPoint F b] 1)

@[reassoc (attr := simp)]
theorem prependUnit_coordinate_left (F : Type u) [Field F] (a : Fˣ) :
    (WeightTwoSymbols.prependUnit F a).left ≫
      (SmoothSite.torusCoordinate (.of F) 2 0).left =
      (target F 1).hom ≫ (rationalTorusPoint F a).left :=
  congrArg (fun f => f.left) (SmoothSite.torusPowerLift_coordinate (.of F) 2
    ![SmoothSite.torusPowerToBase (.of F) 1 ≫ rationalTorusPoint F a,
      SmoothSite.torusCoordinate (.of F) 1 0] 0)

@[reassoc (attr := simp)]
theorem prependUnit_coordinate_right (F : Type u) [Field F] (a : Fˣ) :
    (WeightTwoSymbols.prependUnit F a).left ≫
      (SmoothSite.torusCoordinate (.of F) 2 1).left =
      (SmoothSite.torusCoordinate (.of F) 1 0).left :=
  congrArg (fun f => f.left) (SmoothSite.torusPowerLift_coordinate (.of F) 2
    ![SmoothSite.torusPowerToBase (.of F) 1 ≫ rationalTorusPoint F a,
      SmoothSite.torusCoordinate (.of F) 1 0] 1)

@[reassoc (attr := simp)]
theorem appendUnit_coordinate_left (F : Type u) [Field F] (a : Fˣ) :
    (WeightTwoSymbols.appendUnit F a).left ≫
      (SmoothSite.torusCoordinate (.of F) 2 0).left =
      (SmoothSite.torusCoordinate (.of F) 1 0).left :=
  congrArg (fun f => f.left) (SmoothSite.torusPowerLift_coordinate (.of F) 2
    ![SmoothSite.torusCoordinate (.of F) 1 0,
      SmoothSite.torusPowerToBase (.of F) 1 ≫ rationalTorusPoint F a] 0)

@[reassoc (attr := simp)]
theorem appendUnit_coordinate_right (F : Type u) [Field F] (a : Fˣ) :
    (WeightTwoSymbols.appendUnit F a).left ≫
      (SmoothSite.torusCoordinate (.of F) 2 1).left =
      (target F 1).hom ≫ (rationalTorusPoint F a).left :=
  congrArg (fun f => f.left) (SmoothSite.torusPowerLift_coordinate (.of F) 2
    ![SmoothSite.torusCoordinate (.of F) 1 0,
      SmoothSite.torusPowerToBase (.of F) 1 ≫ rationalTorusPoint F a] 1)

omit [Module.Finite k E] in
@[reassoc (attr := simp)]
theorem unitPoint_snd_projection (b : Eˣ) :
    WeightOneFinitePointNorm.unitPoint (k := k) b ≫
      pullback.snd (SmoothSite.base (Spec (.of k))).hom (target k 1).hom ≫
        (target k 1).hom = Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  rw [← pullback.condition, ← Category.assoc, WeightOneFinitePointNorm.unitPoint_projection]
  exact Category.comp_id _

omit [Module.Finite k E] in
@[reassoc (attr := simp)]
theorem unitPoint_coordinate (b : Eˣ) :
    WeightOneFinitePointNorm.unitPoint (k := k) b ≫
      pullback.snd (SmoothSite.base (Spec (.of k))).hom (target k 1).hom ≫
        (SmoothSite.torusCoordinate (.of k) 1 0).left =
      WeightOneFinitePointNorm.unitTorusPoint (k := k) b :=
  WeightOneFinitePointNorm.unitPoint_ambientCoordinate b

omit [Module.Finite k E] in
/-- The pushed mixed point is the whole finite unit point with its left coordinate adjoined. -/
theorem scalarPoint_prepend (a : kˣ) (b : Eˣ) :
    scalarPoint (k := k) (WeightTwoSymbols.rationalPair E
      (Units.map (algebraMap k E).toMonoidHom a) b) =
      WeightOneFinitePointNorm.unitPoint (k := k) b ≫
        Cor.graphTargetMap k (SmoothSite.base (Spec (.of k)))
          (WeightTwoSymbols.prependUnit k a) := by
  apply pointAmbient_hom_ext
  · simp only [scalarPoint_fst, Category.assoc, Cor.graphTargetMap_fst,
      WeightOneFinitePointNorm.unitPoint_projection]
  · intro i
    fin_cases i
    · simp only [scalarPoint_coordinate, Category.assoc, Cor.graphTargetMap_snd_assoc]
      erw [rationalPair_coordinate_left_assoc E (Units.map (algebraMap k E).toMonoidHom a) b]
      erw [prependUnit_coordinate_left k a, unitPoint_snd_projection_assoc (k := k) b]
      exact WeightTwoFieldChange.rationalTorusPoint_coefficient (algebraMap k E) a
    · simp only [scalarPoint_coordinate, Category.assoc, Cor.graphTargetMap_snd_assoc]
      erw [rationalPair_coordinate_right_assoc E (Units.map (algebraMap k E).toMonoidHom a) b]
      erw [prependUnit_coordinate_right k a, unitPoint_coordinate (k := k) b]
      exact rationalTorusPoint_scalar (k := k) b

omit [Module.Finite k E] in
/-- The same literal equality with the right coordinate fixed. -/
theorem scalarPoint_append (a : kˣ) (b : Eˣ) :
    scalarPoint (k := k) (WeightTwoSymbols.rationalPair E b
      (Units.map (algebraMap k E).toMonoidHom a)) =
      WeightOneFinitePointNorm.unitPoint (k := k) b ≫
        Cor.graphTargetMap k (SmoothSite.base (Spec (.of k)))
          (WeightTwoSymbols.appendUnit k a) := by
  apply pointAmbient_hom_ext
  · simp only [scalarPoint_fst, Category.assoc, Cor.graphTargetMap_fst,
      WeightOneFinitePointNorm.unitPoint_projection]
  · intro i
    fin_cases i
    · simp only [scalarPoint_coordinate, Category.assoc, Cor.graphTargetMap_snd_assoc]
      erw [rationalPair_coordinate_left_assoc E b (Units.map (algebraMap k E).toMonoidHom a)]
      erw [appendUnit_coordinate_left k a, unitPoint_coordinate (k := k) b]
      exact rationalTorusPoint_scalar (k := k) b
    · simp only [scalarPoint_coordinate, Category.assoc, Cor.graphTargetMap_snd_assoc]
      erw [rationalPair_coordinate_right_assoc E b (Units.map (algebraMap k E).toMonoidHom a)]
      erw [appendUnit_coordinate_right k a, unitPoint_snd_projection_assoc (k := k) b]
      exact WeightTwoFieldChange.rationalTorusPoint_coefficient (algebraMap k E) a

/-- Exact correspondence equality for a fixed left coordinate, retaining the whole finite point. -/
theorem pointPushforward_rationalPair_prepend (a : kˣ) (b : Eˣ) :
    pointPushforward (k := k) ((Cor.graphFunctor E).map
      (WeightTwoSymbols.rationalPair E (Units.map (algebraMap k E).toMonoidHom a) b)) =
      WeightOneFinitePointNorm.unitPointCorrespondence (k := k) b ≫
        (Cor.graphFunctor k).map (WeightTwoSymbols.prependUnit k a) := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_pointPushforward_graph,
    IntegralCycle.finitePushforward_congr (scalarPoint_prepend a b),
    Cor.toIntegralCycle_comp_graph_of_finite,
    WeightOneFinitePointNorm.toIntegralCycle_unitPointCorrespondence,
    IntegralCycle.finitePushforward_comp]
  rfl

/-- Exact correspondence equality for a fixed right coordinate, with its original multiplicity. -/
theorem pointPushforward_rationalPair_append (a : kˣ) (b : Eˣ) :
    pointPushforward (k := k) ((Cor.graphFunctor E).map
      (WeightTwoSymbols.rationalPair E b (Units.map (algebraMap k E).toMonoidHom a))) =
      WeightOneFinitePointNorm.unitPointCorrespondence (k := k) b ≫
        (Cor.graphFunctor k).map (WeightTwoSymbols.appendUnit k a) := by
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_pointPushforward_graph,
    IntegralCycle.finitePushforward_congr (scalarPoint_append a b),
    Cor.toIntegralCycle_comp_graph_of_finite,
    WeightOneFinitePointNorm.toIntegralCycle_unitPointCorrespondence,
    IntegralCycle.finitePushforward_comp]
  rfl

/-- The actual pushed mixed graph gives the original determinant norm symbol on the right. -/
theorem cycleClass_pointPushforward_prepend (a : kˣ) (b : Eˣ) :
    WeightTwoSymbols.cycleClass k (pointPushforward (k := k) ((Cor.graphFunctor E).map
      (WeightTwoSymbols.rationalPair E (Units.map (algebraMap k E).toMonoidHom a) b))) =
      WeightTwoSymbols.graphSymbol k a (Units.map (Algebra.norm k) b) := by
  rw [pointPushforward_rationalPair_prepend, WeightTwoMixedNorm.finite_point_prepend]

/-- The actual pushed mixed graph gives the original determinant norm symbol on the left. -/
theorem cycleClass_pointPushforward_append (a : kˣ) (b : Eˣ) :
    WeightTwoSymbols.cycleClass k (pointPushforward (k := k) ((Cor.graphFunctor E).map
      (WeightTwoSymbols.rationalPair E b (Units.map (algebraMap k E).toMonoidHom a)))) =
      WeightTwoSymbols.graphSymbol k (Units.map (Algebra.norm k) b) a := by
  rw [pointPushforward_rationalPair_append, WeightTwoMixedNorm.finite_point_append]

/-- Genuine weight-two corestriction satisfies the fixed-left-coordinate norm formula. -/
theorem corestriction_graphSymbol_prepend (a : kˣ) (b : Eˣ) :
    corestriction (k := k) (WeightTwoSymbols.graphSymbol E
      (Units.map (algebraMap k E).toMonoidHom a) b) =
      WeightTwoSymbols.graphSymbol k a (Units.map (Algebra.norm k) b) := by
  change corestriction (k := k) (WeightTwoSymbols.cycleClass E _) = _
  rw [corestriction_cycleClass]
  exact cycleClass_pointPushforward_prepend a b

/-- Genuine weight-two corestriction satisfies the fixed-right-coordinate norm formula. -/
theorem corestriction_graphSymbol_append (a : kˣ) (b : Eˣ) :
    corestriction (k := k) (WeightTwoSymbols.graphSymbol E b
      (Units.map (algebraMap k E).toMonoidHom a)) =
      WeightTwoSymbols.graphSymbol k (Units.map (Algebra.norm k) b) a := by
  change corestriction (k := k) (WeightTwoSymbols.cycleClass E _) = _
  rw [corestriction_cycleClass]
  exact cycleClass_pointPushforward_append a b

end Motivic.WeightTwoCorestriction
