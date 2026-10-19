/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.PointNorm
public import Motivic.Cohomology.WeightOne.FundamentalNorm
public import Motivic.Cohomology.SuslinVoevodsky.FieldCycleEvaluation
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Flat.LeftComposition
public import Motivic.AlgebraicGeometry.Correspondences.Singular.Maps
public import Aglib.RingTheory.PolynomialFiberNorm
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Actual weight-one boundary norms

The degree-zero simplex and the relative base products are identified
explicitly. The coordinate on the one-simplex is its first barycentric
coordinate, so face zero evaluates it at zero and face one at one.

Every actual integral one-simplex support has a finite torsion-free, hence
free, polynomial coordinate algebra. Its actual Laurent unit has constant
norm. The whole geometric fibers are identified with the evaluation tensor
algebras. Flat left-graph composition retains their fundamental-cycle
lengths, and the actual point norm is the determinant norm on those whole
fibers. Therefore every actual signed singular boundary has norm zero.
The canonical shifted raw differential carries its original negative sign,
while the degree-zero graph of a unit maps to the unit itself.

No injectivity or motivic cohomology computation is asserted here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped Simplicial Polynomial

universe u

namespace Motivic.WeightOneBoundaryNorm
open _root_.AlgebraicGeometry.Scheme _root_.CategoryTheory.SingularComplex

variable (k : Type u) [Field k]

private instance baseIntegral : IsIntegral (SmoothSite.base (Spec (.of k))).left :=
  inferInstanceAs (IsIntegral (Spec (.of k)))

/-- Eliminating the sole barycentric coordinate identifies the zero-simplex ring. -/
def zeroCoordinateEquiv : _root_.AlgebraicSimplex.CoordinateRing k 0 ≃ₐ[k] k :=
  (_root_.AlgebraicSimplex.polynomialEquiv k 0).trans (MvPolynomial.isEmptyAlgEquiv k (Fin 0))

/-- The actual first barycentric coordinate is the affine-line coordinate. -/
def oneCoordinateEquiv : _root_.AlgebraicSimplex.CoordinateRing k 1 ≃ₐ[k] k[X] :=
  (_root_.AlgebraicSimplex.polynomialEquiv k 1).trans (MvPolynomial.uniqueAlgEquiv k (Fin 1))

@[simp] theorem oneCoordinateEquiv_coordinate_zero :
    oneCoordinateEquiv k (_root_.AlgebraicSimplex.coordinate k 1 0) = Polynomial.X := by
  change MvPolynomial.uniqueAlgEquiv k (Fin 1)
    (_root_.AlgebraicSimplex.polynomialEquiv k 1
      (_root_.AlgebraicSimplex.coordinate k 1 (0 : Fin 1).castSucc)) = _
  rw [_root_.AlgebraicSimplex.polynomialEquiv_coordinate_castSucc]
  simp [MvPolynomial.uniqueAlgEquiv]

@[simp] theorem zeroCoordinateEquiv_coordinate :
    zeroCoordinateEquiv k (_root_.AlgebraicSimplex.coordinate k 0 0) = 1 := by
  have h : _root_.AlgebraicSimplex.coordinate k 0 0 = 1 := by
    simpa using _root_.AlgebraicSimplex.sum_coordinate k 0
  rw [h, map_one]

/-- The ring inverse is the actual scalar inclusion, rather than an assumed identification. -/
@[simp] theorem zeroCoordinateEquiv_symm_apply (r : k) :
    (zeroCoordinateEquiv k).symm r = _root_.AlgebraicSimplex.constant k 0 r := by
  exact (zeroCoordinateEquiv k).symm.commutes r

/-- The underlying literal zero-simplex is the base spectrum. -/
def zeroSchemeIso : (_root_.AlgebraicSimplex.smoothSiteObj k 0).left ≅ Spec (.of k) :=
  Scheme.Spec.mapIso (zeroCoordinateEquiv k).symm.toRingEquiv.toCommRingCatIso.op

@[simp] theorem zeroSchemeIso_hom :
    (zeroSchemeIso k).hom = _root_.AlgebraicSimplex.structureMap k 0 := by
  change Spec.map _ = Spec.map _
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (zeroCoordinateEquiv_symm_apply k)

/-- The identification is over the original base and hence belongs to the smooth site. -/
def zeroSimplexIso : _root_.AlgebraicSimplex.smoothSiteObj k 0 ≅
    SmoothSite.base (Spec (.of k)) where
  hom := SmoothSite.homMk (zeroSchemeIso k).hom (by
    change (zeroSchemeIso k).hom ≫ 𝟙 _ = _root_.AlgebraicSimplex.structureMap k 0
    rw [Category.comp_id, zeroSchemeIso_hom])
  inv := SmoothSite.homMk (zeroSchemeIso k).inv (by
    change (zeroSchemeIso k).inv ≫ _root_.AlgebraicSimplex.structureMap k 0 = 𝟙 _
    rw [← zeroSchemeIso_hom]
    exact (zeroSchemeIso k).inv_hom_id)
  hom_inv_id := by
    apply MorphismProperty.Over.Hom.ext
    exact (zeroSchemeIso k).hom_inv_id
  inv_hom_id := by
    apply MorphismProperty.Over.Hom.ext
    exact (zeroSchemeIso k).inv_hom_id

/-- Removing the actual relative base factor via the second projection. -/
def baseProductIso (X : SmoothSite (Spec (.of k))) :
    SmoothSite.product (SmoothSite.base (Spec (.of k))) X ≅ X where
  hom := SmoothSite.productSnd _ _
  inv := SmoothSite.productLift (SmoothSite.homMk X.hom (by exact Category.comp_id _)) (𝟙 X)
  hom_inv_id := by
    apply SmoothSite.product_hom_ext
    · rw [Category.assoc, SmoothSite.productLift_fst, Category.id_comp]
      apply MorphismProperty.Over.Hom.ext
      change pullback.snd (𝟙 (Spec (.of k))) X.hom ≫ X.hom =
        pullback.fst (𝟙 (Spec (.of k))) X.hom
      simpa using (pullback.condition (f := 𝟙 (Spec (.of k))) (g := X.hom)).symm
    · simp
  inv_hom_id := by simp

/-- Degree zero of the actual singular product is the actual base correspondence object. -/
def zeroProductIso : Cor.simplexProduct (WeightOnePointNorm.point k) 0 ≅
    WeightOnePointNorm.point k :=
  (Cor.graphFunctor k).mapIso
    (baseProductIso k (_root_.AlgebraicSimplex.smoothSiteObj k 0) ≪≫ zeroSimplexIso k)

/-- Every actual base-simplex product is identified by its literal second projection. -/
def simplexProductIso (n : ℕ) : Cor.simplexProduct (WeightOnePointNorm.point k) n ≅
    Cor.mk (_root_.AlgebraicSimplex.smoothSiteObj k n) :=
  (Cor.graphFunctor k).mapIso (baseProductIso k (_root_.AlgebraicSimplex.smoothSiteObj k n))

/-- The affine scheme chart for the actual one-simplex. -/
def oneSchemeIso : (_root_.AlgebraicSimplex.smoothSiteObj k 1).left ≅ Spec (.of k[X]) :=
  Scheme.Spec.mapIso (oneCoordinateEquiv k).symm.toRingEquiv.toCommRingCatIso.op

/-- In the chosen chart, the inverse polynomial generator is literally `t₀`. -/
@[simp] theorem oneCoordinateEquiv_symm_X :
    (oneCoordinateEquiv k).symm Polynomial.X = _root_.AlgebraicSimplex.coordinate k 1 0 := by
  apply (oneCoordinateEquiv k).injective
  simp

/-- The scalar polynomials are the original simplex constants. -/
@[simp] theorem oneCoordinateEquiv_symm_C (r : k) :
    (oneCoordinateEquiv k).symm (Polynomial.C r) = _root_.AlgebraicSimplex.constant k 1 r :=
  (oneCoordinateEquiv k).symm.commutes r

/-- Face zero is polynomial evaluation at zero for the coordinate `s=t₀`. -/
theorem face_zero_ringHom :
    (zeroCoordinateEquiv k).toRingHom.comp
      ((_root_.AlgebraicSimplex.face k (0 : Fin 2)).comp (oneCoordinateEquiv k).symm.toRingHom) =
        Polynomial.evalRingHom (0 : k) := by
  apply Polynomial.ringHom_ext
  · intro r
    change zeroCoordinateEquiv k (_root_.AlgebraicSimplex.face k (0 : Fin 2)
      ((oneCoordinateEquiv k).symm (Polynomial.C r))) = Polynomial.eval 0 (Polynomial.C r)
    rw [oneCoordinateEquiv_symm_C, _root_.AlgebraicSimplex.face_eq_pullback,
      _root_.AlgebraicSimplex.pullback_constant, Polynomial.eval_C]
    exact (zeroCoordinateEquiv k).commutes r
  · change zeroCoordinateEquiv k (_root_.AlgebraicSimplex.face k (0 : Fin 2)
      ((oneCoordinateEquiv k).symm Polynomial.X)) = Polynomial.eval 0 Polynomial.X
    rw [oneCoordinateEquiv_symm_X, _root_.AlgebraicSimplex.face_coordinate_self,
      map_zero, Polynomial.eval_X]

/-- Face one is polynomial evaluation at one for the same coordinate. -/
theorem face_one_ringHom :
    (zeroCoordinateEquiv k).toRingHom.comp
      ((_root_.AlgebraicSimplex.face k (1 : Fin 2)).comp (oneCoordinateEquiv k).symm.toRingHom) =
        Polynomial.evalRingHom (1 : k) := by
  apply Polynomial.ringHom_ext
  · intro r
    change zeroCoordinateEquiv k (_root_.AlgebraicSimplex.face k (1 : Fin 2)
      ((oneCoordinateEquiv k).symm (Polynomial.C r))) = Polynomial.eval 1 (Polynomial.C r)
    rw [oneCoordinateEquiv_symm_C, _root_.AlgebraicSimplex.face_eq_pullback,
      _root_.AlgebraicSimplex.pullback_constant, Polynomial.eval_C]
    exact (zeroCoordinateEquiv k).commutes r
  · have h : _root_.AlgebraicSimplex.face k (1 : Fin 2)
        (_root_.AlgebraicSimplex.coordinate k 1 0) = _root_.AlgebraicSimplex.coordinate k 0 0 :=
      _root_.AlgebraicSimplex.face_coordinate_succAbove k (1 : Fin 2) (0 : Fin 1)
    change zeroCoordinateEquiv k (_root_.AlgebraicSimplex.face k (1 : Fin 2)
      ((oneCoordinateEquiv k).symm Polynomial.X)) = Polynomial.eval 1 Polynomial.X
    rw [oneCoordinateEquiv_symm_X, h, zeroCoordinateEquiv_coordinate, Polynomial.eval_X]

/-- The literal smooth-site face, with its zero-simplex source identified with the base. -/
def facePoint (i : Fin 2) : SmoothSite.base (Spec (.of k)) ⟶
    _root_.AlgebraicSimplex.smoothSiteObj k 1 :=
  (zeroSimplexIso k).inv ≫ (_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i

/-- A point of the affine coordinate line, transported to the actual simplex. -/
def evaluationPoint (a : k) : SmoothSite.base (Spec (.of k)) ⟶
    _root_.AlgebraicSimplex.smoothSiteObj k 1 :=
  SmoothSite.homMk
    (Spec.map (CommRingCat.ofHom
      ((Polynomial.evalRingHom a).comp (oneCoordinateEquiv k).toRingHom))) (by
      change Spec.map _ ≫ Spec.map _ = 𝟙 (Spec (.of k))
      rw [← Spec.map_comp, ← Spec.map_id]
      congr 1
      apply CommRingCat.hom_ext
      ext r
      change Polynomial.eval a (oneCoordinateEquiv k (algebraMap k _ r)) = r
      rw [(oneCoordinateEquiv k).commutes]
      exact Polynomial.eval_C)

/-- The affine chart sends each genuine evaluation section to the literal evaluation map. -/
theorem evaluationPoint_oneSchemeIso (a : k) :
    (evaluationPoint k a).left ≫ (oneSchemeIso k).hom =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  exact congrArg (Polynomial.eval a) ((oneCoordinateEquiv k).apply_symm_apply p)

/-- The first actual coface is evaluation at zero, not at one. -/
theorem facePoint_zero : facePoint k 0 = evaluationPoint k 0 := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have h := face_zero_ringHom k
  ext p
  have hp := congrArg (fun f : k[X] →+* k => f (oneCoordinateEquiv k p)) h
  change zeroCoordinateEquiv k (_root_.AlgebraicSimplex.face k (0 : Fin 2)
    ((oneCoordinateEquiv k).symm (oneCoordinateEquiv k p))) =
      Polynomial.eval 0 (oneCoordinateEquiv k p) at hp
  change zeroCoordinateEquiv k (_root_.AlgebraicSimplex.face k (0 : Fin 2) p) =
    Polynomial.eval 0 (oneCoordinateEquiv k p)
  simpa only [AlgEquiv.symm_apply_apply] using hp

/-- The second actual coface is evaluation at one. -/
theorem facePoint_one : facePoint k 1 = evaluationPoint k 1 := by
  apply MorphismProperty.Over.Hom.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  have h := face_one_ringHom k
  ext p
  have hp := congrArg (fun f : k[X] →+* k => f (oneCoordinateEquiv k p)) h
  change zeroCoordinateEquiv k (_root_.AlgebraicSimplex.face k (1 : Fin 2)
    ((oneCoordinateEquiv k).symm (oneCoordinateEquiv k p))) =
      Polynomial.eval 1 (oneCoordinateEquiv k p) at hp
  change zeroCoordinateEquiv k (_root_.AlgebraicSimplex.face k (1 : Fin 2) p) =
    Polynomial.eval 1 (oneCoordinateEquiv k p)
  simpa only [AlgEquiv.symm_apply_apply] using hp

/-- Identifying the source zero-simplex turns each actual product coface
into its literal endpoint. -/
theorem zeroProductIso_inv_face (i : Fin 2) :
    (zeroProductIso k).inv ≫ (Cor.simplexProductCosimplicial
      (WeightOnePointNorm.point k)).δ i =
        (Cor.graphFunctor k).map (facePoint k i) ≫ (simplexProductIso k 1).inv := by
  change (Cor.graphFunctor k).map
    ((zeroSimplexIso k).inv ≫ (baseProductIso k (_root_.AlgebraicSimplex.smoothSiteObj k 0)).inv) ≫
      (Cor.graphFunctor k).map (SmoothSite.productMap (𝟙 _)
        ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i)) =
    (Cor.graphFunctor k).map (facePoint k i) ≫
      (Cor.graphFunctor k).map (baseProductIso k (_root_.AlgebraicSimplex.smoothSiteObj k 1)).inv
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  apply (cancel_mono (baseProductIso k (_root_.AlgebraicSimplex.smoothSiteObj k 1)).hom).mp
  have hn : SmoothSite.productMap (𝟙 (SmoothSite.base (Spec (.of k))))
      ((_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i) ≫
      (baseProductIso k (_root_.AlgebraicSimplex.smoothSiteObj k 1)).hom =
    (baseProductIso k (_root_.AlgebraicSimplex.smoothSiteObj k 0)).hom ≫
      (_root_.AlgebraicSimplex.cosimplicialSmoothSite k).δ i :=
    SmoothSite.productMap_snd _ _
  rw [Category.assoc, hn]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rfl

open _root_.AlgebraicSimplex _root_.Motivic.PresheafWithTransfers

/-- The point norm on the actual degree-zero singular quotient,
via the proved base identification. -/
def degreeZeroNorm : sections (reducedTorus k 1)
    (Cor.simplexProduct (WeightOnePointNorm.point k) 0) →+ Additive kˣ :=
  (WeightOnePointNorm.reducedNorm k).comp
    (transfer (reducedTorus k 1) (zeroProductIso k).inv).hom

/-- Its formula on every actual signed represented zero-simplex cycle. -/
theorem degreeZeroNorm_quotient
    (α : Cor.simplexProduct (WeightOnePointNorm.point k) 0 ⟶ WeightOnePointNorm.target k) :
    degreeZeroNorm k ((toReducedTorus k 1).hom.app
      (op (Cor.simplexProduct (WeightOnePointNorm.point k) 0)) (ULift.up α)) =
        WeightOnePointNorm.cycleNorm k ((zeroProductIso k).inv ≫ α) := by
  change WeightOnePointNorm.reducedNorm k
    (transfer (reducedTorus k 1) (zeroProductIso k).inv _) = _
  rw [reducedTorus_transfer_apply, WeightOnePointNorm.reducedNorm_quotient]

/-- Each actual reduced product coface has exactly its endpoint norm, with no hidden sign. -/
theorem degreeZeroNorm_face_quotient (i : Fin 2)
    (α : Cor.simplexProduct (WeightOnePointNorm.point k) 1 ⟶ WeightOnePointNorm.target k) :
    degreeZeroNorm k
      (transfer (reducedTorus k 1)
        ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ i)
        ((toReducedTorus k 1).hom.app
          (op (Cor.simplexProduct (WeightOnePointNorm.point k) 1)) (ULift.up α))) =
      WeightOnePointNorm.cycleNorm k
        ((Cor.graphFunctor k).map (facePoint k i) ≫ (simplexProductIso k 1).inv ≫ α) := by
  have h := reducedTorus_transfer_apply k 1
    (show Cor.simplexProduct (WeightOnePointNorm.point k) 0 ⟶
        Cor.simplexProduct (WeightOnePointNorm.point k) 1 from
      (Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ i) α
  calc
    _ = degreeZeroNorm k ((toReducedTorus k 1).hom.app
        (op (Cor.simplexProduct (WeightOnePointNorm.point k) 0))
        (ULift.up ((Cor.simplexProductCosimplicial
          (WeightOnePointNorm.point k)).δ i ≫ α))) := congrArg (degreeZeroNorm k) h
    _ = _ := by
      rw [degreeZeroNorm_quotient, ← Category.assoc, zeroProductIso_inv_face, Category.assoc]

/-- The actual integral supports of a one-simplex correspondence. -/
abbrev Generator := FiniteCorrespondenceGenerator
  (smoothSiteObj k 1).hom (SmoothSite.torusPower (.of k) 1).hom

private instance simplexIntegral :
    IsIntegral ((𝟭 Scheme).obj (smoothSiteObj k 1).left) :=
  inferInstanceAs (IsIntegral (Spec (.of (CoordinateRing k 1))))

private instance simplexAffine :
    IsAffine ((𝟭 Scheme).obj (smoothSiteObj k 1).left) :=
  inferInstanceAs (IsAffine (Spec (.of (CoordinateRing k 1))))

/-- Polynomial scalars identify the literal global functions on the actual simplex. -/
def simplexGlobalEquiv : Γ((smoothSiteObj k 1).left, ⊤) ≃+* k[X] :=
  (Scheme.ΓSpecIso (.of (CoordinateRing k 1))).commRingCatIsoToRingEquiv.trans
    (oneCoordinateEquiv k).toRingEquiv

variable {k} (Z : Generator k)

/-- Global functions of the whole actual integral support. -/
abbrev coordinateRing : CommRingCat.{u} := Γ(Z.scheme, ⊤)

instance supportAffine : IsAffine Z.scheme := isAffine_of_isAffineHom Z.projection

/-- The literal polynomial scalar map is induced by the finite source projection. -/
def scalarMap : k[X] →+* coordinateRing Z :=
  Z.projection.appTop.hom.comp (simplexGlobalEquiv k).symm.toRingHom

instance coordinateAlgebra : Algebra k[X] (coordinateRing Z) := (scalarMap Z).toAlgebra

/-- Finite source projection gives finite generation over the actual polynomial coordinate. -/
instance coordinateFinite : Module.Finite k[X] (coordinateRing Z) := by
  change (scalarMap Z).Finite
  exact Z.projection.finite_appTop.comp
    (RingHom.Finite.of_surjective _ (simplexGlobalEquiv k).symm.surjective)

/-- Surjectivity over the reduced simplex makes the actual scalar map injective. -/
theorem scalarMap_injective : Function.Injective (scalarMap Z) := by
  let : Surjective Z.projection := ⟨Z.projection_surjective⟩
  let : IsSchemeTheoreticallyDominant Z.projection :=
    IsSchemeTheoreticallyDominant.of_isDominant Z.projection
  have h : Function.Injective Z.projection.appTop := by
    rw [RingHom.injective_iff_ker_eq_bot,
      ← Z.projection.ker_apply ⟨⊤, isAffineOpen_top _⟩, Z.projection.ker_eq_bot]
    simp
  exact h.comp (simplexGlobalEquiv k).symm.injective

/-- The integral support is torsion-free for the literal polynomial action. -/
instance coordinateTorsionFree : Module.IsTorsionFree k[X] (coordinateRing Z) := by
  apply Module.IsTorsionFree.of_smul_eq_zero
  intro r b h
  change scalarMap Z r * b = 0 at h
  rcases mul_eq_zero.mp h with hr | hb
  · exact Or.inl ((scalarMap_injective Z) (hr.trans (map_zero _).symm))
  · exact Or.inr hb

/-- The actual finite torsion-free support algebra is free over the PID `k[X]`. -/
instance coordinateFree : Module.Free k[X] (coordinateRing Z) :=
  Module.free_of_finite_type_torsion_free'

/-- The actual projection is flat, derived from integrality and finite projection. -/
instance projectionFlat : Flat Z.projection := by
  rw [HasRingHomProperty.iff_of_isAffine (P := @Flat)]
  have h : (scalarMap Z).Flat := by
    change Module.Flat k[X] (coordinateRing Z)
    infer_instance
  have he : Z.projection.appTop.hom =
      (scalarMap Z).comp (simplexGlobalEquiv k).toRingHom := by
    ext r
    simp [scalarMap]
  rw [he]
  exact (RingHom.Flat.of_bijective (simplexGlobalEquiv k).bijective).comp h

/-- The actual support affine chart intertwines its source map with polynomial scalars. -/
theorem supportIsoSpec_projection :
    Z.scheme.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (scalarMap Z)) =
      Z.projection ≫ (oneSchemeIso k).hom := by
  have h : Spec.map (CommRingCat.ofHom (scalarMap Z)) =
      Spec.map Z.projection.appTop ≫
        Spec.map (CommRingCat.ofHom (simplexGlobalEquiv k).symm.toRingHom) := by
    rw [← Spec.map_comp]
    rfl
  rw [h, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc]
  congr 1
  change (Spec (.of (CoordinateRing k 1))).isoSpec.hom ≫ _ = _
  rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro p
  change (Scheme.ΓSpecIso (.of (CoordinateRing k 1))).hom
    ((Scheme.ΓSpecIso (.of (CoordinateRing k 1))).inv
      ((oneCoordinateEquiv k).symm p)) = _
  simp

/-- The literal scheme-theoretic fiber over an arbitrary polynomial point. -/
abbrev fiber (a : k) : Scheme.{u} := Z.graphPullback (evaluationPoint k a).left

/-- Its finite structural map to the original field point. -/
abbrev fiberProjection (a : k) : fiber Z a ⟶ Spec (.of k) :=
  pullback.fst (evaluationPoint k a).left Z.projection

/-- The original map from the whole fiber to the torus product. -/
abbrev fiberInclusion (a : k) :=
  Z.graphPullbackMap (evaluationPoint k a).left
    (MorphismProperty.Over.w (evaluationPoint k a))

/-- The whole fiber remains a closed subscheme of the actual point-torus product. -/
instance fiberInclusionClosed (a : k) : IsClosedImmersion (fiberInclusion Z a) := by
  apply (IsClosedImmersion.iff_isFinite_and_mono _).mpr
  refine ⟨inferInstance, ⟨?_⟩⟩
  intro W f g h
  have hfst : f ≫ fiberProjection Z a = g ≫ fiberProjection Z a := by
    simpa only [Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_fst]
      using congrArg (fun t => t ≫ pullback.fst _ _) h
  have hsnd : f ≫ pullback.snd (evaluationPoint k a).left Z.projection ≫ Z.targetProjection =
      g ≫ pullback.snd (evaluationPoint k a).left Z.projection ≫ Z.targetProjection := by
    simpa only [Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_snd]
      using congrArg (fun t => t ≫ pullback.snd _ _) h
  apply pullback.hom_ext hfst
  apply (cancel_mono Z.inclusion).mp
  apply pullback.hom_ext
  · change (f ≫ pullback.snd (evaluationPoint k a).left Z.projection ≫ Z.inclusion) ≫
      pullback.fst _ _ =
        (g ≫ pullback.snd (evaluationPoint k a).left Z.projection ≫ Z.inclusion) ≫
          pullback.fst _ _
    change (f ≫ pullback.snd (evaluationPoint k a).left Z.projection) ≫ Z.projection =
      (g ≫ pullback.snd (evaluationPoint k a).left Z.projection) ≫ Z.projection
    rw [Category.assoc, Category.assoc, ← pullback.condition]
    simpa only [Category.assoc] using congrArg (fun t => t ≫ (evaluationPoint k a).left) hfst
  · simpa only [Category.assoc] using hsnd

/-- The actual affine pullback chart, with the polynomial action given by evaluation. -/
def fiberSchemeIso (a : k) : fiber Z a ≅
    Spec (.of (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a)) := by
  letI : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  have H : IsPullback (fiberProjection Z a)
      (pullback.snd (evaluationPoint k a).left Z.projection ≫ Z.scheme.isoSpec.hom)
      (Spec.map (CommRingCat.ofHom (algebraMap k[X] k)))
      (Spec.map (CommRingCat.ofHom (algebraMap k[X] (coordinateRing Z)))) :=
    (IsPullback.of_hasPullback (evaluationPoint k a).left Z.projection).of_iso
      (Iso.refl _) (Iso.refl _) Z.scheme.isoSpec (oneSchemeIso k)
      (by simp [fiberProjection]) (by simp)
      (by
        change (evaluationPoint k a).left ≫ (oneSchemeIso k).hom =
          𝟙 _ ≫ Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom a))
        rw [Category.id_comp]
        exact evaluationPoint_oneSchemeIso k a)
      (supportIsoSpec_projection Z).symm
  exact H.isoPullback ≪≫ pullbackSpecIso k[X] k (coordinateRing Z)

/-- The inverse fiber chart preserves the actual map to the base point. -/
theorem fiberSchemeIso_inv_fst (a : k) :
    (fiberSchemeIso Z a).inv ≫ fiberProjection Z a =
      Spec.map (CommRingCat.ofHom
        (algebraMap k (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a))) := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  simp only [fiberSchemeIso, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_fst]
  exact pullbackSpecIso_inv_fst' k[X] k (coordinateRing Z)

/-- The inverse fiber chart preserves the original support projection. -/
theorem fiberSchemeIso_inv_snd (a : k) :
    (fiberSchemeIso Z a).inv ≫ pullback.snd (evaluationPoint k a).left Z.projection ≫
      Z.scheme.isoSpec.hom =
      Spec.map (CommRingCat.ofHom
        (Algebra.PolynomialFiber.specialize (coordinateRing Z) a)) := by
  let : Algebra k[X] k := Algebra.PolynomialFiber.evaluationAlgebra a
  simp only [fiberSchemeIso, Iso.trans_inv, Category.assoc, IsPullback.isoPullback_inv_snd]
  exact pullbackSpecIso_inv_snd k[X] k (coordinateRing Z)

/-- The genuine whole fiber has an affine coordinate ring. -/
instance fiberAffine (a : k) : IsAffine (fiber Z a) :=
  isAffine_of_isAffineHom (fiberProjection Z a)

/-- The field action on global functions is induced by the actual finite fiber map. -/
def fiberScalarMap (a : k) : k →+* Γ(fiber Z a, ⊤) :=
  (fiberProjection Z a).appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

instance fiberCoordinateAlgebra (a : k) : Algebra k Γ(fiber Z a, ⊤) :=
  (fiberScalarMap Z a).toAlgebra

instance fiberCoordinateFinite (a : k) : Module.Finite k Γ(fiber Z a, ⊤) := by
  change (fiberScalarMap Z a).Finite
  exact (fiberProjection Z a).finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)

/-- The actual whole-fiber global functions are its literal polynomial evaluation fiber. -/
def fiberGlobalEquiv (a : k) : Γ(fiber Z a, ⊤) ≃+*
    Algebra.PolynomialFiber.Fiber (coordinateRing Z) a :=
  (asIso (fiberSchemeIso Z a).inv.appTop).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso
      (.of (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a))).commRingCatIsoToRingEquiv

/-- The whole-fiber chart preserves the actual scalar action of the original field. -/
theorem fiberGlobalEquiv_scalar (a r : k) :
    fiberGlobalEquiv Z a (algebraMap k Γ(fiber Z a, ⊤) r) =
      algebraMap k (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a) r := by
  change (Scheme.ΓSpecIso (.of (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a))).hom
    ((fiberSchemeIso Z a).inv.appTop
      ((fiberProjection Z a).appTop ((Scheme.ΓSpecIso (.of k)).inv r))) = _
  rw [← CommRingCat.comp_apply (fiberProjection Z a).appTop (fiberSchemeIso Z a).inv.appTop,
    ← Scheme.Hom.comp_appTop, fiberSchemeIso_inv_fst]
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (algebraMap k (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a)))).symm r
  change (Spec.map (CommRingCat.ofHom
      (algebraMap k (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a)))).appTop
    ((Scheme.ΓSpecIso (.of k)).inv r) =
      (Scheme.ΓSpecIso (.of (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a))).inv
        (algebraMap k (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a) r) at h
  rw [h]
  simp

/-- The tensor chart is an algebra equivalence for the genuine geometric field action. -/
def fiberGlobalAlgEquiv (a : k) : Γ(fiber Z a, ⊤) ≃ₐ[k]
    Algebra.PolynomialFiber.Fiber (coordinateRing Z) a :=
  { fiberGlobalEquiv Z a with commutes' := fiberGlobalEquiv_scalar Z a }

/-- Restriction of every actual support function is the tensor specialization map. -/
theorem fiberGlobalEquiv_restrict (a : k) (b : coordinateRing Z) :
    fiberGlobalEquiv Z a
      ((pullback.snd (evaluationPoint k a).left Z.projection).appTop b) =
        Algebra.PolynomialFiber.specialize (coordinateRing Z) a b := by
  have h := congrArg Scheme.Hom.appTop (fiberSchemeIso_inv_snd Z a)
  simp only [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop] at h
  have he := ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (coordinateRing Z)).inv b)
  change (fiberSchemeIso Z a).inv.appTop
    ((pullback.snd (evaluationPoint k a).left Z.projection).appTop
      ((Scheme.ΓSpecIso (coordinateRing Z)).hom
        ((Scheme.ΓSpecIso (coordinateRing Z)).inv b))) =
      (Spec.map (CommRingCat.ofHom
        (Algebra.PolynomialFiber.specialize (coordinateRing Z) a))).appTop
          ((Scheme.ΓSpecIso (coordinateRing Z)).inv b) at he
  simp only [Iso.inv_hom_id_apply] at he
  have hn := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Algebra.PolynomialFiber.specialize (coordinateRing Z) a))).symm b
  change (Spec.map (CommRingCat.ofHom
      (Algebra.PolynomialFiber.specialize (coordinateRing Z) a))).appTop
    ((Scheme.ΓSpecIso (coordinateRing Z)).inv b) =
      (Scheme.ΓSpecIso (.of (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a))).inv
        (Algebra.PolynomialFiber.specialize (coordinateRing Z) a b) at hn
  change (Scheme.ΓSpecIso (.of (Algebra.PolynomialFiber.Fiber (coordinateRing Z) a))).hom
    ((fiberSchemeIso Z a).inv.appTop
      ((pullback.snd (evaluationPoint k a).left Z.projection).appTop b)) = _
  rw [he, hn]
  simp

/-- The original Laurent coordinate pulled back to the entire one-simplex support. -/
def coordinateUnit : (coordinateRing Z)ˣ :=
  Units.map ((Z.targetProjection ≫
    (SmoothSite.torusCoordinate (.of k) 1 0).left).appTop).hom.toMonoidHom
      (laurentGlobalUnit (.of k))

/-- The norm of the actual support coordinate is a constant unit polynomial. -/
theorem coordinate_norm_constant :
    ∃ a : kˣ, Algebra.norm k[X] (coordinateUnit Z : coordinateRing Z) =
      Polynomial.C (a : k) :=
  Algebra.PolynomialFiber.norm_unit_eq_C (coordinateUnit Z)

/-- Determinant norms of the actual support's algebraic fibers agree at all points. -/
theorem coordinate_fiber_norm_eq (a b : k) :
    Algebra.norm k (Algebra.PolynomialFiber.specialize (coordinateRing Z) a
      (coordinateUnit Z : coordinateRing Z)) =
    Algebra.norm k (Algebra.PolynomialFiber.specialize (coordinateRing Z) b
      (coordinateUnit Z : coordinateRing Z)) :=
  Algebra.PolynomialFiber.norm_specialize_eq (coordinateUnit Z) a b

/-- The Laurent unit on the literal whole geometric fiber. -/
def fiberCoordinateUnit (a : k) : Γ(fiber Z a, ⊤)ˣ :=
  Units.map ((fiberInclusion Z a ≫ pullback.snd
      (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) 1).hom ≫
    (SmoothSite.torusCoordinate (.of k) 1 0).left).appTop).hom.toMonoidHom
      (laurentGlobalUnit (.of k))

/-- The geometric Laurent unit restricts to the literal tensor-specialized support unit. -/
theorem fiberGlobalEquiv_coordinate (a : k) :
    fiberGlobalEquiv Z a (fiberCoordinateUnit Z a : Γ(fiber Z a, ⊤)) =
      Algebra.PolynomialFiber.specialize (coordinateRing Z) a
        (coordinateUnit Z : coordinateRing Z) := by
  change fiberGlobalEquiv Z a
    ((fiberInclusion Z a ≫ pullback.snd _ _ ≫
      (SmoothSite.torusCoordinate (.of k) 1 0).left).appTop
        ((laurentGlobalUnit (.of k)).val)) = _
  rw [← Category.assoc, FiniteCorrespondenceGenerator.graphPullbackMap_snd, Category.assoc,
    Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  exact fiberGlobalEquiv_restrict Z a (coordinateUnit Z : coordinateRing Z)

/-- The determinant norm on the actual whole geometric fiber equals its algebraic specialization. -/
theorem fiber_norm_specialize (a : k) :
    Algebra.norm k (fiberCoordinateUnit Z a : Γ(fiber Z a, ⊤)) =
      Algebra.norm k (Algebra.PolynomialFiber.specialize (coordinateRing Z) a
        (coordinateUnit Z : coordinateRing Z)) := by
  have hn (x : Γ(fiber Z a, ⊤)) :
      Algebra.norm k (fiberGlobalAlgEquiv Z a x) = Algebra.norm k x := by
    simp_rw [Algebra.norm_apply, ← LinearMap.det_conj _ (fiberGlobalAlgEquiv Z a).toLinearEquiv]
    congr 1
    ext y
    simp
  rw [← hn]
  congr 1
  exact fiberGlobalEquiv_coordinate Z a

/-- Every two actual geometric fibers have equal norms, including nonreduced fibers. -/
theorem geometric_fiber_norm_eq (a b : k) :
    Algebra.norm k (fiberCoordinateUnit Z a : Γ(fiber Z a, ⊤)) =
      Algebra.norm k (fiberCoordinateUnit Z b : Γ(fiber Z b, ⊤)) := by
  rw [fiber_norm_specialize, fiber_norm_specialize]
  exact coordinate_fiber_norm_eq Z a b

/-- Equality is in the original field's unit group and retains the actual global Laurent units. -/
theorem geometric_fiber_unitNorm_eq (a b : k) :
    Units.map (Algebra.norm k) (fiberCoordinateUnit Z a) =
      Units.map (Algebra.norm k) (fiberCoordinateUnit Z b) := by
  apply Units.ext
  exact geometric_fiber_norm_eq Z a b

/-- The actual endpoint correspondence norm equals the determinant norm on its whole fiber. -/
theorem cycleNorm_endpoint_generator (a : k) :
    WeightOnePointNorm.cycleNorm k
      ((Cor.graphFunctor k).map (evaluationPoint k a) ≫
        (show Cor.mk (smoothSiteObj k 1) ⟶ WeightOnePointNorm.target k from
          Z.cycle)) =
      Additive.ofMul (Units.map (Algebra.norm k) (fiberCoordinateUnit Z a)) := by
  have h := WeightOneFundamentalNorm.cycleNorm_eq_norm_of_fundamental
    (fiberProjection Z a) (fiberInclusion Z a)
    (Z.graphPullbackMap_fst (evaluationPoint k a).left
      (MorphismProperty.Over.w (evaluationPoint k a)))
    ((Cor.graphFunctor k).map (evaluationPoint k a) ≫
      (show Cor.mk (smoothSiteObj k 1) ⟶ WeightOnePointNorm.target k from
        Z.cycle))
    (Z.toIntegralCycle_graphFunctor_comp k (evaluationPoint k a))
  exact h

/-- Every actual integral one-simplex correspondence has equal endpoint norms. -/
theorem cycleNorm_endpoint_generator_eq (a b : k) :
    WeightOnePointNorm.cycleNorm k
      ((Cor.graphFunctor k).map (evaluationPoint k a) ≫
        (show Cor.mk (smoothSiteObj k 1) ⟶ WeightOnePointNorm.target k from
          Z.cycle)) =
    WeightOnePointNorm.cycleNorm k
      ((Cor.graphFunctor k).map (evaluationPoint k b) ≫
        (show Cor.mk (smoothSiteObj k 1) ⟶ WeightOnePointNorm.target k from
          Z.cycle)) := by
  rw [cycleNorm_endpoint_generator, cycleNorm_endpoint_generator,
    geometric_fiber_unitNorm_eq Z a b]

variable {Z}

/-- The endpoint equality extends to all actual signed one-simplex correspondences. -/
theorem cycleNorm_endpoint_eq
    (α : Cor.mk (smoothSiteObj k 1) ⟶ WeightOnePointNorm.target k)
    (a b : k) :
    WeightOnePointNorm.cycleNorm k ((Cor.graphFunctor k).map (evaluationPoint k a) ≫ α) =
      WeightOnePointNorm.cycleNorm k ((Cor.graphFunctor k).map (evaluationPoint k b) ≫ α) := by
  have h : (WeightOnePointNorm.cycleNorm k).comp
        (Preadditive.leftComp (WeightOnePointNorm.target k)
          ((Cor.graphFunctor k).map (evaluationPoint k a))) =
      (WeightOnePointNorm.cycleNorm k).comp
        (Preadditive.leftComp (WeightOnePointNorm.target k)
          ((Cor.graphFunctor k).map (evaluationPoint k b))) := by
    apply Finsupp.addHom_ext'
    intro Z
    apply AddMonoidHom.ext_int
    exact cycleNorm_endpoint_generator_eq Z a b
  exact DFunLike.congr_fun h α

variable (k)

/-- The original singular differential is exactly the difference of its two actual cofaces. -/
theorem singular_d_one_zero :
    (singularObj (reducedTorus k 1) (WeightOnePointNorm.point k)).d 1 0 =
      transfer (reducedTorus k 1)
        ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ (0 : Fin 2)) -
      transfer (reducedTorus k 1)
        ((Cor.simplexProductCosimplicial (WeightOnePointNorm.point k)).δ (1 : Fin 2)) :=
  SingularComplex.obj_d_one_zero _ _

/-- The point norm kills every actual degree-one singular boundary
in the genuine reduced quotient. -/
theorem degreeZeroNorm_boundary
    (s : sections (reducedTorus k 1) (Cor.simplexProduct (WeightOnePointNorm.point k) 1)) :
    degreeZeroNorm k
      ((singularObj (reducedTorus k 1) (WeightOnePointNorm.point k)).d 1 0 s) = 0 := by
  obtain ⟨⟨α⟩, rfl⟩ := toReducedTorus_surjective k 1
    (Cor.simplexProduct (WeightOnePointNorm.point k) 1) s
  rw [singular_d_one_zero]
  change degreeZeroNorm k (_ - _) = 0
  rw [map_sub, degreeZeroNorm_face_quotient, degreeZeroNorm_face_quotient,
    facePoint_zero, facePoint_one, cycleNorm_endpoint_eq _ 0 1, sub_self]

/-- The canonical weight-one negative sign is also annihilated, with no inverse in degree zero. -/
theorem degreeZeroNorm_negative_boundary
    (s : sections (reducedTorus k 1) (Cor.simplexProduct (WeightOnePointNorm.point k) 1)) :
    degreeZeroNorm k
      (-((singularObj (reducedTorus k 1) (WeightOnePointNorm.point k)).d 1 0 s)) = 0 := by
  rw [map_neg, degreeZeroNorm_boundary, neg_zero]

/-- The point norm on the actual shifted raw weight-one cochain term. -/
def rawDegreeZeroNorm : (motivicRawBaseComplex k 1).X 1 →+ Additive kˣ :=
  (degreeZeroNorm k).comp (motivicRawBaseComplexXIso k 1 0).hom.hom

private theorem raw_d (q r t : ℕ) :
    (motivicRawBaseComplex k q).d (Indexing.singularDegree q r)
        (Indexing.singularDegree q t) =
      (-1 : ℤ) ^ q • ((motivicRawBaseComplexXIso k q r).hom ≫
        (singularObj (reducedTorus k q) (WeightOnePointNorm.point k)).d r t ≫
          (motivicRawBaseComplexXIso k q t).inv) := by
  let E := toPresheaf k ⋙
    (CategoryTheory.evaluation _ AddCommGrpCat.{u + 1}).obj
      (op (SmoothSite.base (Spec (.of k))))
  calc
    _ = E.map (((singularCochainComplex (reducedTorus k q) 0)⟦-(q : ℤ)⟧).d
        (Indexing.singularDegree q r) (Indexing.singularDegree q t)) := by
      simp only [CochainComplex.shiftFunctor_obj_d', Units.smul_def,
        CategoryTheory.Functor.map_zsmul]
      rfl
    _ = _ := by
      change E.map
          ((((singularComplex (reducedTorus k q)).extend
            (ComplexShape.embeddingUpIntLE 0))⟦-(q : ℤ)⟧).d
              ((q : ℤ) - r) ((q : ℤ) - t)) =
        (-1 : ℤ) ^ q •
          (E.map (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso
              (singularComplex (reducedTorus k q)) q r rfl).hom ≫
            E.map ((singularComplex (reducedTorus k q)).d r t) ≫
            E.map (_root_.HomologicalComplex.ExtensionSignedShift.shiftedXIso
              (singularComplex (reducedTorus k q)) q t rfl).inv)
      simpa only [Units.smul_def, CategoryTheory.Functor.map_zsmul,
        CategoryTheory.Functor.map_comp, Int.negOnePow_neg, Int.coe_negOnePow_natCast] using
        congrArg (fun f => E.map f)
          (_root_.HomologicalComplex.ExtensionSignedShift.shifted_d (singularComplex (reducedTorus k
              q)) q r t)

/-- The actual raw complex has the canonical negative weight-one differential. -/
theorem raw_d_zero_one :
    (motivicRawBaseComplex k 1).d 0 1 =
      -((motivicRawBaseComplexXIso k 1 1).hom ≫
        (singularObj (reducedTorus k 1) (WeightOnePointNorm.point k)).d 1 0 ≫
          (motivicRawBaseComplexXIso k 1 0).inv) := by
  have h := raw_d k 1 1 0
  change (motivicRawBaseComplex k 1).d 0 1 =
    (-1 : ℤ) • ((motivicRawBaseComplexXIso k 1 1).hom ≫
      (singularObj (reducedTorus k 1) (WeightOnePointNorm.point k)).d 1 0 ≫
        (motivicRawBaseComplexXIso k 1 0).inv) at h
  simpa only [neg_one_zsmul] using h

/-- Every actual boundary of the canonical signed raw complex has norm zero. -/
theorem rawDegreeZeroNorm_boundary (s : (motivicRawBaseComplex k 1).X 0) :
    rawDegreeZeroNorm k ((motivicRawBaseComplex k 1).d 0 1 s) = 0 := by
  rw [raw_d_zero_one]
  change degreeZeroNorm k
    ((motivicRawBaseComplexXIso k 1 0).hom
      (-((motivicRawBaseComplexXIso k 1 0).inv
        ((singularObj (reducedTorus k 1) (WeightOnePointNorm.point k)).d 1 0
          ((motivicRawBaseComplexXIso k 1 1).hom s))))) = 0
  rw [map_neg, Iso.inv_hom_id_apply]
  exact degreeZeroNorm_negative_boundary k _

/-- Degree zero of the canonical raw complex sends the actual graph of a unit to that unit. -/
theorem rawDegreeZeroNorm_graph_unit (a : kˣ) :
    rawDegreeZeroNorm k ((motivicRawBaseComplexXIso k 1 0).inv
      ((toReducedTorus k 1).hom.app
        (op (Cor.simplexProduct (WeightOnePointNorm.point k) 0))
        (ULift.up ((zeroProductIso k).hom ≫
          (Cor.graphFunctor k).map (WeightOnePointNorm.rationalPoint k a))))) =
      Additive.ofMul a := by
  change degreeZeroNorm k
    ((motivicRawBaseComplexXIso k 1 0).hom ((motivicRawBaseComplexXIso k 1 0).inv _)) = _
  rw [Iso.inv_hom_id_apply, degreeZeroNorm_quotient, Iso.inv_hom_id_assoc,
    WeightOnePointNorm.cycleNorm_graph_unit]

end Motivic.WeightOneBoundaryNorm
