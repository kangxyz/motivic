/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightTwo.ScalarPairChange
public import Aglib.KTheory.MilnorK.K3.ResidueSupport
public import Mathlib.FieldTheory.PrimitiveElement

/-!
# Exact polynomial presentations of weight-two point generators

The entire global field of an actual finite integral support admits a primitive
element in characteristic zero. Its monic irreducible minimal polynomial gives
a literal `AdjoinRoot` presentation preserving the original scalar map, both
Laurent units, and the entire closed immersion. Thus the original generator is
exactly the existing point pushforward of a rational pair, before passing to
homology. Neither individual Laurent coordinate is assumed to generate the
field, and no injectivity of images of different points is used.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial
open AlgebraicGeometry.Scheme.PolynomialLaurent

universe u

namespace Motivic.WeightTwoPointPresentation
open _root_.AlgebraicGeometry.Scheme

open WeightOneInterpolationCycle WeightTwoCubicBoundary WeightTwoCorestriction
open WeightTwoPolynomialTransfer MilnorK.K3.PolynomialResidue

variable (k : Type u) [Field k]

/-- An original geometric generator of the two-coordinate point cycle group. -/
abbrev Generator := FiniteCorrespondenceGenerator
  (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) 2).hom

variable {k} (Z : Generator k)

/-- The global algebra of the entire joint support, retaining both coordinates. -/
abbrev coordinateRing : CommRingCat.{u} := Γ(Z.scheme, ⊤)

instance supportAffine : IsAffine Z.scheme := by
  let : IsAffine ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
    inferInstanceAs (IsAffine (Spec (.of k)))
  exact isAffine_of_isAffineHom Z.projection

/-- The original support, with its actual global affine chart. -/
def supportIsoSpec : Z.scheme ≅ Spec (coordinateRing Z) := Z.scheme.isoSpec

/-- The scalar homomorphism induced by the original source projection. -/
def scalarMap : k →+* coordinateRing Z :=
  (Z.projection.appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

instance coordinateAlgebra : Algebra k (coordinateRing Z) := (scalarMap Z).toAlgebra

instance coordinateFinite : Module.Finite k (coordinateRing Z) := by
  let : IsAffine ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
    inferInstanceAs (IsAffine (Spec (.of k)))
  change (scalarMap Z).Finite
  exact Z.projection.finite_appTop.comp
    (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)

/-- The entire integral finite support has a field of global functions. -/
theorem coordinateRing_isField : IsField (coordinateRing Z) :=
  isField_of_universallyClosed k Z.projection

noncomputable instance coordinateField : Field (coordinateRing Z) :=
  (coordinateRing_isField Z).toField

/-- The specified original Laurent coordinate on the full joint support. -/
def coordinateUnit (i : Fin 2) : (coordinateRing Z)ˣ :=
  Units.map ((Z.targetProjection ≫
    (SmoothSite.torusCoordinate (.of k) 2 i).left).appTop).hom.toMonoidHom
      (laurentGlobalUnit (.of k))

/-- The literal projection to either Laurent coordinate. -/
def coordinateProjection (i : Fin 2) : Z.scheme ⟶ (SmoothSite.torus (.of k)).left :=
  Z.targetProjection ≫ (SmoothSite.torusCoordinate (.of k) 2 i).left

/-- Both coordinates use precisely the original support scalar action. -/
theorem coordinateProjection_structure (i : Fin 2) :
    coordinateProjection Z i ≫ (SmoothSite.torus (.of k)).hom = Z.projection := by
  rw [coordinateProjection, Category.assoc,
    MorphismProperty.Over.w (SmoothSite.torusCoordinate (.of k) 2 i)]
  have h := Z.projection_base.symm
  change _ = Z.projection ≫ 𝟙 _ at h
  simpa only [Category.comp_id] using h

/-- Pullback along each actual coordinate is evaluation at that original unit. -/
theorem coordinatePullback_eq_eval (i : Fin 2) :
    affinePullback (coordinateProjection Z i) =
      LaurentPolynomial.eval₂ (scalarMap Z) (coordinateUnit Z i) := by
  apply laurentRingHom_ext
  · have hs := congrArg affinePullback (coordinateProjection_structure Z i)
    change affinePullback (coordinateProjection Z i ≫
      Spec.map (CommRingCat.ofHom LaurentPolynomial.C)) = scalarMap Z at hs
    rw [affinePullback_comp] at hs
    apply RingHom.ext
    intro r
    exact (RingHom.congr_fun hs r).trans (LaurentPolynomial.eval₂_C _ _ r).symm
  · simp only [LaurentPolynomial.eval₂_T, zpow_one]
    rfl

/-- An actual support map is the spectrum of its global pullback. -/
theorem supportIsoSpec_inv_map {R : Type u} [CommRing R]
    (f : Z.scheme ⟶ Spec (.of R)) :
    (supportIsoSpec Z).inv ≫ f =
      Spec.map (CommRingCat.ofHom (affinePullback f)) := by
  rw [supportIsoSpec, ← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv,
    ← Spec.map_comp]
  rfl

variable [CharZero k]

/-- A primitive element of the full joint coordinate field, supplied by separability. -/
def primitiveElement : coordinateRing Z :=
  (Field.exists_primitive_element k (coordinateRing Z)).choose

/-- The chosen element generates the whole support field. -/
theorem primitiveElement_generates :
    IntermediateField.adjoin k ({primitiveElement Z} : Set (coordinateRing Z)) = ⊤ :=
  (Field.exists_primitive_element k (coordinateRing Z)).choose_spec

/-- The original monic irreducible polynomial of the whole support primitive element. -/
def polynomial : MonicIrreducible k :=
  ⟨minpoly k (primitiveElement Z), minpoly.monic (IsIntegral.of_finite k _),
    minpoly.irreducible (IsIntegral.of_finite k _)⟩

/-- Its degree is the original full support degree, without replacing the field by a coordinate. -/
theorem polynomial_natDegree :
    (polynomial Z).val.natDegree = Module.finrank k (coordinateRing Z) :=
  (Field.primitive_element_iff_minpoly_natDegree_eq k (primitiveElement Z)).mp
    (primitiveElement_generates Z)

/-- The literal minimal-polynomial quotient is the entire actual support field. -/
def rootEquiv : AdjoinRoot (polynomial Z).val ≃ₐ[k] coordinateRing Z :=
  (IntermediateField.adjoinRootEquivAdjoin k (IsIntegral.of_finite k (primitiveElement Z))).trans
    ((IntermediateField.equivOfEq (primitiveElement_generates Z)).trans IntermediateField.topEquiv)

/-- Each quotient coordinate is the inverse image of the same original support unit. -/
def polynomialUnit (i : Fin 2) : (AdjoinRoot (polynomial Z).val)ˣ :=
  Units.map (rootEquiv Z).symm.toRingHom.toMonoidHom (coordinateUnit Z i)

/-- The quotient chart retains the original coordinate unit, for either index. -/
@[simp] theorem rootEquiv_polynomialUnit (i : Fin 2) :
    rootEquiv Z (polynomialUnit Z i : AdjoinRoot (polynomial Z).val) =
      (coordinateUnit Z i : coordinateRing Z) :=
  (rootEquiv Z).apply_symm_apply _

/-- The polynomial affine chart identifies the whole original support scheme. -/
def polynomialSupportIso : Spec (.of (AdjoinRoot (polynomial Z).val)) ≅ Z.scheme :=
  Scheme.Spec.mapIso (rootEquiv Z).symm.toRingEquiv.toCommRingCatIso.op ≪≫
    (supportIsoSpec Z).symm

/-- The chart keeps exactly the original base-field map. -/
@[reassoc] theorem polynomialSupportIso_projection :
    (polynomialSupportIso Z).hom ≫ Z.projection =
      Spec.map (CommRingCat.ofHom (AdjoinRoot.of (polynomial Z).val)) := by
  change Spec.map (CommRingCat.ofHom (rootEquiv Z).symm.toRingHom) ≫
    (supportIsoSpec Z).inv ≫ Z.projection = _
  rw [supportIsoSpec_inv_map, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (rootEquiv Z).symm.commutes r

/-- The chart keeps each of the two original Laurent coordinates literally. -/
@[reassoc] theorem polynomialSupportIso_coordinate (i : Fin 2) :
    (polynomialSupportIso Z).hom ≫ coordinateProjection Z i =
      unitMap (AdjoinRoot.of (polynomial Z).val) (polynomialUnit Z i) := by
  change Spec.map (CommRingCat.ofHom (rootEquiv Z).symm.toRingHom) ≫
    (supportIsoSpec Z).inv ≫ coordinateProjection Z i = _
  rw [supportIsoSpec_inv_map, coordinatePullback_eq_eval]
  exact unitMap_comp (scalarMap Z) (AdjoinRoot.of (polynomial Z).val)
    (rootEquiv Z).symm.toRingHom (coordinateUnit Z i) (polynomialUnit Z i)
    (by ext r; exact (rootEquiv Z).symm.commutes r) rfl

local instance polynomialFinite (p : MonicIrreducible k) : Module.Finite k (AdjoinRoot p.val) :=
  p.property.1.finite_adjoinRoot

/-- The full chart identifies the original inclusion with the actual scalar rational pair. -/
@[reassoc] theorem polynomialSupportIso_inclusion :
    (polynomialSupportIso Z).hom ≫ Z.inclusion =
      scalarPoint (k := k) (WeightTwoSymbols.rationalPair (AdjoinRoot (polynomial Z).val)
        (polynomialUnit Z 0) (polynomialUnit Z 1)) := by
  apply pullback.hom_ext
  · rw [scalarPoint_fst]
    exact polynomialSupportIso_projection Z
  · rw [scalarPoint_snd, rationalPair_torusMap]
    apply pair_hom_ext
    · rw [pairMap_first]
      exact polynomialSupportIso_coordinate Z 0
    · rw [pairMap_second]
      exact polynomialSupportIso_coordinate Z 1

/-- Every original generator is the actual point pushforward over its full polynomial field. -/
theorem generator_cycle_eq_pointPushforward :
    Z.cycle = pointPushforward (k := k)
      ((Cor.graphFunctor (AdjoinRoot (polynomial Z).val)).map
        (WeightTwoSymbols.rationalPair _ (polynomialUnit Z 0) (polynomialUnit Z 1))) := by
  have : IsNoetherian ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
    inferInstanceAs (IsNoetherian (Spec (.of k)))
  have : IsNoetherian Z.scheme := isNoetherian_of_finiteType Z.projection
  have : IsNoetherian
      (pullback (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) 2).hom) :=
    isNoetherian_of_finiteType (pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 2).hom)
  apply FiniteCorrespondence.toIntegralCycle_injective
  rw [toIntegralCycle_pointPushforward_graph]
  simp only [← polynomialSupportIso_inclusion Z,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_fundamentalCycle, FiniteCorrespondenceGenerator.cycle,
    FiniteCorrespondence.toIntegralCycle_single]
  exact (closedFundamentalCycle_of_isIntegral Z.val).symm

/-- The original raw class is the existing transfer of the two original coordinates. -/
theorem cycleClass_generator :
    WeightTwoSymbols.cycleClass k Z.cycle =
      corestriction (k := k) (WeightTwoSymbols.graphSymbol (AdjoinRoot (polynomial Z).val)
        (polynomialUnit Z 0) (polynomialUnit Z 1)) := by
  rw [generator_cycle_eq_pointPushforward, ← corestriction_cycleClass]
  rfl

/-- Existential packaging retains the literal polynomial field and the full original degree. -/
theorem exists_pointPushforward :
    ∃ (p : MonicIrreducible k) (a b : (AdjoinRoot p.val)ˣ),
      p.val.natDegree = Module.finrank k (coordinateRing Z) ∧
        Z.cycle = pointPushforward (k := k)
          ((Cor.graphFunctor (AdjoinRoot p.val)).map (WeightTwoSymbols.rationalPair _ a b)) :=
  ⟨polynomial Z, polynomialUnit Z 0, polynomialUnit Z 1,
    polynomial_natDegree Z, generator_cycle_eq_pointPushforward Z⟩

variable (k)

/-- Every original signed cycle is the sum of its full polynomial-field point transfers. -/
theorem cycle_eq_sum_pointPushforward
    (α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k) :
    α = α.sum (fun Z n => n • pointPushforward (k := k)
      ((Cor.graphFunctor (AdjoinRoot (polynomial Z).val)).map
        (WeightTwoSymbols.rationalPair _ (polynomialUnit Z 0) (polynomialUnit Z 1)))) := by
  classical
  conv_lhs => rw [← α.sum_single]
  apply Finset.sum_congr rfl
  intro Z _
  dsimp only
  erw [← generator_cycle_eq_pointPushforward]
  change Finsupp.single Z (Finsupp.toFun α Z) =
    Finsupp.toFun α Z • (Finsupp.single Z 1 : Generator k →₀ ℤ)
  simp only [Finsupp.smul_single, smul_eq_mul, mul_one]

/-- The original raw cycle class retains every signed support coefficient. -/
theorem cycleClass_eq_sum_corestriction
    (α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k) :
    WeightTwoSymbols.cycleClass k α = α.sum (fun Z n => n • corestriction (k := k)
      (WeightTwoSymbols.graphSymbol (AdjoinRoot (polynomial Z).val)
        (polynomialUnit Z 0) (polynomialUnit Z 1))) := by
  classical
  conv_lhs => rw [cycle_eq_sum_pointPushforward k α]
  rw [map_finsuppSum]
  apply Finset.sum_congr rfl
  intro Z _
  dsimp only
  erw [map_zsmul, ← corestriction_cycleClass]
  rfl

/-- Every actual raw H22 element is a signed sum of these original finite transfers. -/
theorem exists_sum_corestriction (x : (motivicRawBaseComplex k 2).homology 2) :
    ∃ α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k,
      x = α.sum (fun Z n => n • corestriction (k := k)
        (WeightTwoSymbols.graphSymbol (AdjoinRoot (polynomial Z).val)
          (polynomialUnit Z 0) (polynomialUnit Z 1))) := by
  obtain ⟨α, rfl⟩ := WeightTwoSymbols.cycleClass_surjective k x
  exact ⟨α, cycleClass_eq_sum_corestriction k α⟩

end Motivic.WeightTwoPointPresentation
