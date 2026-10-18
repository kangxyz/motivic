/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightTwoCoordinateEvaluation
public import Motivic.AlgebraicGeometry.Cycles.FiniteImageProjection
public import Motivic.Aglib.AlgebraicGeometry.FiniteFieldResidueDegree

/-!
# First-coordinate evaluation of actual finite point cycles

A two-coordinate finite point can have a proper image field. The cycle evaluator
retains the actual image, both original Laurent units, the given scalar map, and
the full extension-to-image residue degree. Thus its value is the independent
first-coordinate evaluation on the entire original point field. These are
identities of actual signed cycles, not assertions of homology descent.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.WeightTwoCoordinateCycleEvaluation

open WeightTwoPointPresentation WeightTwoCoordinateEvaluation
open WeightTwoCorestriction WeightTwoCubicBoundary WeightTwoPolynomialTransfer
open AlgebraicGeometry.Scheme.PolynomialLaurent

variable (k : Type u) [Field k]

/-- The original source-target product for two-coordinate point cycles. -/
abbrev ambient : Scheme.{u} :=
  pullback (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) 2).hom

/-- Either literal Laurent coordinate of the original product. -/
def ambientCoordinate (i : Fin 2) : ambient k ⟶ (SmoothSite.torus (.of k)).left :=
  pullback.snd (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) 2).hom ≫
    (SmoothSite.torusCoordinate (.of k) 2 i).left

variable {k}

/-- The actual affine pullback of either coordinate to the original point field. -/
def affineCoordinateUnit {R : Type u} [CommRing R]
    (j : Spec (.of R) ⟶ ambient k) (i : Fin 2) : Rˣ :=
  Units.map (Scheme.ΓSpecIso (.of R)).hom.hom.toMonoidHom
    (Units.map ((j ≫ ambientCoordinate k i).appTop).hom.toMonoidHom
      (laurentGlobalUnit (.of k)))

/-- Literal affine Laurent evaluation recovers the specified original unit. -/
theorem affineCoordinateUnit_of_unitMap {R : Type u} [CommRing R]
    (j : Spec (.of R) ⟶ ambient k) (i : Fin 2) (c : k →+* R) (b : Rˣ)
    (h : j ≫ ambientCoordinate k i = unitMap c b) : affineCoordinateUnit j i = b := by
  apply Units.ext
  change (Scheme.ΓSpecIso (.of R)).hom
    ((j ≫ ambientCoordinate k i).appTop (laurentGlobalUnit (.of k)).val) = (b : R)
  rw [h]
  change (Scheme.ΓSpecIso (.of R)).hom
    ((Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ c b))).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1))) = _
  have he := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (LaurentPolynomial.eval₂ c b))).symm (LaurentPolynomial.T 1)
  change (Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ c b))).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1)) =
    (Scheme.ΓSpecIso (.of R)).inv
      (LaurentPolynomial.eval₂ c b (LaurentPolynomial.T 1)) at he
  rw [he]
  simp [LaurentPolynomial.eval₂_T]

section FinitePoint

variable {E : Type u} [Field E] [Algebra k E] [Module.Finite k E]
  (j : Spec (.of E) ⟶ ambient k) [IsFinite j]
  (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 2).hom =
    Spec.map (CommRingCat.ofHom (algebraMap k E)))

/-- The literal closed image of the finite field point, with its finite base projection. -/
def imageGenerator : Generator k := by
  have hf : IsFinite (j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 2).hom) := by
    rw [hj]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  refine ⟨j.ker, isIntegral_finiteImage j, ?_, ?_⟩
  · exact isFinite_image_projection j _
  · have : Nonempty j.image := ⟨j.toImage (genericPoint (Spec (.of E)))⟩
    have : Subsingleton ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
      inferInstanceAs (Subsingleton (Spec (.of k)))
    have hs : Function.Surjective
        (correspondenceProjection (SmoothSite.base (Spec (.of k))).hom
          (SmoothSite.torusPower (.of k) 2).hom j.ker) :=
      Function.surjective_to_subsingleton _
    change Set.range (correspondenceProjection (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 2).hom j.ker) ∈ irreducibleComponents (Spec (.of k))
    rw [Set.range_eq_univ.mpr hs]
    exact (irreducibleComponents_eq_singleton (X := Spec (.of k))) ▸ Set.mem_singleton _

/-- The source-to-image map has the original structural scalar map. -/
@[reassoc (attr := simp)]
theorem imageGenerator_toImage_projection :
    j.toImage ≫ (imageGenerator j hj).projection =
      Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  simpa [imageGenerator, FiniteCorrespondenceGenerator.projection,
    correspondenceProjection] using hj

/-- The finite pushforward support is the actual scheme-theoretic image. -/
theorem imageGenerator_support :
    (imageGenerator j hj).toIntegralClosedSubscheme =
      (IntegralClosedSubscheme.pointClosure (genericPoint (Spec (.of E)))).finiteImage j := by
  apply IntegralClosedSubscheme.point_injective
  rw [IntegralClosedSubscheme.point_finiteImage, IntegralClosedSubscheme.point_pointClosure]
  exact imageι_genericPoint j

/-- The whole pushed point includes its full original residue degree. -/
def finitePointCorrespondence : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k :=
  Finsupp.single (imageGenerator j hj) (j.residueDegree (genericPoint (Spec (.of E))) : ℤ)

/-- Forgetting admissibility recovers the original full finite fundamental pushforward. -/
theorem toIntegralCycle_finitePointCorrespondence :
    FiniteCorrespondence.toIntegralCycle (finitePointCorrespondence j hj) =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of E))) := by
  rw [fundamentalCycle_of_isIntegral, IntegralCycle.finitePushforward_single]
  simp only [finitePointCorrespondence, FiniteCorrespondence.toIntegralCycle_single,
    imageGenerator_support, IntegralClosedSubscheme.point_pointClosure, one_mul]

/-- The original pullback from the image field to the given extension field. -/
def imageScalarMap : coordinateRing (imageGenerator j hj) →+* E :=
  (Scheme.ΓSpecIso (.of E)).hom.hom.comp j.toImage.appTop.hom

/-- This image field action uses the actual map on global sections. -/
instance imageAlgebra : Algebra (coordinateRing (imageGenerator j hj)) E :=
  (imageScalarMap j hj).toAlgebra

/-- The two structural maps commute before any norm or degree is taken. -/
theorem imageScalarMap_comp :
    (imageScalarMap j hj).comp (algebraMap k (coordinateRing (imageGenerator j hj))) =
      algebraMap k E := by
  have h : (j.toImage ≫ (imageGenerator j hj).projection).appTop ≫
      (Scheme.ΓSpecIso (.of E)).hom =
      (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom (algebraMap k E) := by
    rw [imageGenerator_toImage_projection, Scheme.ΓSpecIso_naturality]
  apply RingHom.ext
  intro r
  have hv := ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of k)).inv r)
  rw [Scheme.Hom.comp_appTop] at hv
  change (Scheme.ΓSpecIso (.of E)).hom
    (j.toImage.appTop ((imageGenerator j hj).projection.appTop
      ((Scheme.ΓSpecIso (.of k)).inv r))) = algebraMap k E r
  change (Scheme.ΓSpecIso (.of E)).hom
    (j.toImage.appTop ((imageGenerator j hj).projection.appTop
      ((Scheme.ΓSpecIso (.of k)).inv r))) =
    algebraMap k E ((Scheme.ΓSpecIso (.of k)).hom
      ((Scheme.ΓSpecIso (.of k)).inv r)) at hv
  simpa only [Iso.inv_hom_id_apply] using hv

instance imageScalarTower : IsScalarTower k (coordinateRing (imageGenerator j hj)) E :=
  IsScalarTower.of_algebraMap_eq' (imageScalarMap_comp j hj).symm

/-- The original Laurent coordinate pulls back along the actual field inclusion. -/
theorem imageScalarMap_coordinate (i : Fin 2) :
    imageScalarMap j hj
      (coordinateUnit (imageGenerator j hj) i : coordinateRing (imageGenerator j hj)) =
      (affineCoordinateUnit j i : E) := by
  have h : j.toImage ≫ ((imageGenerator j hj).targetProjection ≫
      (SmoothSite.torusCoordinate (.of k) 2 i).left) = j ≫ ambientCoordinate k i := by
    change j.toImage ≫ j.imageι ≫ ambientCoordinate k i = _
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  have ha := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at ha
  have hv := ConcreteCategory.congr_hom ha
    (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit (.of k)).val
  exact congrArg (fun r => (Scheme.ΓSpecIso (.of E)).hom r) hv

/-- The given extension is finite over the actual image field too. -/
instance imageFinite : Module.Finite (coordinateRing (imageGenerator j hj)) E :=
  Module.Finite.of_restrictScalars_finite k _ _

/-- The source-to-image map becomes exactly the original global-section map
under the canonical affine chart. -/
theorem toImage_isoSpec :
    j.toImage ≫ (imageGenerator j hj).scheme.isoSpec.hom =
      Spec.map (CommRingCat.ofHom (imageScalarMap j hj)) := by
  have h := Scheme.isoSpec_hom_naturality
    (show Spec (.of E) ⟶ (imageGenerator j hj).scheme from j.toImage)
  rw [Scheme.isoSpec_Spec_hom, ← Spec.map_comp] at h
  exact h.symm

/-- The geometric pushforward coefficient is the full degree over the literal
image field, not the degree of the image over the base. -/
theorem residueDegree_eq_image_finrank (x : Spec (.of E)) :
    j.residueDegree x = Module.finrank (coordinateRing (imageGenerator j hj)) E := by
  calc
    j.residueDegree x = j.toImage.residueDegree x := by
      have h := congrArg (fun f => f.residueDegree x) j.toImage_imageι
      rw [residueDegree_comp, residueDegree_of_surjectiveOnStalks, one_mul] at h
      exact h.symm
    _ = (Spec.map (CommRingCat.ofHom (imageScalarMap j hj))).residueDegree x := by
      have h := congrArg (fun f => f.residueDegree x) (toImage_isoSpec j hj)
      have hc := residueDegree_comp
        (show Spec (.of E) ⟶ (imageGenerator j hj).scheme from j.toImage)
        (imageGenerator j hj).scheme.isoSpec.hom x
      rw [residueDegree_of_isIso (imageGenerator j hj).scheme.isoSpec.hom, one_mul] at hc
      exact hc.symm.trans h
    _ = _ := Scheme.Hom.residueDegree_SpecMap_algebraMap
      (coordinateRing (imageGenerator j hj)) E x

/-- Pullback of either original support unit through the literal image-field map. -/
theorem imageScalarMap_coordinateUnit (i : Fin 2) :
    Units.map (algebraMap (coordinateRing (imageGenerator j hj)) E).toMonoidHom
      (coordinateUnit (imageGenerator j hj) i) = affineCoordinateUnit j i := by
  apply Units.ext
  exact imageScalarMap_coordinate j hj i

/-- The full pushed cycle evaluates in its entire original field, even when
neither coordinate generates that field and the source is not a closed immersion. -/
theorem cycleValue_finitePointCorrespondence :
    cycleValue k (finitePointCorrespondence j hj) =
      value (k := k) (affineCoordinateUnit j 0) (affineCoordinateUnit j 1) := by
  unfold finitePointCorrespondence
  rw [cycleValue_single, residueDegree_eq_image_finrank j hj, natCast_zsmul]
  change Module.finrank (coordinateRing (imageGenerator j hj)) E •
    value (k := k) (coordinateUnit (imageGenerator j hj) 0)
      (coordinateUnit (imageGenerator j hj) 1) = _
  rw [← value_map_degree (D := E), imageScalarMap_coordinateUnit,
    imageScalarMap_coordinateUnit]

include hj in
/-- The adapter uses an equality of actual finite fundamental pushforwards,
not an assumed equality after evaluation or a chosen primitive polynomial. -/
theorem cycleValue_eq_value_of_finite_fundamental
    (α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of E)))) :
    cycleValue k α =
      value (k := k) (affineCoordinateUnit j 0) (affineCoordinateUnit j 1) := by
  have h : α = finitePointCorrespondence j hj :=
    FiniteCorrespondence.toIntegralCycle_injective
      (hα.trans (toIntegralCycle_finitePointCorrespondence j hj).symm)
  rw [h, cycleValue_finitePointCorrespondence]

include hj in
/-- Both original units may be specified without changing the point's field. -/
theorem cycleValue_eq_value_units_of_finite_fundamental
    (a b : Eˣ) (ha : affineCoordinateUnit j 0 = a) (hb : affineCoordinateUnit j 1 = b)
    (α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of E)))) :
    cycleValue k α = value (k := k) a b := by
  rw [cycleValue_eq_value_of_finite_fundamental j hj α hα, ha, hb]

end FinitePoint

section Pairs

variable {E : Type u} [Field E] [Algebra k E]

/-- The actual scalar point retains the first original Laurent unit. -/
@[simp] theorem affineCoordinateUnit_scalarPoint_left (a b : Eˣ) :
    affineCoordinateUnit (scalarPoint (k := k) (WeightTwoSymbols.rationalPair E a b)) 0 = a := by
  apply affineCoordinateUnit_of_unitMap _ _ (algebraMap k E)
  rw [ambientCoordinate, ← Category.assoc, scalarPoint_snd, rationalPair_torusMap,
    pairMap_first]

/-- The actual scalar point retains the second original Laurent unit. -/
@[simp] theorem affineCoordinateUnit_scalarPoint_right (a b : Eˣ) :
    affineCoordinateUnit (scalarPoint (k := k) (WeightTwoSymbols.rationalPair E a b)) 1 = b := by
  apply affineCoordinateUnit_of_unitMap _ _ (algebraMap k E)
  rw [ambientCoordinate, ← Category.assoc, scalarPoint_snd, rationalPair_torusMap,
    pairMap_second]

variable [Module.Finite k E]

/-- The existing point pushforward of a rational pair has precisely the value
of both original units in the entire given field. -/
theorem cycleValue_pointPushforward_graph (a b : Eˣ) :
    cycleValue k (pointPushforward (k := k)
      ((Cor.graphFunctor E).map (WeightTwoSymbols.rationalPair E a b))) =
      value (k := k) a b :=
  cycleValue_eq_value_units_of_finite_fundamental
    (scalarPoint (k := k) (WeightTwoSymbols.rationalPair E a b)) (scalarPoint_fst _) a b
    (affineCoordinateUnit_scalarPoint_left a b) (affineCoordinateUnit_scalarPoint_right a b)
    _ (toIntegralCycle_pointPushforward_graph _)

/-- Full signed multiplicities survive evaluation, including negative coefficients. -/
theorem cycleValue_zsmul_pointPushforward_graph (a b : Eˣ) (n : ℤ) :
    cycleValue k (n • pointPushforward (k := k)
      ((Cor.graphFunctor E).map (WeightTwoSymbols.rationalPair E a b))) =
      n • value (k := k) a b := by
  rw [map_zsmul, cycleValue_pointPushforward_graph]

/-- No distinctness of image supports is needed for finite signed sums. -/
theorem cycleValue_sum_pointPushforward_graph {ι : Type*} (s : Finset ι)
    (a b : ι → Eˣ) (n : ι → ℤ) :
    cycleValue k (∑ i ∈ s, n i • pointPushforward (k := k)
      ((Cor.graphFunctor E).map (WeightTwoSymbols.rationalPair E (a i) (b i)))) =
      ∑ i ∈ s, n i • value (k := k) (a i) (b i) := by
  simp only [map_sum, cycleValue_zsmul_pointPushforward_graph]

/-- An actual pushed point on the first identity axis has zero value. -/
@[simp] theorem cycleValue_pointPushforward_graph_one_left (b : Eˣ) :
    cycleValue k (pointPushforward (k := k)
      ((Cor.graphFunctor E).map (WeightTwoSymbols.rationalPair E 1 b))) = 0 := by
  rw [cycleValue_pointPushforward_graph, value_one_left]

/-- An actual pushed point on the second identity axis has zero value. -/
@[simp] theorem cycleValue_pointPushforward_graph_one_right (a : Eˣ) :
    cycleValue k (pointPushforward (k := k)
      ((Cor.graphFunctor E).map (WeightTwoSymbols.rationalPair E a 1))) = 0 := by
  rw [cycleValue_pointPushforward_graph, value_one_right]

end Pairs

/-- The first coordinate of the literal rational graph is the given base unit. -/
@[simp] theorem affineCoordinateUnit_graph_left (a b : kˣ) :
    affineCoordinateUnit (graphEmbedding (WeightTwoSymbols.rationalPair k a b)) 0 = a := by
  apply affineCoordinateUnit_of_unitMap _ _ (RingHom.id k)
  rw [ambientCoordinate, ← Category.assoc, graphEmbedding_snd, rationalPair_coordinate_left]
  rfl

/-- The second coordinate of the literal rational graph is the given base unit. -/
@[simp] theorem affineCoordinateUnit_graph_right (a b : kˣ) :
    affineCoordinateUnit (graphEmbedding (WeightTwoSymbols.rationalPair k a b)) 1 = b := by
  apply affineCoordinateUnit_of_unitMap _ _ (RingHom.id k)
  rw [ambientCoordinate, ← Category.assoc, graphEmbedding_snd, rationalPair_coordinate_right]
  rfl

/-- On the actual rational graph, cycle evaluation is the original Milnor symbol. -/
@[simp] theorem cycleValue_graph [CharZero k] (a b : kˣ) :
    cycleValue k ((Cor.graphFunctor k).map (WeightTwoSymbols.rationalPair k a b)) =
      MilnorK.K2.symbol a b := by
  rw [cycleValue_eq_value_units_of_finite_fundamental
    (graphEmbedding (WeightTwoSymbols.rationalPair k a b)) (by
      rw [graphEmbedding_fst]
      exact (Spec.map_id (.of k)).symm) a b
    (affineCoordinateUnit_graph_left a b) (affineCoordinateUnit_graph_right a b)
    _ (toIntegralCycle_graph _), value_rational]

/-- An arbitrary original signed cycle on the identity-coordinate supports
has zero value. Its supports may use either axis, with arbitrary multiplicities. -/
theorem cycleValue_eq_zero_of_identity_support
    (α : WeightOnePointNorm.point k ⟶ WeightTwoSymbols.target k)
    (hα : ∀ Z ∈ α.support, coordinateUnit Z 0 = 1 ∨ coordinateUnit Z 1 = 1) :
    cycleValue k α = 0 := by
  classical
  conv_lhs => rw [← α.sum_single]
  rw [map_finsuppSum]
  apply Finset.sum_eq_zero
  intro Z hZ
  dsimp only
  rw [cycleValue_single]
  rcases hα Z hZ with h | h
  · simp only [generatorValue, h, value_one_left, smul_zero]
  · simp only [generatorValue, h, value_one_right, smul_zero]

end Motivic.WeightTwoCoordinateCycleEvaluation
