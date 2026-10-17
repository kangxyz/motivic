/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightOneFundamentalNorm
public import Motivic.AlgebraicGeometry.Cycles.FiniteImageProjection
public import Mathlib.RingTheory.Norm.Transitivity
public import Motivic.Aglib.AlgebraicGeometry.FiniteFieldResidueDegree

/-!
# Norms of genuine finite pushed points

A finite field point need not be a closed immersion into the torus: its
coordinate may generate a proper subfield. We retain the actual closed image,
its literal global-section field, and the full residue degree in finite
pushforward. All scalar maps come from the original scheme morphisms.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.WeightOneFinitePointNorm

open WeightOnePointNorm WeightOneFundamentalNorm

variable {k E : Type u} [Field k] [Field E] [Algebra k E] [Module.Finite k E]
  (j : Spec (.of E) ⟶ ambient k) [IsFinite j]
  (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom =
    Spec.map (CommRingCat.ofHom (algebraMap k E)))

/-- The literal closed image of the finite field point, with its finite base projection. -/
def imageGenerator : Generator k := by
  have hf : IsFinite (j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom) := by
    rw [hj]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  refine ⟨j.ker, isIntegral_finiteImage j, ?_, ?_⟩
  · exact isFinite_image_projection j _
  · have : Nonempty j.image := ⟨j.toImage (genericPoint (Spec (.of E)))⟩
    have : Subsingleton ((𝟭 Scheme).obj (SmoothSite.base (Spec (.of k))).left) :=
      inferInstanceAs (Subsingleton (Spec (.of k)))
    have hs : Function.Surjective
        (correspondenceProjection (SmoothSite.base (Spec (.of k))).hom
          (SmoothSite.torusPower (.of k) 1).hom j.ker) :=
      Function.surjective_to_subsingleton _
    change Set.range (correspondenceProjection (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom j.ker) ∈ irreducibleComponents (Spec (.of k))
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
def finitePointCorrespondence : point k ⟶ target k :=
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
theorem imageScalarMap_coordinate :
    imageScalarMap j hj
      (coordinateUnit (imageGenerator j hj) : coordinateRing (imageGenerator j hj)) =
      (affineCoordinateUnit j : E) := by
  have h : j.toImage ≫ ((imageGenerator j hj).targetProjection ≫
      (SmoothSite.torusCoordinate (.of k) 1 0).left) = j ≫ ambientCoordinate k := by
    change j.toImage ≫ j.imageι ≫ ambientCoordinate k = _
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  have ha := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at ha
  have hv := ConcreteCategory.congr_hom ha
    (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit (.of k)).val
  exact congrArg (fun r => (Scheme.ΓSpecIso (.of E)).hom r) hv

/-- The image has its actual finite field of global sections. -/
instance imageField : Field (coordinateRing (imageGenerator j hj)) :=
  (coordinateRing_isField (imageGenerator j hj)).toField

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

/-- The tower determinant norm retains the degree over the actual image field. -/
theorem norm_imageScalarMap (a : coordinateRing (imageGenerator j hj)) :
    Algebra.norm k (imageScalarMap j hj a) =
      Algebra.norm k a ^ Module.finrank (coordinateRing (imageGenerator j hj)) E := by
  rw [← Algebra.norm_norm (S := coordinateRing (imageGenerator j hj))]
  change Algebra.norm k
    (Algebra.norm (coordinateRing (imageGenerator j hj))
      (algebraMap (coordinateRing (imageGenerator j hj)) E a)) = _
  rw [Algebra.norm_algebraMap, map_pow]

/-- The same retained-degree tower identity in the original unit group. -/
theorem normUnits_imageScalarMap (a : (coordinateRing (imageGenerator j hj))ˣ) :
    Units.map (Algebra.norm k) (Units.map (imageScalarMap j hj).toMonoidHom a) =
      Units.map (Algebra.norm k) a ^ Module.finrank (coordinateRing (imageGenerator j hj)) E := by
  apply Units.ext
  exact norm_imageScalarMap j hj a.val

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

/-- The genuine finite point norm keeps the extension-to-image multiplicity. -/
theorem cycleNorm_finitePointCorrespondence :
    cycleNorm k (finitePointCorrespondence j hj) =
      Additive.ofMul (Units.map (Algebra.norm k) (affineCoordinateUnit j)) := by
  unfold finitePointCorrespondence
  rw [cycleNorm_single, residueDegree_eq_image_finrank j hj]
  apply Additive.toMul.injective
  simp only [toMul_zsmul, toMul_ofMul, zpow_natCast]
  apply Units.ext
  change Algebra.norm k (coordinateUnit (imageGenerator j hj) :
    coordinateRing (imageGenerator j hj)) ^
      Module.finrank (coordinateRing (imageGenerator j hj)) E =
    Algebra.norm k (affineCoordinateUnit j : E)
  rw [← imageScalarMap_coordinate j hj]
  exact (norm_imageScalarMap j hj _).symm

include hj in
/-- Every actual correspondence representing the whole finite pushed point has
the determinant norm of the original extension field. A closed immersion of
the original point is not required. -/
theorem cycleNorm_eq_norm_of_finite_fundamental
    (α : point k ⟶ target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of E)))) :
    cycleNorm k α = Additive.ofMul (Units.map (Algebra.norm k) (affineCoordinateUnit j)) := by
  have h : α = finitePointCorrespondence j hj :=
    FiniteCorrespondence.toIntegralCycle_injective
      (hα.trans (toIntegralCycle_finitePointCorrespondence j hj).symm)
  rw [h, cycleNorm_finitePointCorrespondence]

include hj in
/-- The finite-point formula with its Laurent coordinate specified as an original unit. -/
theorem cycleNorm_eq_norm_unit_of_finite_fundamental
    (b : Eˣ) (hb : affineCoordinateUnit j = b)
    (α : point k ⟶ target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of E)))) :
    cycleNorm k α = Additive.ofMul (Units.map (Algebra.norm k) b) := by
  rw [cycleNorm_eq_norm_of_finite_fundamental j hj α hα, hb]

/-- Laurent evaluation over the original base field, even for inseparable extensions. -/
def unitTorusPoint (b : Eˣ) : Spec (.of E) ⟶ (SmoothSite.torus (.of k)).left :=
  Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (algebraMap k E) b))

omit [Module.Finite k E] in
/-- Laurent evaluation has precisely the given extension's structural map. -/
@[reassoc (attr := simp)]
theorem unitTorusPoint_projection (b : Eˣ) :
    unitTorusPoint (k := k) b ≫ (SmoothSite.torus (.of k)).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k E)) := by
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  congr 1
  ext r
  exact LaurentPolynomial.eval₂_C _ _ _

/-- The actual extension-field unit point in the original source-target product. -/
def unitPoint (b : Eˣ) : Spec (.of E) ⟶ ambient k :=
  pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap k E)))
    (unitTorusPoint (k := k) b ≫ (SmoothSite.torusPowerOneIso (.of k)).inv.left) (by
      change _ ≫ 𝟙 _ = _
      rw [Category.comp_id, Category.assoc, MorphismProperty.Over.w,
        unitTorusPoint_projection])

omit [Module.Finite k E] in
/-- The actual product point has the original scalar projection. -/
@[reassoc (attr := simp)]
theorem unitPoint_projection (b : Eˣ) :
    unitPoint (k := k) b ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
        (SmoothSite.torusPower (.of k) 1).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k E)) :=
  pullback.lift_fst _ _ _

/-- Finiteness follows from the original finite extension, with no separability assumption. -/
instance unitPoint_finite (b : Eˣ) : IsFinite (unitPoint (k := k) b) := by
  have : IsFinite (unitPoint (k := k) b ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom
        (SmoothSite.torusPower (.of k) 1).hom) := by
    rw [unitPoint_projection]
    exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  exact IsFinite.of_comp _ (pullback.fst (SmoothSite.base (Spec (.of k))).hom
    (SmoothSite.torusPower (.of k) 1).hom)

omit [Module.Finite k E] in
/-- The coordinate morphism is the literal Laurent evaluation. -/
@[reassoc (attr := simp)]
theorem unitPoint_ambientCoordinate (b : Eˣ) :
    unitPoint (k := k) b ≫ ambientCoordinate k = unitTorusPoint (k := k) b := by
  rw [ambientCoordinate, ← Category.assoc]
  simp only [unitPoint, pullback.lift_snd]
  rw [Category.assoc]
  have h : (SmoothSite.torusPowerOneIso (.of k)).inv.left ≫
      (SmoothSite.torusCoordinate (.of k) 1 0).left = 𝟙 _ :=
    congrArg (fun f => f.left) (SmoothSite.torusPowerOneIso (.of k)).inv_hom_id
  rw [h, Category.comp_id]

omit [Module.Finite k E] in
/-- The original pulled-back Laurent unit is exactly the given extension-field unit. -/
@[simp]
theorem affineCoordinateUnit_unitPoint (b : Eˣ) :
    affineCoordinateUnit (unitPoint (k := k) b) = b := by
  apply Units.ext
  change (Scheme.ΓSpecIso (.of E)).hom
    (((unitPoint (k := k) b) ≫ ambientCoordinate k).appTop
      (AlgebraicGeometry.Scheme.PolynomialLaurent.laurentGlobalUnit (.of k)).val) = (b : E)
  rw [unitPoint_ambientCoordinate]
  change (Scheme.ΓSpecIso (.of E)).hom
    ((Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (algebraMap k E) b))).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1))) = _
  have h := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_inv_naturality
      (CommRingCat.ofHom (LaurentPolynomial.eval₂ (algebraMap k E) b))).symm
        (LaurentPolynomial.T 1)
  change (Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (algebraMap k E) b))).appTop
      ((Scheme.ΓSpecIso (.of (LaurentPolynomial k))).inv (LaurentPolynomial.T 1)) =
    (Scheme.ΓSpecIso (.of E)).inv
      (LaurentPolynomial.eval₂ (algebraMap k E) b (LaurentPolynomial.T 1)) at h
  rw [h]
  simp [LaurentPolynomial.eval₂_T]

/-- The actual correspondence obtained by pushing the entire extension-field unit point. -/
def unitPointCorrespondence (b : Eˣ) : point k ⟶ target k :=
  finitePointCorrespondence (unitPoint (k := k) b) (unitPoint_projection b)

/-- Its integral cycle is the full pushed fundamental cycle, including [E:k(b)]. -/
theorem toIntegralCycle_unitPointCorrespondence (b : Eˣ) :
    FiniteCorrespondence.toIntegralCycle (unitPointCorrespondence (k := k) b) =
      IntegralCycle.finitePushforward (unitPoint (k := k) b)
        (fundamentalCycle (Spec (.of E))) :=
  toIntegralCycle_finitePointCorrespondence _ _

/-- The determinant norm formula for an arbitrary extension-field unit, including
units generating a proper subfield and purely inseparable extensions. -/
@[simp]
theorem cycleNorm_unitPointCorrespondence (b : Eˣ) :
    cycleNorm k (unitPointCorrespondence (k := k) b) =
      Additive.ofMul (Units.map (Algebra.norm k) b) := by
  rw [unitPointCorrespondence, cycleNorm_finitePointCorrespondence,
    affineCoordinateUnit_unitPoint]

/-- The same literal formula on an arbitrary representative of the whole pushed point. -/
theorem cycleNorm_eq_norm_of_unitPoint (b : Eˣ) (α : point k ⟶ target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward (unitPoint (k := k) b)
        (fundamentalCycle (Spec (.of E)))) :
    cycleNorm k α = Additive.ofMul (Units.map (Algebra.norm k) b) :=
  cycleNorm_eq_norm_unit_of_finite_fundamental _ (unitPoint_projection b) b
    (affineCoordinateUnit_unitPoint b) α hα

end Motivic.WeightOneFinitePointNorm
