/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.WeightOne.PointNorm
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.Invariance
public import Motivic.Aglib.AlgebraicGeometry.Cycles.FiniteAlgebra.FundamentalDecomposition

/-!
# The norm of the whole finite fundamental cycle

The actual closed finite fiber is compared with every maximal quotient of its
whole coordinate algebra. The original localized ring lengths, including
nilpotents and all residue extensions, are retained.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped BigOperators

open AlgebraicGeometry.Scheme.FiniteAlgebra
universe u

namespace Motivic
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry.Scheme.FiniteAlgebra
open _root_.AlgebraicGeometry.Scheme.Hom

open WeightOnePointNorm

variable (k : Type u) [Field k]

/-- The original product in which weight-one point supports lie. -/
abbrev WeightOneFundamentalNorm.ambient : Scheme.{u} :=
  pullback (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) 1).hom

/-- The actual first Laurent coordinate on the original product. -/
def WeightOneFundamentalNorm.ambientCoordinate : WeightOneFundamentalNorm.ambient k ⟶
    SmoothSite.torus (.of k) |>.left :=
  pullback.snd (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) 1).hom ≫
    (SmoothSite.torusCoordinate (.of k) 1 0).left

section Field

variable {k} {L : Type u} [Field L] [Algebra k L] [Module.Finite k L]
  (j : Spec (.of L) ⟶ WeightOneFundamentalNorm.ambient k) [IsClosedImmersion j]
  (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom =
    Spec.map (CommRingCat.ofHom (algebraMap k L)))

/-- An actual finite field branch determines its literal closed-image generator. -/
def WeightOneFundamentalNorm.fieldGenerator : Generator k := by
  have hf : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have heq : correspondenceProjection (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom j.ker =
      inv j.toImage ≫ Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
    apply (cancel_epi j.toImage).mp
    simpa [correspondenceProjection] using hj
  refine ⟨j.ker, IsIntegral.of_isIso j.toImage, ?_, ?_⟩
  · rw [heq]
    infer_instance
  · have : Nonempty j.image := ⟨j.toImage (genericPoint (Spec (.of L)))⟩
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

@[reassoc]
theorem WeightOneFundamentalNorm.fieldGenerator_toImage_projection :
    j.toImage ≫ (WeightOneFundamentalNorm.fieldGenerator j hj).projection =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  simpa [WeightOneFundamentalNorm.fieldGenerator, FiniteCorrespondenceGenerator.projection,
    correspondenceProjection] using hj

@[reassoc (attr := simp)]
theorem WeightOneFundamentalNorm.fieldGenerator_toImage_projection_simp :
    j.toImage ≫ @FiniteCorrespondenceGenerator.projection (Spec (.of k))
        (SmoothSite.base (Spec (.of k))).left
        (pullback (Scheme.PolynomialLaurent.laurentProjection (.of k))
          (SmoothSite.base (Spec (.of k))).hom)
        (SmoothSite.base (Spec (.of k))).hom
        (pullback.fst (Scheme.PolynomialLaurent.laurentProjection (.of k))
            (SmoothSite.base (Spec (.of k))).hom ≫
          Scheme.PolynomialLaurent.laurentProjection (.of k))
        (WeightOneFundamentalNorm.fieldGenerator j hj) =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) :=
  WeightOneFundamentalNorm.fieldGenerator_toImage_projection j hj

/-- The field support's actual global sections are the literal field branch,
with precisely the scalar map used by `generatorNorm`. -/
def WeightOneFundamentalNorm.fieldCoordinateEquiv : coordinateRing
    (WeightOneFundamentalNorm.fieldGenerator j hj) ≃ₐ[k] L :=
  { ((asIso j.toImage.appTop) ≪≫ Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv with
    commutes' := by
      intro r
      have h : (j.toImage ≫ (WeightOneFundamentalNorm.fieldGenerator j hj).projection).appTop ≫
          (Scheme.ΓSpecIso (.of L)).hom =
          (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom (algebraMap k L) := by
        rw [WeightOneFundamentalNorm.fieldGenerator_toImage_projection, Scheme.ΓSpecIso_naturality]
      have hv := ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of k)).inv r)
      rw [Scheme.Hom.comp_appTop] at hv
      change (Scheme.ΓSpecIso (.of L)).hom
        (j.toImage.appTop ((WeightOneFundamentalNorm.fieldGenerator j hj).projection.appTop
          ((Scheme.ΓSpecIso (.of k)).inv r))) =
        algebraMap k L ((Scheme.ΓSpecIso (.of k)).hom
          ((Scheme.ΓSpecIso (.of k)).inv r)) at hv
      change (Scheme.ΓSpecIso (.of L)).hom
        (j.toImage.appTop ((WeightOneFundamentalNorm.fieldGenerator j hj).projection.appTop
          ((Scheme.ΓSpecIso (.of k)).inv r))) = algebraMap k L r
      simpa only [Iso.inv_hom_id_apply] using hv }


/-- The original Laurent unit, evaluated in the literal affine coordinate algebra. -/
def WeightOneFundamentalNorm.affineCoordinateUnit {R : Type u} [CommRing R]
    (j : Spec (.of R) ⟶ WeightOneFundamentalNorm.ambient k) : Rˣ :=
  Units.map (Scheme.ΓSpecIso (.of R)).hom.hom.toMonoidHom
    (Units.map ((j ≫ WeightOneFundamentalNorm.ambientCoordinate k).appTop).hom.toMonoidHom
      (laurentGlobalUnit (.of k)))

theorem WeightOneFundamentalNorm.fieldCoordinateEquiv_coordinate :
    WeightOneFundamentalNorm.fieldCoordinateEquiv j hj
        (coordinateUnit (WeightOneFundamentalNorm.fieldGenerator j hj) : coordinateRing
            (WeightOneFundamentalNorm.fieldGenerator j hj)) =
      (affineCoordinateUnit j : L) := by
  have h : j.toImage ≫ ((WeightOneFundamentalNorm.fieldGenerator j hj).targetProjection ≫
      (SmoothSite.torusCoordinate (.of k) 1 0).left) = j ≫
          WeightOneFundamentalNorm.ambientCoordinate k := by
    change j.toImage ≫ j.imageι ≫ WeightOneFundamentalNorm.ambientCoordinate k = _
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  have ha := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at ha
  have hv := ConcreteCategory.congr_hom ha (laurentGlobalUnit (.of k)).val
  exact congrArg (fun r => (Scheme.ΓSpecIso (.of L)).hom r) hv

/-- The existing geometric generator norm is the determinant norm on its
literal finite field branch. -/
theorem WeightOneFundamentalNorm.generatorNorm_fieldGenerator :
    generatorNorm (WeightOneFundamentalNorm.fieldGenerator j hj) =
      Units.map (Algebra.norm k) (affineCoordinateUnit j) := by
  apply Units.ext
  rw [generatorNorm_val]
  change Algebra.norm k (coordinateUnit (WeightOneFundamentalNorm.fieldGenerator j hj) :
      coordinateRing (WeightOneFundamentalNorm.fieldGenerator j hj)) =
    Algebra.norm k (affineCoordinateUnit j : L)
  rw [← WeightOneFundamentalNorm.fieldCoordinateEquiv_coordinate j hj]
  let e := WeightOneFundamentalNorm.fieldCoordinateEquiv j hj
  simp_rw [Algebra.norm_apply, ← LinearMap.det_conj _ e.toLinearEquiv]
  congr 1
  ext x
  simp [e]

end Field

section FiniteAlgebra

variable {k} {R : Type u} [CommRing R] [Algebra k R] [Module.Finite k R]

attribute [local instance] _root_.AlgebraicGeometry.Scheme.FiniteAlgebra.quotientField

variable (j : Spec (.of R) ⟶ WeightOneFundamentalNorm.ambient k) [IsClosedImmersion j]
  (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom =
    Spec.map (CommRingCat.ofHom (algebraMap k R)))

omit [Module.Finite k R] [IsClosedImmersion j] in
include hj in
/-- Scalar compatibility for each literal maximal quotient branch. -/
theorem WeightOneFundamentalNorm.branch_projection (p : MaximalSpectrum R) :
    (quotientMap p ≫ j) ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (R ⧸ p.asIdeal))) := by
  rw [Category.assoc, hj]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- Every branch uses the actual image in the original source-target product. -/
def WeightOneFundamentalNorm.branchGenerator (p : MaximalSpectrum R) : Generator k :=
  WeightOneFundamentalNorm.fieldGenerator (quotientMap p ≫ j)
      (WeightOneFundamentalNorm.branch_projection j hj p)

/-- The geometric support of the branch is precisely finite pushforward of
its original quotient support. -/
theorem WeightOneFundamentalNorm.branchGenerator_support (p : MaximalSpectrum R) :
    (WeightOneFundamentalNorm.branchGenerator j hj p).toIntegralClosedSubscheme = (quotientSupport
        p).finiteImage j := by
  apply IntegralClosedSubscheme.point_injective
  rw [IntegralClosedSubscheme.point_finiteImage, quotientSupport_point]
  let := isIntegral_finiteImage (quotientMap p ≫ j)
  change (quotientMap p ≫ j).imageι (genericPoint (quotientMap p ≫ j).image) = _
  rw [imageι_genericPoint, Scheme.Hom.comp_apply, quotientMap_genericPoint]

omit [Algebra k R] [Module.Finite k R] [IsClosedImmersion j] in
/-- The pulled-back coordinate on a residue branch is its literal quotient image. -/
theorem WeightOneFundamentalNorm.affineCoordinateUnit_quotient (p : MaximalSpectrum R) :
    WeightOneFundamentalNorm.affineCoordinateUnit (quotientMap p ≫ j) =
      Units.map (Ideal.Quotient.mk p.asIdeal).toMonoidHom
          (WeightOneFundamentalNorm.affineCoordinateUnit j) := by
  apply Units.ext
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal))
  have hv := ConcreteCategory.congr_hom hn
    ((j ≫ WeightOneFundamentalNorm.ambientCoordinate k).appTop (laurentGlobalUnit (.of k)).val)
  change (Scheme.ΓSpecIso (.of (R ⧸ p.asIdeal))).hom
      ((quotientMap p).appTop
        ((j ≫ WeightOneFundamentalNorm.ambientCoordinate k).appTop (laurentGlobalUnit (.of k)).val))
            =
    Ideal.Quotient.mk p.asIdeal ((Scheme.ΓSpecIso (.of R)).hom
        ((j ≫ WeightOneFundamentalNorm.ambientCoordinate k).appTop (laurentGlobalUnit (.of k)).val))
            at hv
  have hc : ((quotientMap p ≫ j) ≫ WeightOneFundamentalNorm.ambientCoordinate k).appTop =
      (j ≫ WeightOneFundamentalNorm.ambientCoordinate k).appTop ≫ (quotientMap p).appTop := by
    rw [Category.assoc, Scheme.Hom.comp_appTop]
  change (Scheme.ΓSpecIso (.of (R ⧸ p.asIdeal))).hom
      (((quotientMap p ≫ j) ≫ WeightOneFundamentalNorm.ambientCoordinate k).appTop
        (laurentGlobalUnit (.of k)).val) = _
  rw [hc]
  exact hv

/-- The full actual affine fundamental correspondence, with every original local length. -/
def WeightOneFundamentalNorm.affineFundamentalCorrespondence : point k ⟶ target k := by
  classical
  let : IsArtinianRing R := .of_finite k R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  exact ∑ p : MaximalSpectrum R, Finsupp.single (WeightOneFundamentalNorm.branchGenerator j hj p)
    ((Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal)).toNat : ℤ)

variable [IsNoetherianRing R]

/-- Forgetting admissibility recovers the finite pushforward of the literal
whole fundamental cycle, including nonreduced local multiplicities. -/
theorem WeightOneFundamentalNorm.toIntegralCycle_affineFundamentalCorrespondence :
    FiniteCorrespondence.toIntegralCycle (WeightOneFundamentalNorm.affineFundamentalCorrespondence j
        hj) =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of R))) := by
  classical
  let : IsArtinianRing R := .of_finite k R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  rw [fundamentalCycle_affine_eq_sum (k := k)]
  simp only [WeightOneFundamentalNorm.affineFundamentalCorrespondence, map_sum,
    FiniteCorrespondence.toIntegralCycle_single, IntegralCycle.finitePushforward_single,
    WeightOneFundamentalNorm.branchGenerator_support, residueDegree_of_surjectiveOnStalks,
        Nat.cast_one, mul_one]

omit [IsNoetherianRing R] in
/-- The existing point-cycle norm on the full fundamental correspondence is
the determinant norm on the entire unreduced finite algebra. -/
theorem WeightOneFundamentalNorm.cycleNorm_affineFundamentalCorrespondence :
    cycleNorm k (WeightOneFundamentalNorm.affineFundamentalCorrespondence j hj) =
      Additive.ofMul (Units.map (Algebra.norm k) (affineCoordinateUnit j)) := by
  classical
  let : IsArtinianRing R := .of_finite k R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  unfold WeightOneFundamentalNorm.affineFundamentalCorrespondence
  rw [map_sum]
  have hs : (∑ p : MaximalSpectrum R, cycleNorm k
      (Finsupp.single (WeightOneFundamentalNorm.branchGenerator j hj p)
        ((Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat : ℤ))) =
      ∑ p : MaximalSpectrum R,
        ((Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat : ℤ) •
          Additive.ofMul (generatorNorm (WeightOneFundamentalNorm.branchGenerator j hj p)) := by
    apply Finset.sum_congr rfl
    intro p _
    exact cycleNorm_single _ _
  rw [hs]
  simp only [WeightOneFundamentalNorm.branchGenerator,
      WeightOneFundamentalNorm.generatorNorm_fieldGenerator,
      WeightOneFundamentalNorm.affineCoordinateUnit_quotient]
  apply Additive.toMul.injective
  apply Units.ext
  simp only [toMul_sum, toMul_zsmul, toMul_ofMul,
    zpow_natCast, Units.coe_prod, Units.val_pow_eq_pow_val, Units.coe_map]
  exact (Algebra.norm_eq_prod_quotient_norm_pow_local_length
    (k := k) (affineCoordinateUnit j : R)).symm

include hj in
/-- Any actual correspondence whose integral cycle is the whole finite
fundamental pushforward has its genuine determinant norm. -/
theorem WeightOneFundamentalNorm.cycleNorm_eq_norm_of_affine_fundamental
    (α : point k ⟶ target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of R)))) :
    cycleNorm k α = Additive.ofMul (Units.map (Algebra.norm k)
        (WeightOneFundamentalNorm.affineCoordinateUnit j)) := by
  have h : α = WeightOneFundamentalNorm.affineFundamentalCorrespondence j hj :=
    FiniteCorrespondence.toIntegralCycle_injective
      (hα.trans (WeightOneFundamentalNorm.toIntegralCycle_affineFundamentalCorrespondence j
          hj).symm)
  rw [h, WeightOneFundamentalNorm.cycleNorm_affineFundamentalCorrespondence]

end FiniteAlgebra


section FiniteScheme

variable {k} {T : Scheme.{u}}

/-- The scalar map induced by the original finite structure morphism. -/
def WeightOneFundamentalNorm.schemeScalarMap (p : T ⟶ Spec (.of k)) : k →+* Γ(T, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The actual Laurent unit pulled back to the whole original finite scheme. -/
def WeightOneFundamentalNorm.schemeCoordinateUnit (j : T ⟶ WeightOneFundamentalNorm.ambient k) :
    Γ(T, ⊤)ˣ :=
  Units.map ((j ≫ WeightOneFundamentalNorm.ambientCoordinate k).appTop).hom.toMonoidHom
    (laurentGlobalUnit (.of k))

/-- Determinant norm on the whole coordinate algebra with the literal scalar map. -/
def WeightOneFundamentalNorm.schemeNorm (p : T ⟶ Spec (.of k)) (j : T ⟶
    WeightOneFundamentalNorm.ambient k) : kˣ :=
  let : Algebra k Γ(T, ⊤) := (WeightOneFundamentalNorm.schemeScalarMap p).toAlgebra
  Units.map (Algebra.norm k) (WeightOneFundamentalNorm.schemeCoordinateUnit j)

/-- Passing to the canonical affine chart preserves the actual Laurent unit. -/
theorem WeightOneFundamentalNorm.affineCoordinateUnit_isoSpec [IsAffine T] (j : T ⟶
    WeightOneFundamentalNorm.ambient k) :
    WeightOneFundamentalNorm.affineCoordinateUnit (T.isoSpec.inv ≫ j) =
        WeightOneFundamentalNorm.schemeCoordinateUnit j := by
  apply Units.ext
  have hi : T.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(T, ⊤)).hom = 𝟙 Γ(T, ⊤) := by
    rw [← Scheme.toSpecΓ_appTop T, ← Scheme.Hom.comp_appTop]
    change (T.isoSpec.hom ≫ T.isoSpec.inv).appTop = _
    rw [Iso.hom_inv_id]
    rfl
  have hv := ConcreteCategory.congr_hom hi
    ((j ≫ WeightOneFundamentalNorm.ambientCoordinate k).appTop (laurentGlobalUnit (.of k)).val)
  have hc : ((T.isoSpec.inv ≫ j) ≫ WeightOneFundamentalNorm.ambientCoordinate k).appTop =
      (j ≫ WeightOneFundamentalNorm.ambientCoordinate k).appTop ≫ T.isoSpec.inv.appTop := by
    rw [Category.assoc, Scheme.Hom.comp_appTop]
  change (Scheme.ΓSpecIso Γ(T, ⊤)).hom
      (((T.isoSpec.inv ≫ j) ≫ WeightOneFundamentalNorm.ambientCoordinate k).appTop
        (laurentGlobalUnit (.of k)).val) = _
  rw [hc]
  exact hv

/-- The actual full finite fundamental cycle has determinant norm in the
whole global algebra. No reducedness, separability, connectedness, or
integrality of the finite scheme is assumed. -/
theorem WeightOneFundamentalNorm.cycleNorm_eq_norm_of_fundamental [IsNoetherian T]
    (p : T ⟶ Spec (.of k)) [IsFinite p]
    (j : T ⟶ WeightOneFundamentalNorm.ambient k) [IsClosedImmersion j]
    (hp : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom = p)
    (α : point k ⟶ target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle T)) :
    cycleNorm k α = Additive.ofMul (WeightOneFundamentalNorm.schemeNorm p j) := by
  let : IsAffine T := isAffine_of_isAffineHom p
  let : Algebra k Γ(T, ⊤) := (WeightOneFundamentalNorm.schemeScalarMap p).toAlgebra
  let : Module.Finite k Γ(T, ⊤) := by
    change (WeightOneFundamentalNorm.schemeScalarMap p).Finite
    exact p.finite_appTop.comp (RingHom.Finite.of_surjective _
      (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)
  let : IsNoetherianRing Γ(T, ⊤) := .of_finite k _
  have hj : (T.isoSpec.inv ≫ j) ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom
        (SmoothSite.torusPower (.of k) 1).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k Γ(T, ⊤))) := by
    calc
      _ = T.isoSpec.inv ≫ p := by rw [Category.assoc, hp]
      _ = Spec.map p.appTop ≫ (Spec (.of k)).isoSpec.inv :=
        (Scheme.isoSpec_inv_naturality p).symm
      _ = _ := by
        rw [Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
        rfl
  have hf : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward (T.isoSpec.inv ≫ j)
        (fundamentalCycle (Spec Γ(T, ⊤))) := by
    rw [IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
      finitePushforward_fundamentalCycle]
    exact hα
  have hn := WeightOneFundamentalNorm.cycleNorm_eq_norm_of_affine_fundamental (T.isoSpec.inv ≫ j) hj
      α hf
  rw [WeightOneFundamentalNorm.affineCoordinateUnit_isoSpec] at hn
  exact hn

end FiniteScheme

end Motivic
