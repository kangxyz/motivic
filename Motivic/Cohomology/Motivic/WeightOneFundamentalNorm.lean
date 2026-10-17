/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Motivic.WeightOnePointNorm
public import Motivic.AlgebraicGeometry.Cycles.FundamentalInvariance

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

universe u

namespace Motivic.WeightOneFundamentalNorm

open WeightOnePointNorm

variable (k : Type u) [Field k]

/-- The original product in which weight-one point supports lie. -/
abbrev ambient : Scheme.{u} :=
  pullback (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) 1).hom

/-- The actual first Laurent coordinate on the original product. -/
def ambientCoordinate : ambient k ⟶ SmoothSite.torus (.of k) |>.left :=
  pullback.snd (SmoothSite.base (Spec (.of k))).hom (SmoothSite.torusPower (.of k) 1).hom ≫
    (SmoothSite.torusCoordinate (.of k) 1 0).left

section Field

variable {k} {L : Type u} [Field L] [Algebra k L] [Module.Finite k L]
  (j : Spec (.of L) ⟶ ambient k) [IsClosedImmersion j]
  (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom =
    Spec.map (CommRingCat.ofHom (algebraMap k L)))

/-- An actual finite field branch determines its literal closed-image generator. -/
def fieldGenerator : Generator k := by
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

@[reassoc (attr := simp)]
theorem fieldGenerator_toImage_projection :
    j.toImage ≫ (fieldGenerator j hj).projection =
      Spec.map (CommRingCat.ofHom (algebraMap k L)) := by
  simpa [fieldGenerator, FiniteCorrespondenceGenerator.projection,
    correspondenceProjection] using hj

/-- The field support's actual global sections are the literal field branch,
with precisely the scalar map used by `generatorNorm`. -/
def fieldCoordinateEquiv : coordinateRing (fieldGenerator j hj) ≃ₐ[k] L :=
  { ((asIso j.toImage.appTop) ≪≫ Scheme.ΓSpecIso (.of L)).commRingCatIsoToRingEquiv with
    commutes' := by
      intro r
      have h : (j.toImage ≫ (fieldGenerator j hj).projection).appTop ≫
          (Scheme.ΓSpecIso (.of L)).hom =
          (Scheme.ΓSpecIso (.of k)).hom ≫ CommRingCat.ofHom (algebraMap k L) := by
        rw [fieldGenerator_toImage_projection, Scheme.ΓSpecIso_naturality]
      have hv := ConcreteCategory.congr_hom h ((Scheme.ΓSpecIso (.of k)).inv r)
      rw [Scheme.Hom.comp_appTop] at hv
      change (Scheme.ΓSpecIso (.of L)).hom
        (j.toImage.appTop ((fieldGenerator j hj).projection.appTop
          ((Scheme.ΓSpecIso (.of k)).inv r))) =
        algebraMap k L ((Scheme.ΓSpecIso (.of k)).hom
          ((Scheme.ΓSpecIso (.of k)).inv r)) at hv
      change (Scheme.ΓSpecIso (.of L)).hom
        (j.toImage.appTop ((fieldGenerator j hj).projection.appTop
          ((Scheme.ΓSpecIso (.of k)).inv r))) = algebraMap k L r
      simpa only [Iso.inv_hom_id_apply] using hv }


/-- The original Laurent unit, evaluated in the literal affine coordinate algebra. -/
def affineCoordinateUnit {R : Type u} [CommRing R]
    (j : Spec (.of R) ⟶ ambient k) : Rˣ :=
  Units.map (Scheme.ΓSpecIso (.of R)).hom.hom.toMonoidHom
    (Units.map ((j ≫ ambientCoordinate k).appTop).hom.toMonoidHom
      (laurentGlobalUnit (.of k)))

theorem fieldCoordinateEquiv_coordinate :
    fieldCoordinateEquiv j hj
        (coordinateUnit (fieldGenerator j hj) : coordinateRing (fieldGenerator j hj)) =
      (affineCoordinateUnit j : L) := by
  have h : j.toImage ≫ ((fieldGenerator j hj).targetProjection ≫
      (SmoothSite.torusCoordinate (.of k) 1 0).left) = j ≫ ambientCoordinate k := by
    change j.toImage ≫ j.imageι ≫ ambientCoordinate k = _
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  have ha := congrArg Scheme.Hom.appTop h
  rw [Scheme.Hom.comp_appTop] at ha
  have hv := ConcreteCategory.congr_hom ha (laurentGlobalUnit (.of k)).val
  exact congrArg (fun r => (Scheme.ΓSpecIso (.of L)).hom r) hv

/-- The existing geometric generator norm is the determinant norm on its
literal finite field branch. -/
theorem generatorNorm_fieldGenerator :
    generatorNorm (fieldGenerator j hj) =
      Units.map (Algebra.norm k) (affineCoordinateUnit j) := by
  apply Units.ext
  rw [generatorNorm_val]
  change Algebra.norm k (coordinateUnit (fieldGenerator j hj) :
      coordinateRing (fieldGenerator j hj)) =
    Algebra.norm k (affineCoordinateUnit j : L)
  rw [← fieldCoordinateEquiv_coordinate j hj]
  let e := fieldCoordinateEquiv j hj
  simp_rw [Algebra.norm_apply, ← LinearMap.det_conj _ e.toLinearEquiv]
  congr 1
  ext x
  simp [e]

end Field

section FiniteAlgebra

variable {k} {R : Type u} [CommRing R] [Algebra k R] [Module.Finite k R]

local instance quotientField (p : MaximalSpectrum R) : Field (R ⧸ p.asIdeal) :=
  Ideal.Quotient.field p.asIdeal

/-- Every quotient branch is included by the literal quotient homomorphism. -/
def quotientMap (p : MaximalSpectrum R) : Spec (.of (R ⧸ p.asIdeal)) ⟶ Spec (.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal))

instance (p : MaximalSpectrum R) : IsClosedImmersion (quotientMap p) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- The generic point of the actual maximal quotient maps to its original prime. -/
theorem quotientMap_genericPoint (p : MaximalSpectrum R) :
    quotientMap p (genericPoint (Spec (.of (R ⧸ p.asIdeal)))) = p.toPrimeSpectrum := by
  apply PrimeSpectrum.ext
  change Ideal.comap (Ideal.Quotient.mk p.asIdeal)
    (genericPoint (Spec (.of (R ⧸ p.asIdeal)))).asIdeal = p.asIdeal
  let q : PrimeSpectrum (R ⧸ p.asIdeal) := genericPoint (Spec (.of (R ⧸ p.asIdeal)))
  have hb : q.asIdeal = ⊥ := Ideal.eq_bot_of_prime q.asIdeal
  rw [hb]
  exact Ideal.mk_ker

/-- The actual reduced closed support of a quotient branch. -/
def quotientSupport (p : MaximalSpectrum R) : IntegralClosedSubscheme (Spec (.of R)) :=
  ⟨(quotientMap p).ker, IsIntegral.of_isIso (quotientMap p).toImage⟩

@[simp] theorem quotientSupport_point (p : MaximalSpectrum R) :
    (quotientSupport p).point = p.toPrimeSpectrum := by
  exact (imageι_genericPoint (quotientMap p)).trans (quotientMap_genericPoint p)

include k in
/-- Every point of a finite algebra is an actual component generic point. -/
theorem finiteAlgebra_mem_genericPoints (p : PrimeSpectrum R) :
    p ∈ genericPoints (Spec (.of R)) := by
  let : IsArtinianRing R := .of_finite k R
  have h : genericPoints (Spec (.of R)) = Set.univ := by
    rw [← genericPoints.closure (α := Spec (.of R))]
    exact (isClosed_discrete _).closure_eq.symm
  exact Set.eq_univ_iff_forall.mp h p

/-- The original scheme's stalk length is the literal localization length. -/
theorem affine_genericMultiplicity (p : MaximalSpectrum R) :
    genericMultiplicity ⟨p.toPrimeSpectrum, finiteAlgebra_mem_genericPoints (k := k) _⟩ =
      (Module.length (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal)).toNat := by
  unfold genericMultiplicity
  rw [ringLength_eq_of_ringEquiv
    (Spec.stalkIso (.of R) p.toPrimeSpectrum).commRingCatIsoToRingEquiv]
  rfl

/-- The full fundamental cycle includes every maximal quotient with its
original local length. -/
theorem fundamentalCycle_affine_eq_sum :
    let : IsArtinianRing R := .of_finite k R
    let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
    fundamentalCycle (Spec (.of R)) =
      ∑ p : MaximalSpectrum R, Finsupp.single (quotientSupport p)
        ((Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat : ℤ) := by
  classical
  let : IsArtinianRing R := .of_finite k R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  apply IntegralCycle.toPoints_injective
  rw [toPoints_fundamentalCycle, map_sum]
  simp only [IntegralCycle.toPoints_single, quotientSupport_point]
  ext q
  let p : MaximalSpectrum R := IsArtinianRing.primeSpectrumEquivMaximalSpectrum q
  have hp : p.toPrimeSpectrum = q := rfl
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single p]
  · rw [← hp, Finsupp.single_eq_same, fundamentalPointCycle_apply,
      dite_eq_left (finiteAlgebra_mem_genericPoints (k := k) _),
      affine_genericMultiplicity (k := k)]
  · intro r _ hr
    exact Finsupp.single_eq_of_ne (fun h => hr
      (MaximalSpectrum.toPrimeSpectrum_injective (h.symm.trans hp.symm)))
  · simp


variable (j : Spec (.of R) ⟶ ambient k) [IsClosedImmersion j]
  (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom =
    Spec.map (CommRingCat.ofHom (algebraMap k R)))

omit [Module.Finite k R] [IsClosedImmersion j] in
include hj in
/-- Scalar compatibility for each literal maximal quotient branch. -/
theorem branch_projection (p : MaximalSpectrum R) :
    (quotientMap p ≫ j) ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (R ⧸ p.asIdeal))) := by
  rw [Category.assoc, hj]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

/-- Every branch uses the actual image in the original source-target product. -/
def branchGenerator (p : MaximalSpectrum R) : Generator k :=
  fieldGenerator (quotientMap p ≫ j) (branch_projection j hj p)

/-- The geometric support of the branch is precisely finite pushforward of
its original quotient support. -/
theorem branchGenerator_support (p : MaximalSpectrum R) :
    (branchGenerator j hj p).toIntegralClosedSubscheme = (quotientSupport p).finiteImage j := by
  apply IntegralClosedSubscheme.point_injective
  rw [IntegralClosedSubscheme.point_finiteImage, quotientSupport_point]
  let := isIntegral_finiteImage (quotientMap p ≫ j)
  change (quotientMap p ≫ j).imageι (genericPoint (quotientMap p ≫ j).image) = _
  rw [imageι_genericPoint, Scheme.Hom.comp_apply, quotientMap_genericPoint]

omit [Algebra k R] [Module.Finite k R] [IsClosedImmersion j] in
/-- The pulled-back coordinate on a residue branch is its literal quotient image. -/
theorem affineCoordinateUnit_quotient (p : MaximalSpectrum R) :
    affineCoordinateUnit (quotientMap p ≫ j) =
      Units.map (Ideal.Quotient.mk p.asIdeal).toMonoidHom (affineCoordinateUnit j) := by
  apply Units.ext
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal))
  have hv := ConcreteCategory.congr_hom hn
    ((j ≫ ambientCoordinate k).appTop (laurentGlobalUnit (.of k)).val)
  change (Scheme.ΓSpecIso (.of (R ⧸ p.asIdeal))).hom
      ((quotientMap p).appTop
        ((j ≫ ambientCoordinate k).appTop (laurentGlobalUnit (.of k)).val)) =
    Ideal.Quotient.mk p.asIdeal ((Scheme.ΓSpecIso (.of R)).hom
        ((j ≫ ambientCoordinate k).appTop (laurentGlobalUnit (.of k)).val)) at hv
  have hc : ((quotientMap p ≫ j) ≫ ambientCoordinate k).appTop =
      (j ≫ ambientCoordinate k).appTop ≫ (quotientMap p).appTop := by
    rw [Category.assoc, Scheme.Hom.comp_appTop]
  change (Scheme.ΓSpecIso (.of (R ⧸ p.asIdeal))).hom
      (((quotientMap p ≫ j) ≫ ambientCoordinate k).appTop
        (laurentGlobalUnit (.of k)).val) = _
  rw [hc]
  exact hv

/-- The full actual affine fundamental correspondence, with every original local length. -/
def affineFundamentalCorrespondence : point k ⟶ target k := by
  classical
  let : IsArtinianRing R := .of_finite k R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  exact ∑ p : MaximalSpectrum R, Finsupp.single (branchGenerator j hj p)
    ((Module.length (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal)).toNat : ℤ)

variable [IsNoetherianRing R]

/-- Forgetting admissibility recovers the finite pushforward of the literal
whole fundamental cycle, including nonreduced local multiplicities. -/
theorem toIntegralCycle_affineFundamentalCorrespondence :
    FiniteCorrespondence.toIntegralCycle (affineFundamentalCorrespondence j hj) =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of R))) := by
  classical
  let : IsArtinianRing R := .of_finite k R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  rw [fundamentalCycle_affine_eq_sum (k := k)]
  simp only [affineFundamentalCorrespondence, map_sum,
    FiniteCorrespondence.toIntegralCycle_single, IntegralCycle.finitePushforward_single,
    branchGenerator_support, residueDegree_of_surjectiveOnStalks, Nat.cast_one, mul_one]

omit [IsNoetherianRing R] in
/-- The existing point-cycle norm on the full fundamental correspondence is
the determinant norm on the entire unreduced finite algebra. -/
theorem cycleNorm_affineFundamentalCorrespondence :
    cycleNorm k (affineFundamentalCorrespondence j hj) =
      Additive.ofMul (Units.map (Algebra.norm k) (affineCoordinateUnit j)) := by
  classical
  let : IsArtinianRing R := .of_finite k R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  unfold affineFundamentalCorrespondence
  rw [map_sum]
  have hs : (∑ p : MaximalSpectrum R, cycleNorm k
      (Finsupp.single (branchGenerator j hj p)
        ((Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat : ℤ))) =
      ∑ p : MaximalSpectrum R,
        ((Module.length (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal)).toNat : ℤ) •
          Additive.ofMul (generatorNorm (branchGenerator j hj p)) := by
    apply Finset.sum_congr rfl
    intro p _
    exact cycleNorm_single _ _
  rw [hs]
  simp only [branchGenerator, generatorNorm_fieldGenerator, affineCoordinateUnit_quotient]
  apply Additive.toMul.injective
  apply Units.ext
  simp only [toMul_sum, toMul_zsmul, toMul_ofMul,
    zpow_natCast, Units.coe_prod, Units.val_pow_eq_pow_val, Units.coe_map]
  exact (Algebra.norm_eq_prod_quotient_norm_pow_local_length
    (k := k) (affineCoordinateUnit j : R)).symm

include hj in
/-- Any actual correspondence whose integral cycle is the whole finite
fundamental pushforward has its genuine determinant norm. -/
theorem cycleNorm_eq_norm_of_affine_fundamental
    (α : point k ⟶ target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of R)))) :
    cycleNorm k α = Additive.ofMul (Units.map (Algebra.norm k) (affineCoordinateUnit j)) := by
  have h : α = affineFundamentalCorrespondence j hj :=
    FiniteCorrespondence.toIntegralCycle_injective
      (hα.trans (toIntegralCycle_affineFundamentalCorrespondence j hj).symm)
  rw [h, cycleNorm_affineFundamentalCorrespondence]

end FiniteAlgebra


section FiniteScheme

variable {k} {T : Scheme.{u}}

/-- The scalar map induced by the original finite structure morphism. -/
def schemeScalarMap (p : T ⟶ Spec (.of k)) : k →+* Γ(T, ⊤) :=
  p.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- The actual Laurent unit pulled back to the whole original finite scheme. -/
def schemeCoordinateUnit (j : T ⟶ ambient k) : Γ(T, ⊤)ˣ :=
  Units.map ((j ≫ ambientCoordinate k).appTop).hom.toMonoidHom
    (laurentGlobalUnit (.of k))

/-- Determinant norm on the whole coordinate algebra with the literal scalar map. -/
def schemeNorm (p : T ⟶ Spec (.of k)) (j : T ⟶ ambient k) : kˣ :=
  let : Algebra k Γ(T, ⊤) := (schemeScalarMap p).toAlgebra
  Units.map (Algebra.norm k) (schemeCoordinateUnit j)

/-- Passing to the canonical affine chart preserves the actual Laurent unit. -/
theorem affineCoordinateUnit_isoSpec [IsAffine T] (j : T ⟶ ambient k) :
    affineCoordinateUnit (T.isoSpec.inv ≫ j) = schemeCoordinateUnit j := by
  apply Units.ext
  have hi : T.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(T, ⊤)).hom = 𝟙 Γ(T, ⊤) := by
    rw [← Scheme.toSpecΓ_appTop T, ← Scheme.Hom.comp_appTop]
    change (T.isoSpec.hom ≫ T.isoSpec.inv).appTop = _
    rw [Iso.hom_inv_id]
    rfl
  have hv := ConcreteCategory.congr_hom hi
    ((j ≫ ambientCoordinate k).appTop (laurentGlobalUnit (.of k)).val)
  have hc : ((T.isoSpec.inv ≫ j) ≫ ambientCoordinate k).appTop =
      (j ≫ ambientCoordinate k).appTop ≫ T.isoSpec.inv.appTop := by
    rw [Category.assoc, Scheme.Hom.comp_appTop]
  change (Scheme.ΓSpecIso Γ(T, ⊤)).hom
      (((T.isoSpec.inv ≫ j) ≫ ambientCoordinate k).appTop
        (laurentGlobalUnit (.of k)).val) = _
  rw [hc]
  exact hv

/-- The actual full finite fundamental cycle has determinant norm in the
whole global algebra. No reducedness, separability, connectedness, or
integrality of the finite scheme is assumed. -/
theorem cycleNorm_eq_norm_of_fundamental [IsNoetherian T]
    (p : T ⟶ Spec (.of k)) [IsFinite p]
    (j : T ⟶ ambient k) [IsClosedImmersion j]
    (hp : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) 1).hom = p)
    (α : point k ⟶ target k)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle T)) :
    cycleNorm k α = Additive.ofMul (schemeNorm p j) := by
  let : IsAffine T := isAffine_of_isAffineHom p
  let : Algebra k Γ(T, ⊤) := (schemeScalarMap p).toAlgebra
  let : Module.Finite k Γ(T, ⊤) := by
    change (schemeScalarMap p).Finite
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
  have hn := cycleNorm_eq_norm_of_affine_fundamental (T.isoSpec.inv ≫ j) hj α hf
  rw [affineCoordinateUnit_isoSpec] at hn
  exact hn

end FiniteScheme

end Motivic.WeightOneFundamentalNorm
