/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Diagonal.FinitePointEvaluation
public import Motivic.Cohomology.WeightOne.FundamentalNorm

/-!
# Evaluation of whole finite fundamental cycles in every diagonal weight

Each maximal quotient of the original, possibly nonreduced, finite algebra is
weighted by its original local length. Its map to the torus need only be finite:
the full degree over its actual image field is included before evaluation.
The resulting Milnor value is the sum of norms from the whole quotient fields.
No boundary descent, reducedness, or equality of image and residue fields is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.PolynomialLaurent
open scoped BigOperators

universe u

namespace Motivic.DiagonalFiniteFundamentalEvaluation
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Hom

open DiagonalPointNorm DiagonalFinitePointEvaluation MilnorK
open _root_.AlgebraicGeometry.Scheme.FiniteAlgebra (quotientMap quotientSupport
    quotientSupport_point
  quotientMap_genericPoint fundamentalCycle_affine_eq_sum)

variable {k : Type u} [Field k] {q : ℕ}

section FiniteAlgebra

variable {R : Type u} [CommRing R] [Algebra k R] [Module.Finite k R]

/-- The field structure on the quotient by a maximal ideal. -/
local instance quotientField (p : MaximalSpectrum R) : Field (R ⧸ p.asIdeal) :=
  Ideal.Quotient.field p.asIdeal

/-- The original local length, with nilpotents retained. -/
def localMultiplicity (p : MaximalSpectrum R) : ℕ :=
  (Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)).toNat

variable (j : Spec (.of R) ⟶ ambient k q) [IsFinite j]
  (hj : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom =
    Spec.map (CommRingCat.ofHom (algebraMap k R)))

omit [Module.Finite k R] [IsFinite j] in
include hj in
/-- Every quotient branch has its actual original structural scalar map. -/
theorem branch_projection (p : MaximalSpectrum R) :
    (quotientMap p ≫ j) ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom =
      Spec.map (CommRingCat.ofHom (algebraMap k (R ⧸ p.asIdeal))) := by
  rw [Category.assoc, hj]
  change Spec.map _ ≫ Spec.map _ = _
  rw [← Spec.map_comp]
  rfl

omit [Algebra k R] [Module.Finite k R] [IsFinite j] in
/-- All coordinates on a branch are their literal quotient images. -/
theorem affineCoordinateUnit_quotient (p : MaximalSpectrum R) (i : Fin q) :
    affineCoordinateUnit (quotientMap p ≫ j) i =
      Units.map (Ideal.Quotient.mk p.asIdeal).toMonoidHom (affineCoordinateUnit j i) := by
  apply Units.ext
  have hn := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk p.asIdeal))
  have hv := ConcreteCategory.congr_hom hn
    ((j ≫ ambientCoordinate k q i).appTop (laurentGlobalUnit (.of k)).val)
  change (Scheme.ΓSpecIso (.of (R ⧸ p.asIdeal))).hom
      ((quotientMap p).appTop
        ((j ≫ ambientCoordinate k q i).appTop (laurentGlobalUnit (.of k)).val)) =
    Ideal.Quotient.mk p.asIdeal ((Scheme.ΓSpecIso (.of R)).hom
        ((j ≫ ambientCoordinate k q i).appTop (laurentGlobalUnit (.of k)).val)) at hv
  have hc : ((quotientMap p ≫ j) ≫ ambientCoordinate k q i).appTop =
      (j ≫ ambientCoordinate k q i).appTop ≫ (quotientMap p).appTop := by
    rw [Category.assoc, Scheme.Hom.comp_appTop]
  change (Scheme.ΓSpecIso (.of (R ⧸ p.asIdeal))).hom
      (((quotientMap p ≫ j) ≫ ambientCoordinate k q i).appTop
        (laurentGlobalUnit (.of k)).val) = _
  rw [hc]
  exact hv

/-- The whole fundamental correspondence includes every local multiplicity and
all original degrees over the actual finite branch images. -/
def affineFundamentalCorrespondence :
    WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q := by
  classical
  let : IsArtinianRing R := .of_finite k R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  exact ∑ p : MaximalSpectrum R, (localMultiplicity p : ℤ) •
    finitePointCorrespondence (quotientMap p ≫ j) (branch_projection j hj p)

/-- A quotient field contributes its literal reduced support with coefficient one. -/
theorem finitePushforward_quotient_fundamental (p : MaximalSpectrum R) :
    IntegralCycle.finitePushforward (quotientMap p)
        (fundamentalCycle (Spec (.of (R ⧸ p.asIdeal)))) =
      Finsupp.single (quotientSupport p) 1 := by
  rw [fundamentalCycle_of_isIntegral, IntegralCycle.finitePushforward_single]
  have hs : (IntegralClosedSubscheme.pointClosure
      (genericPoint (Spec (.of (R ⧸ p.asIdeal))))).finiteImage (quotientMap p) =
      quotientSupport p := by
    apply IntegralClosedSubscheme.point_injective
    rw [IntegralClosedSubscheme.point_finiteImage,
      IntegralClosedSubscheme.point_pointClosure, quotientMap_genericPoint,
      quotientSupport_point]
  simp only [hs, residueDegree_of_surjectiveOnStalks, Nat.cast_one, mul_one]

/-- Forgetting admissibility recovers the full finite fundamental pushforward.
The morphism is finite, not necessarily a closed immersion. -/
theorem toIntegralCycle_affineFundamentalCorrespondence [IsNoetherianRing R] :
    FiniteCorrespondence.toIntegralCycle (affineFundamentalCorrespondence j hj) =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of R))) := by
  classical
  let : IsArtinianRing R := .of_finite k R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  rw [fundamentalCycle_affine_eq_sum (k := k)]
  simp only [affineFundamentalCorrespondence, map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [map_zsmul, toIntegralCycle_finitePointCorrespondence,
    IntegralCycle.finitePushforward_comp, AddMonoidHom.comp_apply,
    finitePushforward_quotient_fundamental, ← map_zsmul]
  congr 1
  simp [localMultiplicity, Finsupp.smul_single]

variable [CharZero k]

/-- The full local-length-weighted residue-field norm formula. -/
def affineFundamentalValue (a : Fin q → Rˣ) : K k q := by
  classical
  let : IsArtinianRing R := .of_finite k R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  exact ∑ p : MaximalSpectrum R, (localMultiplicity p : ℤ) •
    finiteExtensionNorm k (R ⧸ p.asIdeal) q
      (symbol (fun i => Units.map (Ideal.Quotient.mk p.asIdeal).toMonoidHom (a i)))

/-- Every original quotient field and local length survives in the actual value. -/
theorem cycleValue_affineFundamentalCorrespondence :
    cycleValue k q (affineFundamentalCorrespondence j hj) =
      affineFundamentalValue (k := k) (affineCoordinateUnit j) := by
  classical
  let : IsArtinianRing R := .of_finite k R
  let : Fintype (MaximalSpectrum R) := Fintype.ofFinite _
  simp only [affineFundamentalCorrespondence, map_sum, map_zsmul,
    cycleValue_finitePointCorrespondence, affineFundamentalValue]
  apply Finset.sum_congr rfl
  intro p _
  congr 3
  exact funext (affineCoordinateUnit_quotient j p)

include hj in
/-- Equality of actual fundamental cycles suffices; no norm identity is supplied. -/
theorem cycleValue_eq_norms_of_affine_fundamental [IsNoetherianRing R]
    (α : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of R)))) :
    cycleValue k q α = affineFundamentalValue (k := k) (affineCoordinateUnit j) := by
  have h : α = affineFundamentalCorrespondence j hj :=
    FiniteCorrespondence.toIntegralCycle_injective
      (hα.trans (toIntegralCycle_affineFundamentalCorrespondence j hj).symm)
  rw [h, cycleValue_affineFundamentalCorrespondence]

include hj in
/-- Evaluation with specified original units, still including all local lengths. -/
theorem cycleValue_eq_norms_units_of_affine_fundamental [IsNoetherianRing R]
    (a : Fin q → Rˣ) (ha : ∀ i, affineCoordinateUnit j i = a i)
    (α : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle (Spec (.of R)))) :
    cycleValue k q α = affineFundamentalValue (k := k) a := by
  rw [cycleValue_eq_norms_of_affine_fundamental j hj α hα, funext ha]

end FiniteAlgebra

section FiniteScheme

variable {T : Scheme.{u}}

/-- All literal Laurent coordinates on the whole original finite scheme. -/
def schemeCoordinateUnit (j : T ⟶ ambient k q) (i : Fin q) : Γ(T, ⊤)ˣ :=
  Units.map ((j ≫ ambientCoordinate k q i).appTop).hom.toMonoidHom
    (laurentGlobalUnit (.of k))

/-- Passing through the actual canonical affine chart preserves every coordinate. -/
theorem affineCoordinateUnit_isoSpec [IsAffine T] (j : T ⟶ ambient k q) (i : Fin q) :
    affineCoordinateUnit (T.isoSpec.inv ≫ j) i = schemeCoordinateUnit j i := by
  apply Units.ext
  have hi : T.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(T, ⊤)).hom = 𝟙 Γ(T, ⊤) := by
    rw [← Scheme.toSpecΓ_appTop T, ← Scheme.Hom.comp_appTop]
    change (T.isoSpec.hom ≫ T.isoSpec.inv).appTop = _
    rw [Iso.hom_inv_id]
    rfl
  have hv := ConcreteCategory.congr_hom hi
    ((j ≫ ambientCoordinate k q i).appTop (laurentGlobalUnit (.of k)).val)
  have hc : ((T.isoSpec.inv ≫ j) ≫ ambientCoordinate k q i).appTop =
      (j ≫ ambientCoordinate k q i).appTop ≫ T.isoSpec.inv.appTop := by
    rw [Category.assoc, Scheme.Hom.comp_appTop]
  change (Scheme.ΓSpecIso Γ(T, ⊤)).hom
      (((T.isoSpec.inv ≫ j) ≫ ambientCoordinate k q i).appTop
        (laurentGlobalUnit (.of k)).val) = _
  rw [hc]
  exact hv

/-- The whole finite global algebra uses the scalar map of the original morphism. -/
theorem schemeScalarMap_finite (p : T ⟶ Spec (.of k)) [IsFinite p] :
    (WeightOneFundamentalNorm.schemeScalarMap p).Finite := by
  exact p.finite_appTop.comp (RingHom.Finite.of_surjective _
    (Scheme.ΓSpecIso (.of k)).symm.commRingCatIsoToRingEquiv.surjective)

variable [CharZero k]

/-- The original global algebra's residue norms, with all original local lengths. -/
def schemeFundamentalValue (p : T ⟶ Spec (.of k)) [IsFinite p]
    (a : Fin q → Γ(T, ⊤)ˣ) : K k q := by
  let : Algebra k Γ(T, ⊤) := (WeightOneFundamentalNorm.schemeScalarMap p).toAlgebra
  let : Module.Finite k Γ(T, ⊤) := schemeScalarMap_finite p
  exact affineFundamentalValue (k := k) a

/-- An arbitrary finite scheme's actual fundamental cycle evaluates to its whole
local-length-weighted residue norms. Neither the scheme nor its finite map to
the torus is required to be reduced, integral, or a closed immersion. -/
theorem cycleValue_eq_norms_of_fundamental [IsNoetherian T]
    (p : T ⟶ Spec (.of k)) [IsFinite p]
    (j : T ⟶ ambient k q) [IsFinite j]
    (hp : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom = p)
    (α : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle T)) :
    cycleValue k q α = schemeFundamentalValue p (schemeCoordinateUnit j) := by
  let : IsAffine T := isAffine_of_isAffineHom p
  let : Algebra k Γ(T, ⊤) := (WeightOneFundamentalNorm.schemeScalarMap p).toAlgebra
  let : Module.Finite k Γ(T, ⊤) := schemeScalarMap_finite p
  let : IsNoetherianRing Γ(T, ⊤) := .of_finite k _
  have hj : (T.isoSpec.inv ≫ j) ≫
      pullback.fst (SmoothSite.base (Spec (.of k))).hom
        (SmoothSite.torusPower (.of k) q).hom =
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
  have hn := cycleValue_eq_norms_of_affine_fundamental (T.isoSpec.inv ≫ j) hj α hf
  rw [show affineCoordinateUnit (T.isoSpec.inv ≫ j) = schemeCoordinateUnit j from
    funext (affineCoordinateUnit_isoSpec j)] at hn
  exact hn

/-- Specified coordinate units on a whole finite scheme give the same complete
residue-norm sum, with no replacement by reduced or image coordinate algebras. -/
theorem cycleValue_eq_norms_units_of_fundamental [IsNoetherian T]
    (p : T ⟶ Spec (.of k)) [IsFinite p]
    (j : T ⟶ ambient k q) [IsFinite j]
    (hp : j ≫ pullback.fst (SmoothSite.base (Spec (.of k))).hom
      (SmoothSite.torusPower (.of k) q).hom = p)
    (a : Fin q → Γ(T, ⊤)ˣ) (ha : ∀ i, schemeCoordinateUnit j i = a i)
    (α : WeightOnePointNorm.point k ⟶ DiagonalCycleSymbols.target k q)
    (hα : FiniteCorrespondence.toIntegralCycle α =
      IntegralCycle.finitePushforward j (fundamentalCycle T)) :
    cycleValue k q α = schemeFundamentalValue p a := by
  rw [cycleValue_eq_norms_of_fundamental p j hp α hα, funext ha]

end FiniteScheme

end Motivic.DiagonalFiniteFundamentalEvaluation
