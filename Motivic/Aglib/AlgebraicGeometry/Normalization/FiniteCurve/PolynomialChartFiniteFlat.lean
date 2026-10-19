/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteCurve.PolynomialFiniteFlat
public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.Basic
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Norm.FiniteSchemeNormBaseChange

/-!
# Finite flat coefficient base change of an actual normalization chart

For an actual polynomial open chart in an integral scheme, a nonzero coefficient
localization makes its original generic finite-etale normalization finite flat
over that whole chart.
The conclusion is its literal scheme pullback, not a replacement algebra model.
The canonical open-range affine isomorphism supplies the polynomial coordinates,
and the native
normalization chart Cartesian square retains the original gluing morphism.

This is one whole affine-line chart. Gluing the two original projective-line
charts after a common coefficient localization remains a separate step.


Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.FiniteCurve.PolynomialChartFiniteFlat`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteCurve.ProjectiveFiniteFlat`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial TensorProduct nonZeroDivisors

attribute [local instance] Polynomial.algebra Algebra.TensorProduct.rightAlgebra

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization

universe u

/-- The original global generic normalization becomes finite flat above one
actual polynomial open chart after shrinking only its coefficient base. -/
theorem exists_free_polynomial_openChart_baseChange
    (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R[X]] [IsIntegrallyClosed R[X]]
    (X : Scheme.{u}) [IsIntegral X]
    (C : Scheme.FiniteEtale (Spec X.functionField))
    (chart : Spec (.of R[X]) ⟶ X) [IsOpenImmersion chart] :
    ∃ r : R, r ≠ 0 ∧
      let Ar := (Localization.Away r)[X]
      let f := (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
      let l := Spec.map (CommRingCat.ofHom (R := R[X]) (S := Ar)
        (algebraMap R[X] Ar)) ≫ chart
      let q := pullback.snd f l
      let : Algebra Ar Γ(pullback f l, ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap q).toAlgebra
      Module.Free Ar Γ(pullback f l, ⊤) ∧ IsFinite q ∧ Flat q := by
  let A := R[X]
  let U := chart.opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange chart
  let : Nonempty U := ⟨⟨chart (genericPoint (Spec (.of A))), by
    exact ⟨genericPoint (Spec (.of A)), rfl⟩⟩⟩
  let f := C.obj.hom ≫ X.fromSpecStalk (genericPoint X)
  let G := Γ(X, U)
  let E := Γ(C.obj.left, f ⁻¹ᵁ U)
  let T := integralClosure G E
  let eSpec : Spec (.of A) ≅ Spec G := chart.isoOpensRange ≪≫ hU.isoSpec
  let eRing : CommRingCat.of A ≅ G := (Scheme.Spec.preimageIso eSpec.symm).unop
  let e : A ≃+* G := eRing.commRingCatIsoToRingEquiv
  have he : Spec.map eRing.hom = eSpec.inv := by
    simp [eRing, ← Scheme.Spec_map]
  let : Algebra A G := e.toRingHom.toAlgebra
  let : Algebra A T := ((algebraMap G T).comp (algebraMap A G)).toAlgebra
  let : IsScalarTower A G T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsNoetherianRing G := isNoetherianRing_of_ringEquiv A e
  let : IsIntegrallyClosed G := IsIntegrallyClosed.of_equiv e
  let : IsFractionRing G X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  let : Module.IsTorsionFree G X.functionField :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (IsFractionRing.injective G X.functionField)
  let : Module.IsTorsionFree G E := Module.IsTorsionFree.trans X.functionField
  let : Module.IsTorsionFree A G :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr e.injective
  let : Module.IsTorsionFree A T := Module.IsTorsionFree.trans G
  let : Module.Finite G T := integralClosure.finite_of_etale G X.functionField E
  let : Module.Finite A G := RingHom.finite_algebraMap.mp
    (RingHom.Finite.of_surjective e.toRingHom e.surjective)
  let : Module.Finite A T := Module.Finite.trans G T
  let : Module.FinitePresentation A T := Module.finitePresentation_of_finite A T
  let S : Submonoid R[X] := R⁰.map Polynomial.C
  let : IsLocalization S (FractionRing R)[X] := Polynomial.isLocalization R⁰ (FractionRing R)
  let : Module.IsTorsionFree (FractionRing R)[X] ((FractionRing R)[X] ⊗[R[X]] T) :=
    IsLocalizedModule.isTorsionFree (TensorProduct.mk R[X] (FractionRing R)[X] T 1) S
  obtain ⟨r, hr, hfree⟩ := exists_free_polynomial_tensorProduct_away R (FractionRing R) T
  let Ar := (Localization.Away r)[X]
  let : Module.Free Ar (Ar ⊗[A] T) := hfree
  let j : Spec (.of T) ⟶ f.normalization := f.normalizationOpenCover.f ⟨U, hU⟩
  have hc := isPullback_chart X C U hU
  change IsPullback j
    (Spec.map (CommRingCat.ofHom (R := G) (S := T) (algebraMap G T)))
    f.fromNormalization hU.fromSpec at hc
  have hc' : IsPullback j
      (Spec.map (CommRingCat.ofHom (R := A) (S := T) (algebraMap A T)))
      f.fromNormalization chart := by
    refine hc.of_iso (Iso.refl _) (Iso.refl _) eSpec.symm (Iso.refl _)
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]) ?_
      (by simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]) ?_
    · simp only [Iso.refl_hom, Category.id_comp, Iso.symm_hom, ← he]
      exact (Spec.map_comp eRing.hom
        (CommRingCat.ofHom (R := G) (S := T) (algebraMap G T))).symm
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom]
      rw [Iso.eq_inv_comp]
      simp [eSpec, U]
  let q : Spec (.of (Ar ⊗[A] T)) ⟶ Spec (.of Ar) :=
    Spec.map (CommRingCat.ofHom (R := Ar) (S := Ar ⊗[A] T) (algebraMap Ar _))
  let z : Spec (.of (Ar ⊗[A] T)) ⟶ Spec (.of T) :=
    Spec.map (CommRingCat.ofHom (R := T) (S := Ar ⊗[A] T) (algebraMap T _))
  let l : Spec (.of Ar) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (R := A) (S := Ar) (algebraMap A Ar))
  have ht : IsPullback z q
      (Spec.map (CommRingCat.ofHom (R := A) (S := T) (algebraMap A T))) l :=
    (isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct A Ar T)).flip
  have hn : IsPullback (z ≫ j) q f.fromNormalization (l ≫ chart) :=
    ht.paste_horiz hc'
  let p := pullback.snd f.fromNormalization (l ≫ chart)
  let : Algebra Ar Γ(pullback f.fromNormalization (l ≫ chart), ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap p).toAlgebra
  let ei : Γ(Spec (.of (Ar ⊗[A] T)), ⊤) ≅
      Γ(pullback f.fromNormalization (l ≫ chart), ⊤) :=
    { hom := hn.isoPullback.inv.appTop
      inv := hn.isoPullback.hom.appTop
      hom_inv_id := by rw [← Scheme.Hom.comp_appTop]; simp
      inv_hom_id := by rw [← Scheme.Hom.comp_appTop]; simp }
  let es := (Scheme.ΓSpecIso (.of (Ar ⊗[A] T))).symm ≪≫ ei
  have hes : CommRingCat.ofHom (R := Ar) (S := Ar ⊗[A] T) (algebraMap Ar _) ≫ es.hom =
      (Scheme.ΓSpecIso (.of Ar)).inv ≫ p.appTop := by
    change _ ≫ (Scheme.ΓSpecIso (.of (Ar ⊗[A] T))).inv ≫
      hn.isoPullback.inv.appTop = _
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop]
    rw [hn.isoPullback_inv_snd]
  let eΓ : (Ar ⊗[A] T) ≃ₐ[Ar] Γ(pullback f.fromNormalization (l ≫ chart), ⊤) :=
    { es.commRingCatIsoToRingEquiv with
      commutes' a := congrArg (fun k : CommRingCat.of Ar ⟶
        Γ(pullback f.fromNormalization (l ≫ chart), ⊤) => k.hom a) hes }
  have hfinite : IsFinite q := by
    rw [IsFinite.SpecMap_iff]
    change RingHom.Finite (A := Ar) (B := Ar ⊗[A] T) (algebraMap Ar (Ar ⊗[A] T))
    rw [RingHom.finite_algebraMap]
    infer_instance
  have hflat : Flat q := by
    rw [Flat.SpecMap_iff]
    change RingHom.Flat (R := Ar) (S := Ar ⊗[A] T) (algebraMap Ar (Ar ⊗[A] T))
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  refine ⟨r, hr, Module.Free.of_equiv eΓ.toLinearEquiv, ?_, ?_⟩
  · let : IsFinite q := hfinite
    rw [← hn.isoPullback_inv_snd]
    infer_instance
  · let : Flat q := hflat
    rw [← hn.isoPullback_inv_snd]
    infer_instance

/-- The original finite-flat open-chart API is a specialization of the actual
free global-sections chart producer. -/
theorem exists_finite_flat_polynomial_openChart_baseChange
    (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R[X]] [IsIntegrallyClosed R[X]]
    (X : Scheme.{u}) [IsIntegral X]
    (C : Scheme.FiniteEtale (Spec X.functionField))
    (chart : Spec (.of R[X]) ⟶ X) [IsOpenImmersion chart] :
    ∃ r : R, r ≠ 0 ∧
      IsFinite (pullback.snd
        ((C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization)
        (Spec.map (CommRingCat.ofHom
          (R := R[X]) (S := (Localization.Away r)[X])
          (algebraMap R[X] (Localization.Away r)[X])) ≫ chart)) ∧
      Flat (pullback.snd
        ((C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization)
        (Spec.map (CommRingCat.ofHom
          (R := R[X]) (S := (Localization.Away r)[X])
          (algebraMap R[X] (Localization.Away r)[X])) ≫ chart)) := by
  obtain ⟨r, hr, _, hfinite, hflat⟩ :=
    exists_free_polynomial_openChart_baseChange R X C chart
  exact ⟨r, hr, hfinite, hflat⟩

/-- The original generic normalization over a polynomial affine chart becomes
finite flat after a nonzero coefficient localization. No comparison map or
flatness witness is supplied in the hypotheses. -/
theorem exists_finite_flat_polynomial_baseChange
    (R : Type u) [CommRing R] [IsDomain R]
    [IsNoetherianRing R[X]] [IsIntegrallyClosed R[X]]
    (C : Scheme.FiniteEtale (Spec (Spec (.of R[X])).functionField)) :
    ∃ r : R, r ≠ 0 ∧
      IsFinite (pullback.snd
        ((C.obj.hom ≫ (Spec (.of R[X])).fromSpecStalk
          (genericPoint (Spec (.of R[X])))).fromNormalization)
        (Spec.map (CommRingCat.ofHom
          (R := R[X]) (S := (Localization.Away r)[X])
          (algebraMap R[X] (Localization.Away r)[X])))) ∧
      Flat (pullback.snd
        ((C.obj.hom ≫ (Spec (.of R[X])).fromSpecStalk
          (genericPoint (Spec (.of R[X])))).fromNormalization)
        (Spec.map (CommRingCat.ofHom
          (R := R[X]) (S := (Localization.Away r)[X])
          (algebraMap R[X] (Localization.Away r)[X])))) := by
  obtain ⟨r, hr, hfinite, hflat⟩ :=
    exists_finite_flat_polynomial_openChart_baseChange R (Spec (.of R[X])) C (𝟙 _)
  rw [Category.comp_id] at hfinite hflat
  exact ⟨r, hr, hfinite, hflat⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
