/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.FiniteCurve.PolynomialChartFiniteFlat
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.BaseChange
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveLine.Charts.Normal

/-!
# Finite flat coefficient shrinking of the original projective normalization

The two actual polynomial charts give two nonzero coefficients. Their product
shrinks only the coefficient base, and target locality glues the resulting finite
flat maps. The conclusion retains the original normalization and the literal
projective coefficient map.


Intended upstream module: `Aglib.AlgebraicGeometry.Normalization.FiniteCurve.ProjectiveFiniteFlat`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.RelativeAffineLine.FiniteFlat`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Polynomial

attribute [local instance] Polynomial.algebra

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization

universe u

private lemma property_pullback_snd_comp
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    {W X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (h : W ⟶ Y)
    (H : P (pullback.snd f g)) : P (pullback.snd f (h ≫ g)) := by
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd f g h,
    P.cancel_left_of_respectsIso]
  exact P.pullback_snd _ _ H

private def coefficientLocalizationMap
    {R : Type u} [CommRing R] (s r : R) (hsr : s ∣ r) :
    Localization.Away s →+* Localization.Away r :=
  IsLocalization.Away.lift s (IsLocalization.Away.isUnit_of_dvd r hsr)

private lemma polynomial_coefficientLocalizationMap_comp
    {R : Type u} [CommRing R] (s r : R) (hsr : s ∣ r) :
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (coefficientLocalizationMap s r hsr))) ≫
      Spec.map (CommRingCat.ofHom (R := R[X]) (S := (Localization.Away s)[X])
        (algebraMap R[X] (Localization.Away s)[X])) =
      Spec.map (CommRingCat.ofHom (R := R[X]) (S := (Localization.Away r)[X])
        (algebraMap R[X] (Localization.Away r)[X])) := by
  have hρ : (coefficientLocalizationMap s r hsr).comp
      (algebraMap R (Localization.Away s)) = algebraMap R (Localization.Away r) := by
    ext a
    exact IsLocalization.Away.lift_eq s (IsLocalization.Away.isUnit_of_dvd r hsr) a
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a <;> simp [hρ]

private lemma property_polynomial_localization_of_dvd
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (chart : Spec (.of R[X]) ⟶ X) (s r : R) (hsr : s ∣ r)
    (H : P (pullback.snd f
      (Spec.map (CommRingCat.ofHom (R := R[X]) (S := (Localization.Away s)[X])
        (algebraMap R[X] (Localization.Away s)[X])) ≫ chart))) :
    P (pullback.snd f
      (Spec.map (CommRingCat.ofHom (R := R[X]) (S := (Localization.Away r)[X])
        (algebraMap R[X] (Localization.Away r)[X])) ≫ chart)) := by
  let l := Spec.map (CommRingCat.ofHom
    (Polynomial.mapRingHom (coefficientLocalizationMap s r hsr)))
  have hl := polynomial_coefficientLocalizationMap_comp s r hsr
  have H' := property_pullback_snd_comp P f _ l H
  rw [← Category.assoc, hl] at H'
  exact H'

private lemma free_sections_polynomial_localization_of_dvd
    (R : Type u) [CommRing R] {X Y : Scheme.{u}} (f : Y ⟶ X)
    (chart : Spec (.of R[X]) ⟶ X) (s r : R) (hsr : s ∣ r) :
    let g := Spec.map (CommRingCat.ofHom (R := R[X]) (S := (Localization.Away s)[X])
      (algebraMap R[X] (Localization.Away s)[X])) ≫ chart
    let : Algebra (Localization.Away s)[X] Γ(pullback f g, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f g)).toAlgebra
    ∀ [IsFinite (pullback.snd f g)] [Module.Free (Localization.Away s)[X] Γ(pullback f g, ⊤)],
    let g' := Spec.map (CommRingCat.ofHom (R := R[X]) (S := (Localization.Away r)[X])
      (algebraMap R[X] (Localization.Away r)[X])) ≫ chart
    let : Algebra (Localization.Away r)[X] Γ(pullback f g', ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f g')).toAlgebra
    Module.Free (Localization.Away r)[X] Γ(pullback f g', ⊤) := by
  dsimp only
  intro hfinite hfree
  let g := Spec.map (CommRingCat.ofHom (R := R[X]) (S := (Localization.Away s)[X])
    (algebraMap R[X] (Localization.Away s)[X])) ≫ chart
  let q := pullback.snd f g
  let φ := Polynomial.mapRingHom (coefficientLocalizationMap s r hsr)
  let l := Spec.map (CommRingCat.ofHom φ)
  let : Algebra (Localization.Away s)[X] Γ(pullback f g, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap q).toAlgebra
  let : Module.Free (Localization.Away s)[X] Γ(pullback f g, ⊤) := hfree
  let : IsAffine (pullback f g) := isAffine_of_isAffineHom q
  let : Algebra (Localization.Away r)[X] Γ(pullback q l, ⊤) :=
    (FiniteSchemeNormBaseChange.scalarMap (pullback.snd q l)).toAlgebra
  let : Module.Free (Localization.Away r)[X] Γ(pullback q l, ⊤) :=
    FiniteSchemeNormBaseChange.sections_free_pullback q φ
  have H := FiniteSchemeNormBaseChange.sections_free_of_iso
    (pullback.snd q l) (pullback.snd f (l ≫ g)) (pullbackLeftPullbackSndIso f g l)
    (pullbackLeftPullbackSndIso_hom_snd f g l)
  have hl : l ≫ g = Spec.map (CommRingCat.ofHom
      (R := R[X]) (S := (Localization.Away r)[X])
      (algebraMap R[X] (Localization.Away r)[X])) ≫ chart := by
    dsimp only [g]
    rw [← Category.assoc, polynomial_coefficientLocalizationMap_comp]
  exact hl ▸ H

private def polynomialChartCover (R : Type u) [CommRing R] :
    (ProjectiveSpace R (ULift.{u} (Fin 2))).OpenCover :=
  Scheme.Cover.mkOfCovers (ULift.{u} (Fin 2))
    (fun _ ↦ Spec (.of R[X])) (RelativeProjectiveLine.chart R) (by
      intro x
      have hx : x ∈ (⨆ i, (RelativeProjectiveLine.chart R i).opensRange) := by
        rw [RelativeProjectiveLine.iSup_chart_opensRange]
        trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨i, hi⟩)

/-- A single nonzero coefficient makes the same original generic normalization
finite flat over the entire projective line after coefficient base change. -/
theorem exists_finite_flat_projective_baseChange
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R[X]] [IsIntegrallyClosed R[X]]
    (C : Scheme.FiniteEtale
      (Spec (ProjectiveSpace R (ULift.{u} (Fin 2))).functionField)) :
    ∃ r : R, r ≠ 0 ∧
      IsFinite (pullback.snd
        ((C.obj.hom ≫ (ProjectiveSpace R (ULift.{u} (Fin 2))).fromSpecStalk
          (genericPoint (ProjectiveSpace R (ULift.{u} (Fin 2))))).fromNormalization)
        (ProjectiveSpace.map (algebraMap R (Localization.Away r)) (ULift.{u} (Fin 2)))) ∧
      Flat (pullback.snd
        ((C.obj.hom ≫ (ProjectiveSpace R (ULift.{u} (Fin 2))).fromSpecStalk
          (genericPoint (ProjectiveSpace R (ULift.{u} (Fin 2))))).fromNormalization)
        (ProjectiveSpace.map (algebraMap R (Localization.Away r)) (ULift.{u} (Fin 2)))) := by
  let X := ProjectiveSpace R (ULift.{u} (Fin 2))
  let f := (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
  obtain ⟨s, hs, hsfin, hsflat⟩ :=
    exists_finite_flat_polynomial_openChart_baseChange R X C
      (RelativeProjectiveLine.chart R ⟨0⟩)
  obtain ⟨t, ht, htfin, htflat⟩ :=
    exists_finite_flat_polynomial_openChart_baseChange R X C
      (RelativeProjectiveLine.chart R ⟨1⟩)
  let r := s * t
  let A := Localization.Away r
  let m := ProjectiveSpace.map (algebraMap R A) (ULift.{u} (Fin 2))
  have hchart (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      (H₀ : P (pullback.snd f
        (Spec.map (CommRingCat.ofHom (R := R[X]) (S := (Localization.Away s)[X])
          (algebraMap R[X] (Localization.Away s)[X])) ≫ RelativeProjectiveLine.chart R ⟨0⟩)))
      (H₁ : P (pullback.snd f
        (Spec.map (CommRingCat.ofHom (R := R[X]) (S := (Localization.Away t)[X])
          (algebraMap R[X] (Localization.Away t)[X])) ≫ RelativeProjectiveLine.chart R ⟨1⟩)))
      (i : ULift.{u} (Fin 2)) :
      P (pullback.snd f (RelativeProjectiveLine.chart A i ≫ m)) := by
    rw [RelativeProjectiveLine.chart_map]
    rcases i with ⟨i⟩
    fin_cases i
    · exact property_polynomial_localization_of_dvd P R f _ s r (dvd_mul_right s t) H₀
    · exact property_polynomial_localization_of_dvd P R f _ t r (dvd_mul_left t s) H₁
  have hglobal (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
      [IsZariskiLocalAtTarget P]
      (H : ∀ i, P (pullback.snd f (RelativeProjectiveLine.chart A i ≫ m))) :
      P (pullback.snd f m) := by
    apply (IsZariskiLocalAtTarget.iff_of_openCover (P := P) (polynomialChartCover A)).mpr
    intro i
    change P (pullback.snd (pullback.snd f m) (RelativeProjectiveLine.chart A i))
    rw [← pullbackLeftPullbackSndIso_hom_snd f m (RelativeProjectiveLine.chart A i),
      P.cancel_left_of_respectsIso]
    exact H i
  let : IsZariskiLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u}) := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  let : IsZariskiLocalAtTarget (@Flat : MorphismProperty Scheme.{u}) := by
    set_option backward.isDefEq.respectTransparency false in infer_instance
  exact ⟨r, mul_ne_zero hs ht,
    hglobal @IsFinite (hchart @IsFinite hsfin htfin),
    hglobal @Flat (hchart @Flat hsflat htflat)⟩

/-- Both whole standard charts of the same normalization have free coordinate
modules after one coefficient localization. This is not global freeness on P1. -/
theorem exists_free_projective_chart_sections_baseChange
    (R : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R[X]] [IsIntegrallyClosed R[X]]
    (C : Scheme.FiniteEtale
      (Spec (ProjectiveSpace R (ULift.{u} (Fin 2))).functionField)) :
    ∃ r : R, r ≠ 0 ∧ ∀ i : ULift.{u} (Fin 2),
      let A := Localization.Away r
      let X := ProjectiveSpace R (ULift.{u} (Fin 2))
      let f := (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
      let g := RelativeProjectiveLine.chart A i ≫
        ProjectiveSpace.map (algebraMap R A) (ULift.{u} (Fin 2))
      let : Algebra A[X] Γ(pullback f g, ⊤) :=
        (FiniteSchemeNormBaseChange.scalarMap (pullback.snd f g)).toAlgebra
      Module.Free A[X] Γ(pullback f g, ⊤) := by
  let X := ProjectiveSpace R (ULift.{u} (Fin 2))
  let f := (C.obj.hom ≫ X.fromSpecStalk (genericPoint X)).fromNormalization
  obtain ⟨s, hs, hsfree, hsfin, _⟩ :=
    exists_free_polynomial_openChart_baseChange R X C (RelativeProjectiveLine.chart R ⟨0⟩)
  obtain ⟨t, ht, htfree, htfin, _⟩ :=
    exists_free_polynomial_openChart_baseChange R X C (RelativeProjectiveLine.chart R ⟨1⟩)
  refine ⟨s * t, mul_ne_zero hs ht, ?_⟩
  intro i
  dsimp only
  rw [RelativeProjectiveLine.chart_map]
  rcases i with ⟨i⟩
  fin_cases i
  · let q := pullback.snd f (Spec.map (CommRingCat.ofHom
      (R := R[X]) (S := (Localization.Away s)[X])
      (algebraMap R[X] (Localization.Away s)[X])) ≫ RelativeProjectiveLine.chart R ⟨0⟩)
    let : Algebra (Localization.Away s)[X] Γ(pullback f _, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap q).toAlgebra
    let : IsFinite q := hsfin
    let : Module.Free (Localization.Away s)[X] Γ(pullback f _, ⊤) := hsfree
    exact free_sections_polynomial_localization_of_dvd R f
      (RelativeProjectiveLine.chart R ⟨0⟩) s (s * t) (dvd_mul_right s t)
  · let q := pullback.snd f (Spec.map (CommRingCat.ofHom
      (R := R[X]) (S := (Localization.Away t)[X])
      (algebraMap R[X] (Localization.Away t)[X])) ≫ RelativeProjectiveLine.chart R ⟨1⟩)
    let : Algebra (Localization.Away t)[X] Γ(pullback f _, ⊤) :=
      (FiniteSchemeNormBaseChange.scalarMap q).toAlgebra
    let : IsFinite q := htfin
    let : Module.Free (Localization.Away t)[X] Γ(pullback f _, ⊤) := htfree
    exact free_sections_polynomial_localization_of_dvd R f
      (RelativeProjectiveLine.chart R ⟨1⟩) t (s * t) (dvd_mul_left t s)

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization
