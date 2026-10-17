/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.ProjectiveSpace.FixedBadLocusRetainedPresentation
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.OriginalEtalePresentation

/-! # An actual original-data étale curve presentation from one simultaneous quadratic tuple -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.Scheme.RelativeCurve
universe u
namespace QuadraticIncidence.InfinityChart

/-- The infinite-field closed-point presentation supplies every geometric input of the
original-section lifting theorem, preserving the literal original étale map, puncture,
full nonreduced closed scheme, field structure and selected point. -/
theorem nonempty_originalEtalePresentation
    (k B : Type u) [Field k] [Infinite k] [CommRing B] [IsDomain B] [Algebra k B]
    [Algebra.Smooth k B] (P : PrimeSpectrum B) [P.asIdeal.IsMaximal]
    (J : Ideal B) (hJ : J ≠ ⊥) {σ : Type u} [Finite σ] (g : σ → B)
    (hg : Algebra.adjoin k (Set.range g) = ⊤) (d : ℕ)
    (hd : Algebra.trdeg k B = (d + 1 : ℕ))
    {Y A : Scheme.{u}} (p : Y ⟶ Spec (.of B)) [Etale p] [QuasiCompact p] [IsSeparated p]
    (a : A ⟶ Spec (.of B)) [IsOpenImmersion a]
    (s : Spec (.of (B ⧸ J)) ⟶ Y)
    (hs : s ≫ p = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))
    (H : IsPullback s (𝟙 _) p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))))
    (ha : Disjoint (Set.range a)
      (Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))))
    (hcover : ∀ x : Spec (.of B), x ∈ Set.range a ∨
      x ∈ Set.range (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))) :
    Nonempty (OriginalEtalePresentation k (Spec.map (CommRingCat.ofHom (algebraMap k B)))
      p a (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))) s P) := by
  let := Fintype.ofFinite σ
  obtain ⟨I, _, hIJ, U, hU, hpU, _, c, _, N, i, π, V, t,
    hN, hNoeth, hnormal, hi, hπ, _, htail, hwhole, hV, hVa, hVs,
    ht, hbfin, hVaT, hIfin, hIret⟩ :=
    exists_fixed_bad_locus_retained_presentation k B P p J hJ g hg d hd 1 one_ne_zero
  let R := MvPolynomial (Fin d) k
  let f := Spec.map (CommRingCat.ofHom (quadraticCoordinateHom k B g d c))
  let Q := π ≫ ProjectiveSpace.toSpec R (ULift.{u} (Fin 2))
  let T : (Spec (.of R)).Opens := PrimeSpectrum.basicOpen t
  let zI := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let zJ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))
  have hQ : i ≫ Q = f := htail
  have : IsClosedImmersion zI :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsClosedImmersion zJ :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : IsFinite (p ∣_ U) := hpU
  have : IsIntegral N := hN
  have : IsLocallyNoetherian N := hNoeth
  have : IsOpenImmersion i := hi
  have : IsFinite π := hπ
  have : IsAffine V.toScheme := hVa
  have : SmoothOfRelativeDimension 1 (V.ι ≫ Q) := hVs
  have : IsAffine T.toScheme :=
    IsAffine.of_isIso (basicOpenIsoSpecAway (R := .of R) t).hom
  have hIfc : zI ≫ f = Spec.map (CommRingCat.ofHom
      ((Ideal.Quotient.mk I).comp (quadraticCoordinateHom k B g d c))) :=
    (Spec.map_comp _ _).symm
  have : IsFinite (zI ≫ f) := hIfc.symm ▸ hIfin
  have : IsFinite (zJ ≫ f) := prescribedSubquotient_finite B I J hIJ f
  have hzI : ∀ x : Spec (.of (B ⧸ I)), (zI ≫ f) x ∈ T → i (zI x) ∈ V := by
    intro x hx
    apply hIret x
    simpa only [hIfc] using hx
  have hzJ : ∀ x : Spec (.of (B ⧸ J)), (zJ ≫ f) x ∈ T → i (zJ x) ∈ V :=
    prescribedSubquotient_retained B I J hIJ i f T V hzI
  have hxT : Q (i P) ∈ T := by
    change (i ≫ Q) P ∈ T
    rw [htail]
    exact ht
  have hnorm : N.NormalStalks := fun x => ⟨inferInstance, hnormal x⟩
  obtain ⟨hCn, hCnoeth, hCnormal, hπT, _⟩ :=
    finiteProjectiveBaseRestriction_properties R (ULift.{u} (Fin 2)) π T hnorm (i P) hxT
  let r := retainedBaseToOriginal i Q T V hV
  let j := retainedBaseInclusion Q T V
  let πT := finiteProjectiveBaseRestriction R (ULift.{u} (Fin 2)) π T
  let tK := T.toScheme.isoSpec.inv ≫ T.ι ≫
    Spec.map (CommRingCat.ofHom (algebraMap k R))
  let zT := prescribedBaseToRetained i Q f htail T V hV zJ hzJ
  let sT := retainedEtaleClosedLift i Q f htail T V hV zJ hzJ p s hs
  let zIN := zI ≫ i
  let dT := coprod.desc (retainedBoundaryInclusion V ∣_ Q ⁻¹ᵁ T) (zIN ∣_ Q ⁻¹ᵁ T)
  have : IsFinite ((zI ≫ i) ≫ Q) := by simpa only [Category.assoc, hQ] using
    (inferInstance : IsFinite (zI ≫ f))
  have : IsClosedImmersion zIN := prescribed_closed_in_compactification i Q zI
  have : IsFinite ((retainedBoundaryInclusion V ≫ Q) ∣_ T) := hbfin
  have : IsFinite ((zIN ≫ Q) ∣_ T) := inferInstance
  have hretIN : ∀ x, (zIN ≫ Q) x ∈ T → zIN x ∈ V := by
    simpa only [zIN, Category.assoc, hQ, Scheme.Hom.comp_apply] using hzI
  obtain ⟨hdClosed, hdFinite⟩ := retained_prescribed_boundary_on_base Q V zIN T hretIN
  have : IsFinite (dT ≫ (Q ∣_ T)) := hdFinite
  have : IsFinite (zT ≫ ((V.ι ≫ Q) ∣_ T)) :=
    prescribedBaseToRetained_finite i Q f htail T V hV zJ hzJ
  have hbR : Smooth (Spec.map (CommRingCat.ofHom (algebraMap k R))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have hrbase : r ≫ f = ((V.ι ≫ Q) ∣_ T) ≫ T.ι := by
    rw [morphismRestrict_ι, ← hQ, ← Category.assoc r, retainedBaseToOriginal_comp]
    simp only [Category.assoc]
  have hfield : f ≫ Spec.map (CommRingCat.ofHom (algebraMap k R)) =
      Spec.map (CommRingCat.ofHom (algebraMap k B)) := by
    rw [← Spec.map_comp]
    congr 1
    ext x
    exact (MvPolynomial.aeval (fun i => aeval g (parameterTuple k σ d c i).val)).commutes x
  refine ⟨{
    base := Γ(T.toScheme, ⊤)
    base_noetherian := (restrictedBaseCoefficientMap_properties k R T).1
    toField := tK
    base_smooth := inferInstance
    target := (retainedBaseOpen Q T V).toScheme
    target_affine := hVaT
    refinement := r
    refinement_open := inferInstance
    point := ⟨⟨i P, hwhole P rfl⟩, hxT⟩
    point_eq := retainedBaseToOriginal_point i Q T V hV P (hwhole P rfl) hxT
    compact := (Q ⁻¹ᵁ T).toScheme
    compact_integral := hCn
    compact_noetherian := hCnoeth
    compact_normal := fun x => (hCnormal x).2
    projectiveMap := πT
    projective_finite := hπT
    inclusion := j
    inclusion_open := inferInstance
    target_smooth := finiteProjectiveBaseRestriction_retained_smooth R _ π T V
    base_compatibility := ?_
    closed := ((zJ ≫ f) ⁻¹ᵁ T).toScheme
    closedToOriginal := ((zJ ≫ f) ⁻¹ᵁ T).ι
    closedInclusion := zT
    closed_cartesian := prescribedBaseToRetained_isPullback i Q f htail T V hV zJ hzJ
    closed_finite := ?_
    closedLift := sT
    closedLift_original := retainedEtaleClosedLift_fst i Q f htail T V hV zJ hzJ p s hs
    closedLift_eq := retainedEtaleClosedLift_snd i Q f htail T V hV zJ hzJ p s hs
    closedLift_closed := retainedEtaleClosedLift_closed i Q f htail T V hV zJ hzJ p s hs H
    closedLift_cartesian := retainedEtaleClosedLift_isPullback i Q f htail T V hV zJ hzJ p s hs H
    punctured_disjoint := retainedPunctured_disjoint i Q f htail T V hV zJ hzJ a ha
    punctured_cover := retainedPunctured_cover i Q f htail T V hV zJ hzJ a hcover
    boundary := _
    boundaryInclusion := dT
    boundary_closed := hdClosed
    boundary_finite := ?_
    goodOpen := r ⁻¹ᵁ U
    good_finite := Scheme.finite_pullback_on_original_chart p r U
    bad_cover := ?_ }⟩
  · rw [← hfield, ← Category.assoc, hrbase]
    simp only [πT, tK, Category.assoc, finiteProjectiveBaseRestriction_toSpec_assoc,
      Iso.hom_inv_id_assoc]
    exact (retainedBaseInclusion_projection_assoc Q T V _).symm
  · change IsFinite (zT ≫ j ≫ πT ≫ ProjectiveSpace.toSpec _ _)
    rw [finiteProjectiveBaseRestriction_toSpec, retainedBaseInclusion_projection_assoc,
      ← Category.assoc]
    infer_instance
  · change IsFinite (dT ≫ πT ≫ ProjectiveSpace.toSpec _ _)
    rw [finiteProjectiveBaseRestriction_toSpec, ← Category.assoc]
    infer_instance
  · simpa only [r, j, dT, zIN, zI, Scheme.Hom.coe_image,
      Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, Scheme.Opens.range_ι]
      using retained_base_bad_chart_cover B I i Q T V hV U hU

end QuadraticIncidence.InfinityChart
