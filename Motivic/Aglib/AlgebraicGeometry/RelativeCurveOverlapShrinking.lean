/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.CurveOpenShrinking
public import Motivic.Aglib.AlgebraicGeometry.EtaleCurveDimension
public import Motivic.AlgebraicGeometry.Cycles.GenericDominance
public import Aglib.AlgebraicGeometry.Stalk.FlatBaseChange
public import Aglib.AlgebraicGeometry.Spec.PolynomialLaurent.BaseChange
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Relative curve overlap shrinking over the original base

Only the generic fiber has dimension at most one. The original total space,
open overlap, smaller open, and finite prescribed subscheme are retained.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme

private theorem exists_specializes_of_mem_closure_range
    {E Y : Scheme.{u}} [IsNoetherian E] (f : E ⟶ Y) (y : Y)
    (hy : y ∈ closure (Set.range f)) : ∃ e : E, f e ⤳ y := by
  have hfin := genericPoints.finite
    (NoetherianSpace.finite_irreducibleComponents (α := E))
  have hd : closure (f '' genericPoints E) = closure (Set.range f) := by
    rw [← closure_image_closure f.continuous, genericPoints.closure, Set.image_univ]
  have he : f '' genericPoints E = ⋃ e ∈ genericPoints E, {f e} := by
    ext y
    simp [eq_comm]
  rw [← hd, he, hfin.closure_biUnion] at hy
  obtain ⟨e, _, hy⟩ := Set.mem_iUnion₂.mp hy
  exact ⟨e, specializes_iff_mem_closure.mpr hy⟩

/-- The complement of the closure of the original omitted overlap. -/
def overlapClosureComplement {Y : Scheme.{u}} (W : Y.Opens) (O : W.toScheme.Opens) :
    Y.Opens := ⟨(closure (W.ι '' (O : Set W.toScheme)ᶜ))ᶜ, isClosed_closure.isOpen_compl⟩

/-- Its original inverse-image open is contained in the original smaller overlap. -/
theorem overlapClosureComplement_preimage_le {Y : Scheme.{u}}
    (W : Y.Opens) (O : W.toScheme.Opens) :
    W.ι ⁻¹ᵁ overlapClosureComplement W O ≤ O := by
  intro x hx
  by_contra hn
  exact hx (subset_closure ⟨x, hn, rfl⟩)

/-- On a curve fiber, an omitted overlap point cannot specialize outside the
original overlap. Flatness transports component generic points to the total model. -/
theorem overlap_specialization_mem_of_curve_fiber
    {K Y : Scheme.{u}} [IsNoetherian K] [JacobsonSpace K]
    (j : K ⟶ Y) [Flat j] [IsPreimmersion j]
    (W : Y.Opens) (O : W.toScheme.Opens)
    (hO : genericPoints W.toScheme ⊆ (O : Set W.toScheme))
    (hdim : topologicalKrullDim K ≤ 1)
    {a b : K} (haW : j a ∈ W) (haO : (⟨j a, haW⟩ : W.toScheme) ∉ O)
    (hab : j a ⤳ j b) : j b ∈ W := by
  let V := j ⁻¹ᵁ W
  let O' := (j ∣_ W) ⁻¹ᵁ O
  let : IsNoetherian V.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _) }
  have hO' : genericPoints V.toScheme ⊆ (O' : Set V.toScheme) := by
    intro a ha
    exact hO (Motivic.mem_genericPoints_of_generalizing (j ∣_ W)
      (Flat.generalizingMap _) a ha)
  have hdim' : topologicalKrullDim V.toScheme ≤ 1 :=
    V.ι.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le.trans hdim
  have hc := (finite_closed_complement_of_genericPoints_subset O' hO' hdim').2
    (⟨a, haW⟩ : V.toScheme) (by
      change (j ∣_ W) ⟨a, haW⟩ ∉ O
      have he : (j ∣_ W) (⟨a, haW⟩ : V.toScheme) =
          (⟨j a, haW⟩ : W.toScheme) := Subtype.ext (morphismRestrict_base_coe j W _)
      rw [he]
      exact haO)
  have hc' : IsClosed ({a} : Set K) :=
    V.ι.closePoints_subset_preimage_closedPoints hc
  have hab' : a ⤳ b := j.isEmbedding.isInducing.specializes_iff.mp hab
  have he : b = a := by
    have := hab'.mem_closed hc' (by simp : a ∈ ({a} : Set K))
    exact Set.mem_singleton_iff.mp this
  simpa only [he] using haW

/-- A generic curve fiber detects that the actual closure of the omitted overlap
misses every prescribed point outside the overlap on that fiber. -/
theorem closure_overlap_avoids_generic_fiber
    {S Y K : Scheme.{u}} [IsIntegral S] [IsNoetherian Y]
    [IsNoetherian K] [JacobsonSpace K]
    (q : Y ⟶ S) (j : K ⟶ Y) [Flat j] [IsPreimmersion j]
    (hj : Set.range j = q ⁻¹' {genericPoint S})
    (W : Y.Opens) (O : W.toScheme.Opens)
    (hO : genericPoints W.toScheme ⊆ (O : Set W.toScheme))
    (hdim : topologicalKrullDim K ≤ 1)
    (y : Y) (hy : q y = genericPoint S) (hyW : y ∉ W) :
    y ∉ closure (W.ι '' (O : Set W.toScheme)ᶜ) := by
  let I := IdealSheafData.vanishingIdeal
    (⟨(O : Set W.toScheme)ᶜ, O.isOpen.isClosed_compl⟩ : Closeds W.toScheme)
  let e := I.subschemeι ≫ W.ι
  let : IsNoetherian W.toScheme :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := isCompact_iff_compactSpace.mp (NoetherianSpace.isCompact _) }
  let : IsNoetherian I.subscheme :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace I.subschemeι }
  have he : Set.range e = W.ι '' (O : Set W.toScheme)ᶜ := by
    rw [show Set.range e = W.ι '' Set.range I.subschemeι from by
      change Set.range (W.ι ∘ I.subschemeι) = _
      exact Set.range_comp _ _,
      IdealSheafData.range_subschemeι]
    simp [I]
  intro hbad
  obtain ⟨a, ha⟩ := exists_specializes_of_mem_closure_range e y (he.symm ▸ hbad)
  have hqa : q (e a) = genericPoint S := by
    have h := ha.map q.continuous
    rw [hy] at h
    exact (h.antisymm ((genericPoint_spec S).specializes (Set.mem_univ _))).eq
  obtain ⟨a', ha'⟩ := hj.ge (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hqa)
  obtain ⟨b', hb'⟩ := hj.ge (by simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hy)
  have haW : j a' ∈ W := by rw [ha']; exact (I.subschemeι a).property
  have haO : (⟨j a', haW⟩ : W.toScheme) ∉ O := by
    have hh : I.subschemeι a ∈ (O : Set W.toScheme)ᶜ := by
      have := I.range_subschemeι.le (Set.mem_range_self a)
      simpa [I] using this
    have ee : (⟨j a', haW⟩ : W.toScheme) = I.subschemeι a := by
      apply Subtype.ext
      exact ha'
    rw [ee]
    exact hh
  exact hyW (hb' ▸ overlap_specialization_mem_of_curve_fiber j W O hO hdim haW haO
    (by simpa only [ha', hb'] using ha))


private theorem range_fst_of_isPullback {P X Y S : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S}
    (H : IsPullback a b f g) : Set.range a = f ⁻¹' Set.range g := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨b t, (congrArg (fun h : P ⟶ S => h t) H.w).symm⟩
  · rintro ⟨y, hy⟩
    obtain ⟨t, ht, _⟩ := exists_preimage_of_isPullback H x y hy.symm
    exact ⟨t, ht⟩

/-- For the actual étale relative affine line, the closure of the omitted overlap
avoids the entire generic fiber outside the original overlap. -/
theorem closure_overlap_avoids_generic_of_etale_affineLine
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {Y : Scheme.{u}} (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p]
    (W : Y.Opens) (O : W.toScheme.Opens)
    (hO : genericPoints W.toScheme ⊆ (O : Set W.toScheme))
    (y : Y)
    (hy : (p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) y =
      genericPoint (Spec (.of R))) (hyW : y ∉ W) :
    y ∉ closure (W.ι '' (O : Set W.toScheme)ᶜ) := by
  let S := Spec (.of R)
  let E : CommRingCat.{u} := S.functionField
  let c : CommRingCat.of R ⟶ E :=
    StructureSheaf.toStalk R (genericPoint S)
  let b := Spec.map c
  have hb : b = S.fromSpecStalk (genericPoint S) := (Spec.fromSpecStalk_eq' _ _).symm
  let : Flat b := hb ▸ fromSpecStalk_flat S (genericPoint S)
  let : IsPreimmersion b := by rw [hb]; infer_instance
  let d := Spec.map (CommRingCat.PolynomialLaurent.polynomialMap c)
  let π := Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  have H : IsPullback d
      (Spec.map (CommRingCat.ofHom (Polynomial.C : E →+* Polynomial E))) π b :=
    (isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.PolynomialLaurent.polynomial_isPushout c)).flip
  let : Flat d := MorphismProperty.of_isPullback H.flip inferInstance
  let : IsPreimmersion d := MorphismProperty.of_isPullback H.flip inferInstance
  let K := pullback p d
  let j : K ⟶ Y := pullback.fst p d
  let t : K ⟶ Spec (.of (Polynomial E)) := pullback.snd p d
  let : Flat j := inferInstanceAs (Flat (pullback.fst p d))
  let : IsPreimmersion j := inferInstanceAs (IsPreimmersion (pullback.fst p d))
  let : Etale t := inferInstanceAs (Etale (pullback.snd p d))
  let : QuasiCompact t := inferInstanceAs (QuasiCompact (pullback.snd p d))
  let : IsNoetherian Y :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian p
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace p }
  let : IsNoetherian K :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian t
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace t }
  let : JacobsonSpace K := LocallyOfFiniteType.jacobsonSpace t
  let : Subsingleton (Spec E) := inferInstanceAs (Subsingleton (PrimeSpectrum E))
  have hbr : Set.range b = {genericPoint S} := by
    rw [hb]
    ext s
    constructor
    · rintro ⟨a, rfl⟩
      rw [Subsingleton.elim a (IsLocalRing.closedPoint E)]
      change S.fromSpecStalk (genericPoint S) (IsLocalRing.closedPoint E) = genericPoint S
      exact fromSpecStalk_closedPoint
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint E, fromSpecStalk_closedPoint⟩
  have hj : Set.range j = (p ≫ π) ⁻¹' {genericPoint S} := by
    calc
      Set.range j = p ⁻¹' Set.range d := Pullback.range_fst p d
      _ = p ⁻¹' (π ⁻¹' Set.range b) :=
        congrArg (fun A : Set (Spec (.of (Polynomial R))) => p ⁻¹' A)
          (range_fst_of_isPullback H)
      _ = p ⁻¹' (π ⁻¹' {genericPoint S}) :=
        congrArg (fun A : Set S => p ⁻¹' (π ⁻¹' A)) hbr
      _ = _ := rfl
  exact closure_overlap_avoids_generic_fiber (p ≫ π) j hj W O hO
    (topologicalKrullDim_le_one_of_etale_affineLine t) y hy hyW


/-- After a genuine principal shrinking of the original base, the complement of
`closure (W \ O)` retains the entire original finite prescribed scheme. Only the
actual generic fiber is a curve; the dimension of the total space is unrestricted. -/
theorem exists_base_principal_overlapClosureComplement
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {Y Z : Scheme.{u}} (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] [QuasiCompact p]
    (W : Y.Opens) (O : W.toScheme.Opens)
    (hO : genericPoints W.toScheme ⊆ (O : Set W.toScheme))
    (z : Z ⟶ Y)
    [IsFinite (z ≫ p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R)))]
    (hz : Disjoint (Set.range z) (W : Set Y)) :
    ∃ r : R, r ≠ 0 ∧
      (∀ a : Z,
        (z ≫ p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))) a ∈
          PrimeSpectrum.basicOpen r → z a ∈ overlapClosureComplement W O) ∧
      W.ι ⁻¹ᵁ overlapClosureComplement W O ≤ O := by
  let q := p ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : R →+* Polynomial R))
  let B : Set Y := closure (W.ι '' (O : Set W.toScheme)ᶜ)
  let V : (Spec (.of R)).Opens :=
    ⟨((z ≫ q) '' (z ⁻¹' B))ᶜ,
      ((z ≫ q).isClosedMap _ (isClosed_closure.preimage z.continuous)).isOpen_compl⟩
  have hη : genericPoint (Spec (.of R)) ∈ V := by
    rintro ⟨a, ha, he⟩
    exact closure_overlap_avoids_generic_of_etale_affineLine R p W O hO (z a) he
      (fun h => Set.disjoint_left.mp hz (Set.mem_range_self a) h) ha
  obtain ⟨_, ⟨r, rfl⟩, hr, hrV⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp V.isOpen _ hη
  have hr0 : r ≠ 0 := by
    intro he
    exact hr (he ▸ (genericPoint (Spec (.of R))).asIdeal.zero_mem)
  refine ⟨r, hr0, ?_, overlapClosureComplement_preimage_le W O⟩
  intro a ha hbad
  exact hrV ha ⟨a, hbad, rfl⟩

end AlgebraicGeometry.Scheme
