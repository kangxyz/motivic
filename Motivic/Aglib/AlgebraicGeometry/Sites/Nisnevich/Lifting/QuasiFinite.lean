/-
Copyright (c) 2026 Andrew Yang, Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-!
# Nisnevich neighborhoods isolating a quasi-finite branch

A separated morphism locally of finite type admits, at each quasi-finite point,
a pointed étale base neighborhood whose actual residue-field map is an
isomorphism and over which the chosen branch lies in a finite clopen piece.
The underlying point set of its fiber over the distinguished base point is a
singleton; the fiber need not be reduced.

The construction below adapts Andrew Yang's proof of
`AlgebraicGeometry.exists_etale_isCompl_of_quasiFiniteAt` in mathlib's
`Mathlib/AlgebraicGeometry/ZariskisMainTheorem.lean`, retaining the residue-field
and unique-prime data supplied by
`Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- On affine schemes, the actual residue-field map agrees with the map induced
by localization under the canonical residue-field isomorphisms. -/
@[reassoc]
lemma Scheme.Spec.residueFieldMap_residueFieldIso_hom
    {R T : CommRingCat.{u}} (φ : R ⟶ T) (p : PrimeSpectrum T) :
    (Spec.map φ).residueFieldMap p ≫ (Scheme.Spec.residueFieldIso T p).hom =
      (Scheme.Spec.residueFieldIso R (p.comap φ.hom)).hom ≫
        CommRingCat.ofHom (Ideal.ResidueField.map (p.comap φ.hom).asIdeal p.asIdeal
          φ.hom rfl) := by
  rw [← cancel_epi ((Spec R).residue ((Spec.map φ) p))]
  rw [Scheme.residue_residueFieldMap_assoc (Spec.map φ) p,
    Scheme.Spec.residue_residueFieldIso_hom]
  erw [Scheme.Spec.residue_residueFieldIso_hom_assoc,
    ← Scheme.localRingHom_comp_stalkIso]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Bijectivity of the algebraic residue-field map gives an isomorphism of the
actual scheme residue-field map. -/
lemma Scheme.Spec.isIso_residueFieldMap_of_bijective
    {R T : CommRingCat.{u}} (φ : R ⟶ T) (q : PrimeSpectrum T)
    (p : Ideal R) [p.IsPrime] (hp : p = q.asIdeal.comap φ.hom)
    (hb : Function.Bijective (Ideal.ResidueField.map p q.asIdeal φ.hom hp)) :
    IsIso ((Spec.map φ).residueFieldMap q) := by
  subst p
  have : IsIso (CommRingCat.ofHom (Ideal.ResidueField.map
      (q.comap φ.hom).asIdeal q.asIdeal φ.hom rfl)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  rw [← isIso_comp_right_iff _ (Scheme.Spec.residueFieldIso T q).hom,
    Scheme.Spec.residueFieldMap_residueFieldIso_hom]
  infer_instance

variable {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
/-- A quasi-finite branch of a separated, locally finite-type morphism becomes
finite and isolated after a pointed Nisnevich base change. The residue-field
isomorphism is the one induced by the neighborhood morphism itself. -/
theorem exists_nisnevich_isCompl_of_quasiFiniteAt [IsSeparated f]
    {x : X} {s : S} (h : f x = s) (hx : f.QuasiFiniteAt x) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ (u : U), g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ (V W : (pullback f g).Opens) (v : V),
      IsCompl V W ∧ IsFinite (V.ι ≫ pullback.snd f g) ∧
      pullback.fst f g v.1 = x ∧ pullback.snd f g v.1 = u ∧
      ∀ v' : V, pullback.snd f g v'.1 = u → v' = v := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hUV : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  have : (f.appLE U V hUV).hom.FiniteType := f.finiteType_appLE hU hV hUV
  algebraize [(f.appLE U V hUV).hom]
  have : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal := by
    suffices hU.primeIdealOf ⟨f x, hxU⟩ = Spec.map (f.appLE U V hUV) (hV.primeIdealOf ⟨x, hxV⟩) from
      ⟨congr(($this).1)⟩
    apply hU.isoSpec.inv.homeomorph.injective
    apply Subtype.ext
    simp only [IsAffineOpen.primeIdealOf, Scheme.Hom.homeomorph_apply,
      ← Scheme.Hom.comp_apply, ← Scheme.Opens.ι_apply, IsAffineOpen.isoSpec_hom]
    simp
  have : Algebra.QuasiFiniteAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hx.quasiFiniteAt hV hU hUV hxV
  obtain ⟨R, _, _, _, P, _, _, e, _, P', _, _, hP', heP', hb, _, hUnique⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
    (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : (algebraMap R (Localization.Away e)).Finite := RingHom.finite_algebraMap.mpr ‹_›
  let φ : Γ(S, U) ⟶ ↧R := CommRingCat.ofHom <| algebraMap Γ(S, U) R
  have hφ : φ.hom.Etale := RingHom.etale_algebraMap.mpr ‹_›
  have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff.mpr hφ
  let e₁ : Spec ↧(R ⊗ Γ(X, V)) ≅ pullback (Spec.map (f.appLE U V hUV)) (Spec.map φ) :=
    (pullbackSpecIso _ _ _).symm ≪≫ pullbackSymmetry _ _
  have he₁ : e₁.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
    dsimp [e₁, RingHom.algebraMap_toAlgebra]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullbackSpecIso_inv_snd ..
  let g : Spec ↧(R ⊗[Γ(S, U)] Γ(X, V)) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
    e₁.hom ≫ pullback.map _ _ _ _ hV.fromSpec (𝟙 _) hU.fromSpec
      (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)
  have he₂ : g ≫ pullback.snd f (Spec.map φ ≫ hU.fromSpec) =
      Spec.map (CommRingCat.ofHom (algebraMap R (R ⊗[Γ(S, U)] Γ(X, V)))) := by
    simpa [g, e₁, RingHom.algebraMap_toAlgebra, φ] using
      (pullbackSpecIso_inv_fst' Γ(S, U) R Γ(X, V))
  have hres : IsIso ((Spec.map φ).residueFieldMap ⟨P, ‹_›⟩) :=
    Scheme.Spec.isIso_residueFieldMap_of_bijective φ ⟨P, ‹_›⟩
      (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (P.over_def _) hb
  let W₁ := g ''ᵁ PrimeSpectrum.basicOpen e
  have : IsFinite (W₁.ι ≫ pullback.snd f _) := by
    let ι : Spec ↧(Localization.Away e) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
      Spec.map (CommRingCat.ofHom <| algebraMap _ _) ≫ g
    have : ι.opensRange = W₁ := by
      simp only [Scheme.Hom.opensRange_comp, ι, W₁]
      congr 1
      exact TopologicalSpace.Opens.ext <| PrimeSpectrum.localization_away_comap_range _ _
    rw [← this, ← MorphismProperty.cancel_left_of_respectsIso @IsFinite
      (Scheme.Hom.isoOpensRange _).hom]
    have H : (pullbackSpecIso _ R _).inv ≫ pullback.fst _ (Spec.map (f.appLE U V hUV)) = _ :=
      pullbackSpecIso_inv_fst ..
    simpa [Scheme.Hom.isoOpensRange, ι, g, e₁, RingHom.algebraMap_toAlgebra, φ, H,
      ← Spec.map_comp, IsFinite.SpecMap_iff]
  have : IsFinite W₁.ι := .of_comp _ (pullback.snd f _)
  let W₂ : (pullback f (Spec.map φ ≫ hU.fromSpec)).Opens :=
    ⟨W₁ᶜ, by simpa using W₁.ι.isClosedMap.isClosed_range⟩
  refine ⟨Spec ↧R, Spec.map φ ≫ hU.fromSpec, inferInstance,
    ⟨P, ‹_›⟩, ?_, ?_, W₁, W₂, ⟨g ⟨P', ‹_›⟩, ?_⟩, ?_, ‹_›, ?_, ?_, ?_⟩
  · dsimp [Spec.map_apply]
    convert! hU.fromSpec_primeIdealOf ⟨f x, hxU⟩
    · exact PrimeSpectrum.ext (Ideal.over_def _ _).symm
    · simp [h]
  · rw [Scheme.residueFieldMap_comp]
    infer_instance
  · exact ⟨⟨P', ‹_›⟩, heP', rfl⟩
  · simp [isCompl_iff, disjoint_iff, codisjoint_iff, W₂, SetLike.ext'_iff]
  · trans hV.fromSpec ⟨P'.comap Algebra.TensorProduct.includeRight.toRingHom, inferInstance⟩
    · simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, g, reassoc_of% he₁]; rfl
    convert! hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  · rw [← Scheme.Hom.comp_apply, he₂]
    exact PrimeSpectrum.ext (P'.over_def P).symm
  · intro z hz
    obtain ⟨Q, hQ, hzQ⟩ := z.2
    change g Q = z.1 at hzQ
    have hQP : Q.asIdeal.LiesOver P := by
      constructor
      have hQmap : Spec.map
          (CommRingCat.ofHom (algebraMap R (R ⊗[Γ(S, U)] Γ(X, V)))) Q = ⟨P, ‹_›⟩ := by
        rw [← he₂, Scheme.Hom.comp_apply, hzQ]
        exact hz
      exact congr(($hQmap).asIdeal).symm
    have hQeq : Q = ⟨P', ‹_›⟩ :=
      PrimeSpectrum.ext (hUnique Q.asIdeal Q.isPrime hQP hQ)
    exact Subtype.ext (hzQ.symm.trans (congrArg g hQeq))

end AlgebraicGeometry
