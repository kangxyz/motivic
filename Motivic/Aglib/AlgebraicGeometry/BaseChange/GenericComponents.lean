/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.RingTheory.Spectrum.Prime.FlatScalarMinimalPrimes
public import Motivic.Aglib.AlgebraicGeometry.Stalk.KernelMinimalPrimes
public import Motivic.Aglib.AlgebraicGeometry.Cycles.Fundamental.Invariance
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.CartesianAffineAlgebra
public import Motivic.Aglib.AlgebraicGeometry.Scheme.DomainStalkComponents
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Generic components after arbitrary flat base change

An actual flat base change of a finite surjective map between integral schemes
has every component dominating each integral target chart. The original finite
map need not be flat, and the flat test map need not be of finite type. The
actual pullback may have nilpotents and several components.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Hom

private theorem injective_of_spec_surjective_flatBaseChange
    {R B : Type u} [CommRing R] [CommRing B] [IsDomain R]
    (φ : R →+* B) (hφ : Function.Surjective (PrimeSpectrum.comap φ)) :
    Function.Injective φ := by
  obtain ⟨p, hp⟩ := hφ ⟨⊥, inferInstance⟩
  apply (RingHom.injective_iff_ker_eq_bot φ).mpr
  apply le_bot_iff.mp
  have h : RingHom.ker φ ≤ p.asIdeal.comap φ := Ideal.ker_le_comap φ
  simpa only [PrimeSpectrum.ext_iff] using h.trans_eq (congrArg PrimeSpectrum.asIdeal hp)

/-- The actual tensor-product affine pullback sends every component generic to
a generic point of the new integral base. -/
theorem mem_genericPoints_pullbackFst_spec_flat
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [IsDomain R] [IsDomain S]
    [Module.Flat R S] [Module.IsTorsionFree R B]
    (w : (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) : Scheme.{u}))
    (hw : w ∈ genericPoints (pullback (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) : Scheme.{u})) :
    pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B))) w ∈ genericPoints (Spec (.of S)) := by
  have hw' := (mem_genericPoints_iff_of_isIso (pullbackSpecIso R S B).hom w).mpr hw
  have hmin := (spec_mem_genericPoints_iff_minimalPrime _ _).mp hw'
  have hbot := Ideal.under_eq_bot_of_mem_minimalPrimes_tensorProduct hmin
  have hgeneric : (Spec.map (CommRingCat.ofHom (algebraMap S (S ⊗[R] B))))
      ((pullbackSpecIso R S B).hom w) ∈ genericPoints (Spec (.of S)) := by
    apply (spec_mem_genericPoints_iff_minimalPrime S _).mpr
    rw [IsDomain.minimalPrimes_eq_singleton_bot]
    exact Set.mem_singleton_iff.mpr hbot
  simpa only [← Scheme.Hom.comp_apply, pullbackSpecIso_hom_fst'] using hgeneric

/-- Generic preservation transported through the canonical affine scheme
isomorphisms and the actual given Cartesian square. -/
theorem mem_genericPoints_of_isPullback_flat_affine
    {W A B Y : Scheme.{u}} [IsAffine A] [IsAffine Y]
    [IsIntegral A] [IsIntegral B] [IsIntegral Y]
    (p : W ⟶ A) (q : W ⟶ B) (g : A ⟶ Y) (f : B ⟶ Y)
    (H : IsPullback p q g f) [IsFinite f] [Surjective f] [Flat g]
    (w : W) (hw : w ∈ genericPoints W) : p w ∈ genericPoints A := by
  have : IsAffine B := isAffine_of_isAffineHom f
  let R := Γ(Y, ⊤)
  let S := Γ(A, ⊤)
  let T := Γ(B, ⊤)
  algebraize [g.appTop.hom, f.appTop.hom]
  have : Module.Flat R S := RingHom.flat_algebraMap_iff.mp g.flat_appTop
  have hf : Function.Surjective (PrimeSpectrum.comap (algebraMap R T)) := by
    intro x
    obtain ⟨b, hb⟩ := f.surjective (Y.isoSpec.inv x)
    refine ⟨B.isoSpec.hom b, ?_⟩
    have h := congrArg (fun e : B ⟶ Spec R ↦ e b) (Scheme.isoSpec_hom_naturality f)
    change (Spec.map f.appTop) (B.isoSpec.hom b) = Y.isoSpec.hom (f b) at h
    rw [hb] at h
    exact h.trans (Scheme.inv_hom_apply Y.isoSpec x)
  have : Module.IsTorsionFree R T := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (injective_of_spec_surjective_flatBaseChange (algebraMap R T) hf)
  have H' : IsPullback (p ≫ A.isoSpec.hom) (q ≫ B.isoSpec.hom)
      (Spec.map g.appTop) (Spec.map f.appTop) :=
    H.of_iso (Iso.refl _) A.isoSpec B.isoSpec Y.isoSpec
      (by simp) (by simp) (Scheme.isoSpec_hom_naturality g).symm
      (Scheme.isoSpec_hom_naturality f).symm
  have hw' := (mem_genericPoints_iff_of_isIso H'.isoPullback.hom w).mpr hw
  have hp : pullback.fst (Spec.map g.appTop) (Spec.map f.appTop)
      (H'.isoPullback.hom w) ∈ genericPoints (Spec S) :=
    mem_genericPoints_pullbackFst_spec_flat R S T (H'.isoPullback.hom w) hw'
  have hp' : A.isoSpec.hom (p w) ∈ genericPoints (Spec S) := by
    simpa only [← Scheme.Hom.comp_apply, H'.isoPullback_hom_fst] using hp
  exact (mem_genericPoints_iff_of_isIso A.isoSpec.hom (p w)).mp hp'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Every actual component of a finite integral support remains dominant after
an arbitrary flat base change to an integral scheme. -/
theorem mem_genericPoints_of_isPullback_flat_integral
    {W A B Y : Scheme.{u}} [IsIntegral A] [IsIntegral B] [IsIntegral Y]
    (p : W ⟶ A) (q : W ⟶ B) (g : A ⟶ Y) (f : B ⟶ Y)
    (H : IsPullback p q g f) [IsFinite f] [Surjective f] [Flat g]
    (w : W) (hw : w ∈ genericPoints W) : p w ∈ genericPoints A := by
  obtain ⟨U, hU, hwU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := g (p w)) (by simp)
  obtain ⟨V, hV, hwV, hVU⟩ :=
    exists_isAffineOpen_mem_and_subset (U := g ⁻¹ᵁ U) hwU
  have : Nonempty U := ⟨⟨g (p w), hwU⟩⟩
  have : Nonempty V := ⟨⟨p w, hwV⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨b, hb⟩ := f.surjective (g (p w))
    exact ⟨⟨b, by simpa only [Scheme.Hom.mem_preimage, hb] using hwU⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion U.ι
  have : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  have : IsIntegral (f ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  let : IsAffine U.toScheme := hU
  let : IsAffine V.toScheme := hV
  have : Surjective (f ∣_ U) :=
    IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance U
  have : Flat (g.resLE U V hVU) := by
    delta Scheme.Hom.resLE
    infer_instance
  have H' := (FiniteCartesianAffineAlgebra.restricted_isPullback H.flip hVU).flip
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at H'
  let w' : (p ⁻¹ᵁ V).toScheme := ⟨w, hwV⟩
  have hw' : w' ∈ genericPoints (p ⁻¹ᵁ V).toScheme :=
    mem_genericPoints_of_isOpenImmersion (p ⁻¹ᵁ V).ι w' hw
  have hp := mem_genericPoints_of_isPullback_flat_affine _ _ _ _ H' w' hw'
  have hp' := mem_genericPoints_of_generalizing V.ι V.ι.isOpenEmbedding.generalizingMap
    ((p ∣_ V) w') hp
  change ((p ∣_ V) w').1 ∈ genericPoints A at hp'
  simpa only [morphismRestrict_base_coe] using hp'

/-- The reduced point-closure of each generic point surjects onto the integral
new base. The whole original pullback need not be reduced or irreducible. -/
theorem surjective_pointClosure_of_isPullback_flat_integral
    {W A B Y : Scheme.{u}} [IsIntegral A] [IsIntegral B] [IsIntegral Y]
    (p : W ⟶ A) (q : W ⟶ B) (g : A ⟶ Y) (f : B ⟶ Y)
    (H : IsPullback p q g f) [IsFinite f] [Surjective f] [Flat g]
    (w : W) (hw : w ∈ genericPoints W) :
    Function.Surjective ((IntegralClosedSubscheme.pointClosure w).val.subschemeι ≫ p) := by
  have : IsFinite p := MorphismProperty.of_isPullback H.flip inferInstance
  have hp := mem_genericPoints_of_isPullback_flat_integral p q g f H w hw
  have heq : closure ({p w} : Set A) = Set.univ := by
    simpa only [genericPoints, Set.mem_ofPred_eq, irreducibleComponents_eq_singleton,
      Set.mem_singleton_iff] using hp
  apply Set.range_eq_univ.mp
  change Set.range (p ∘ (IntegralClosedSubscheme.pointClosure w).val.subschemeι) = Set.univ
  rw [Set.range_comp, (IntegralClosedSubscheme.pointClosure w).val.range_subschemeι,
    IntegralClosedSubscheme.support_pointClosure,
    ← p.isClosedMap.closure_image_eq_of_continuous p.continuous, Set.image_singleton, heq]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The new target may have several disjoint integral open components. -/
theorem mem_genericPoints_of_isPullback_flat_domainStalks
    {W A B Y : Scheme.{u}} [IsNoetherian A] [IsIntegral B] [IsIntegral Y]
    (p : W ⟶ A) (q : W ⟶ B) (g : A ⟶ Y) (f : B ⟶ Y)
    (H : IsPullback p q g f) [IsFinite f] [Surjective f] [Flat g]
    (hA : ∀ a : A, IsDomain (A.presheaf.stalk a))
    (w : W) (hw : w ∈ genericPoints W) : p w ∈ genericPoints A := by
  let C := domainStalkComponentOpen hA (irreducibleComponent (p w))
    (irreducibleComponent_mem_irreducibleComponents (p w))
  have hwC : p w ∈ C := mem_irreducibleComponent
  have : IsIntegral C.toScheme := isIntegral_domainStalkComponentOpen hA _ _
  have H' : IsPullback (p ∣_ C) ((p ⁻¹ᵁ C).ι ≫ q) (C.ι ≫ g) f :=
    (isPullback_morphismRestrict p C).paste_vert H
  let w' : (p ⁻¹ᵁ C).toScheme := ⟨w, hwC⟩
  have hw' : w' ∈ genericPoints (p ⁻¹ᵁ C).toScheme :=
    mem_genericPoints_of_isOpenImmersion (p ⁻¹ᵁ C).ι w' hw
  have hp := mem_genericPoints_of_isPullback_flat_integral _ _ _ _ H' w' hw'
  have hp' := mem_genericPoints_of_generalizing C.ι C.ι.isOpenEmbedding.generalizingMap
    ((p ∣_ C) w') hp
  change ((p ∣_ C) w').1 ∈ genericPoints A at hp'
  simpa only [morphismRestrict_base_coe] using hp'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An arbitrary flat base change of an integral finite support over one
component preserves component genericity, allowing disconnected ambient bases. -/
theorem mem_genericPoints_of_isPullback_flat_component
    {W A B Y : Scheme.{u}} [IsNoetherian A] [IsNoetherian Y] [IsIntegral B]
    (p : W ⟶ A) (q : W ⟶ B) (g : A ⟶ Y) (f : B ⟶ Y)
    (H : IsPullback p q g f) [IsFinite f] [Flat g]
    (hf : Set.range f ∈ irreducibleComponents Y)
    (hA : ∀ a : A, IsDomain (A.presheaf.stalk a))
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y))
    (w : W) (hw : w ∈ genericPoints W) : p w ∈ genericPoints A := by
  let U := domainStalkComponentOpen hY (Set.range f) hf
  have : IsIntegral U.toScheme := isIntegral_domainStalkComponentOpen hY _ _
  have : Nonempty (f ⁻¹ᵁ U) := by
    obtain ⟨b⟩ := (inferInstance : Nonempty B)
    exact ⟨⟨b, ⟨b, rfl⟩⟩⟩
  have : IsIntegral (f ⁻¹ᵁ U).toScheme :=
    isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U).ι
  have : Surjective (f ∣_ U) := by
    constructor
    intro y
    obtain ⟨b, hb⟩ := y.2
    refine ⟨⟨b, ⟨b, rfl⟩⟩, Subtype.ext ?_⟩
    rw [morphismRestrict_base_coe]
    exact hb
  have hwU : p w ∈ g ⁻¹ᵁ U := by
    change g (p w) ∈ Set.range f
    exact ⟨q w, (congrArg (fun e : W ⟶ Y ↦ e w) H.w).symm⟩
  have H' := Scheme.Hom.isPullback_resLE H (US := U)
    (UT := f ⁻¹ᵁ U) (UX := g ⁻¹ᵁ U) le_rfl le_rfl
    (UY := p ⁻¹ᵁ g ⁻¹ᵁ U) (by
      rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage, inf_idem])
  simp only [Scheme.Hom.resLE_eq_morphismRestrict] at H'
  have : IsNoetherian (g ⁻¹ᵁ U).toScheme :=
    { toIsLocallyNoetherian := inferInstance
      toCompactSpace := isCompact_iff_compactSpace.mp
        (TopologicalSpace.NoetherianSpace.isCompact (g ⁻¹ᵁ U : Set A)) }
  have hA' (a : (g ⁻¹ᵁ U).toScheme) :
      IsDomain ((g ⁻¹ᵁ U).toScheme.presheaf.stalk a) := by
    have := hA a.1
    exact ((g ⁻¹ᵁ U).stalkIso a).commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  let w' : (p ⁻¹ᵁ g ⁻¹ᵁ U).toScheme := ⟨w, hwU⟩
  have hw' : w' ∈ genericPoints (p ⁻¹ᵁ g ⁻¹ᵁ U).toScheme :=
    mem_genericPoints_of_isOpenImmersion (p ⁻¹ᵁ g ⁻¹ᵁ U).ι w' hw
  have hp := mem_genericPoints_of_isPullback_flat_domainStalks _ _ _ _ H' hA' w' hw'
  have hp' := mem_genericPoints_of_generalizing (g ⁻¹ᵁ U).ι
    (g ⁻¹ᵁ U).ι.isOpenEmbedding.generalizingMap ((p ∣_ (g ⁻¹ᵁ U)) w') hp
  change ((p ∣_ (g ⁻¹ᵁ U)) w').1 ∈ genericPoints A at hp'
  simpa only [morphismRestrict_base_coe] using hp'

end AlgebraicGeometry.Scheme.Hom
