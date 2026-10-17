/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FiniteBaseChangeDominance
public import Motivic.AlgebraicGeometry.Scheme.NormalStalks

/-!
# Generalization lifting for finite base change over a normal integral scheme

The affine calculation uses the actual tensor-product pullback and the proved
finite-type going-down theorem. The test scheme and its pullback may be
nonreduced or disconnected.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic

/-- A surjective spectrum map into the spectrum of a domain is induced by an
injective ring homomorphism. -/
theorem ringHom_injective_of_spec_surjective
    {R S : Type u} [CommRing R] [CommRing S] [IsDomain R]
    (φ : R →+* S) (hφ : Function.Surjective (PrimeSpectrum.comap φ)) :
    Function.Injective φ := by
  obtain ⟨p, hp⟩ := hφ ⟨⊥, inferInstance⟩
  apply (RingHom.injective_iff_ker_eq_bot φ).mpr
  apply le_bot_iff.mp
  have h : RingHom.ker φ ≤ p.asIdeal.comap φ := Ideal.ker_le_comap φ
  simpa only [PrimeSpectrum.ext_iff] using h.trans_eq (congrArg PrimeSpectrum.asIdeal hp)

/-- The literal affine tensor-product pullback is generalizing after a
finite-type base change of a finite surjective map between integral affine schemes. -/
theorem generalizingMap_pullbackFst_spec
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.FiniteType R A]
    [IsDomain R] [IsDomain B] [IsIntegrallyClosed R] [Module.Finite R B]
    (hf : Function.Surjective (PrimeSpectrum.comap (algebraMap R B))) :
    GeneralizingMap (pullback.fst
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R B)))) := by
  have : FaithfulSMul R B := (faithfulSMul_iff_algebraMap_injective R B).mpr
    (ringHom_injective_of_spec_surjective (algebraMap R B) hf)
  have : Algebra.HasGoingDown A (A ⊗[R] B) :=
    Algebra.HasGoingDown.finiteType_baseChange (R := R) (S := B) (A := A)
  apply (MorphismProperty.cancel_left_of_respectsIso (topologically GeneralizingMap)
    (pullbackSpecIso R A B).inv _).mp
  rw [pullbackSpecIso_inv_fst']
  exact Algebra.HasGoingDown.iff_generalizingMap_primeSpectrumComap.mp inferInstance

/-- The tensor-product calculation transported through the canonical affine
scheme isomorphisms and an actual pullback square. -/
theorem generalizingMap_of_isPullback_affine
    {W A B Y : Scheme.{u}} [IsAffine A] [IsAffine Y]
    (p : W ⟶ A) (q : W ⟶ B) (g : A ⟶ Y) (f : B ⟶ Y)
    (H : IsPullback p q g f) [IsFinite f] [Surjective f]
    [LocallyOfFiniteType g] [IsIntegral B] [IsIntegral Y]
    [IsIntegrallyClosed Γ(Y, ⊤)] : GeneralizingMap p := by
  have : IsAffine B := isAffine_of_isAffineHom f
  let R := Γ(Y, ⊤)
  let S := Γ(A, ⊤)
  let T := Γ(B, ⊤)
  algebraize [g.appTop.hom, f.appTop.hom]
  have : Algebra.FiniteType R S :=
    RingHom.finiteType_algebraMap.mp (HasRingHomProperty.appTop
      @LocallyOfFiniteType g inferInstance)
  have : Module.Finite R T := RingHom.finite_algebraMap.mp f.finite_appTop
  have hf : Function.Surjective (PrimeSpectrum.comap (algebraMap R T)) := by
    intro x
    obtain ⟨b, hb⟩ := f.surjective (Y.isoSpec.inv x)
    refine ⟨B.isoSpec.hom b, ?_⟩
    have h := congrArg (fun e : B ⟶ Spec R ↦ e b) (Scheme.isoSpec_hom_naturality f)
    change (Spec.map f.appTop) (B.isoSpec.hom b) = Y.isoSpec.hom (f b) at h
    rw [hb] at h
    exact h.trans (Scheme.inv_hom_apply Y.isoSpec x)
  have H' : IsPullback (p ≫ A.isoSpec.hom) (q ≫ B.isoSpec.hom)
      (Spec.map g.appTop) (Spec.map f.appTop) :=
    H.of_iso (Iso.refl _) A.isoSpec B.isoSpec Y.isoSpec
      (by simp) (by simp) (Scheme.isoSpec_hom_naturality g).symm
      (Scheme.isoSpec_hom_naturality f).symm
  have hp : topologically GeneralizingMap
      (pullback.fst (Spec.map g.appTop) (Spec.map f.appTop)) :=
    generalizingMap_pullbackFst_spec R S T hf
  change topologically GeneralizingMap p
  rw [← MorphismProperty.cancel_right_of_respectsIso
    (topologically GeneralizingMap) p A.isoSpec.hom]
  rw [← H'.isoPullback_hom_fst]
  exact (MorphismProperty.cancel_left_of_respectsIso
    (topologically GeneralizingMap) H'.isoPullback.hom _).mpr hp

/-- Over an affine integral normal base, generalization lifting holds for
arbitrary locally finite-type test schemes, by their actual affine covers. -/
theorem generalizingMap_of_isPullback_affine_base
    {W A B Y : Scheme.{u}} [IsAffine Y]
    (p : W ⟶ A) (q : W ⟶ B) (g : A ⟶ Y) (f : B ⟶ Y)
    (H : IsPullback p q g f) [IsFinite f] [Surjective f]
    [LocallyOfFiniteType g] [IsIntegral B] [IsIntegral Y]
    [IsIntegrallyClosed Γ(Y, ⊤)] : GeneralizingMap p := by
  change topologically GeneralizingMap p
  rw [IsZariskiLocalAtTarget.iff_of_openCover
    (P := topologically GeneralizingMap) A.affineCover]
  intro i
  exact generalizingMap_of_isPullback_affine
    (pullback.snd p (A.affineCover.f i))
    (pullback.fst p (A.affineCover.f i) ≫ q)
    (A.affineCover.f i ≫ g) f
    ((IsPullback.of_hasPullback p (A.affineCover.f i)).flip.paste_vert H)

/-- Finite surjective maps between integral schemes with integrally closed
base stalks lift generalizations after every locally finite-type base change.
The test scheme and the fiber product need not be reduced or irreducible. -/
theorem generalizingMap_of_isPullback_normal_base
    {W A B Y : Scheme.{u}}
    (p : W ⟶ A) (q : W ⟶ B) (g : A ⟶ Y) (f : B ⟶ Y)
    (H : IsPullback p q g f) [IsFinite f] [Surjective f]
    [LocallyOfFiniteType g] [IsIntegral B] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    GeneralizingMap p := by
  change topologically GeneralizingMap p
  apply IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun U : Y.affineOpens ↦ g ⁻¹ᵁ U.1)
    (by rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top]; rfl)
  intro U
  by_cases hU : Nonempty U.1
  · let := hU
    have : IsIntegral U.1.toScheme := isIntegral_of_isOpenImmersion U.1.ι
    have : Nonempty (f ⁻¹ᵁ U.1) := by
      obtain ⟨y, hy⟩ := hU
      obtain ⟨b, hb⟩ := f.surjective y
      exact ⟨⟨b, by simpa only [Scheme.Hom.mem_preimage, hb] using hy⟩⟩
    have : IsIntegral (f ⁻¹ᵁ U.1).toScheme :=
      isIntegral_of_isOpenImmersion (f ⁻¹ᵁ U.1).ι
    have : IsIntegrallyClosed Γ(U.1.toScheme, ⊤) :=
      isIntegrallyClosed_sections_of_stalks
        (isIntegrallyClosed_stalk_open_of_stalks hY U.1) (isAffineOpen_top _)
    have H' := Scheme.Hom.isPullback_resLE H (US := U.1)
      (UT := f ⁻¹ᵁ U.1) (UX := g ⁻¹ᵁ U.1) le_rfl le_rfl
      (UY := p ⁻¹ᵁ g ⁻¹ᵁ U.1) (by
        rw [← Scheme.Hom.comp_preimage, H.w, Scheme.Hom.comp_preimage, inf_idem])
    have : Surjective (f ∣_ U.1) :=
      IsZariskiLocalAtTarget.restrict (P := @Surjective) inferInstance U.1
    simp only [Scheme.Hom.resLE_eq_morphismRestrict] at H'
    exact generalizingMap_of_isPullback_affine_base _ _ _ _ H'
  · intro x y hxy
    exact (hU ⟨⟨g (p x.1), x.2⟩⟩).elim

/-- The actual first pullback projection of a finite surjective map between
integral schemes over a normal base is generalizing for a finite-type test map. -/
theorem generalizingMap_pullbackFst_normal_base
    {A B Y : Scheme.{u}} (g : A ⟶ Y) (f : B ⟶ Y)
    [IsFinite f] [Surjective f] [LocallyOfFiniteType g]
    [IsIntegral B] [IsIntegral Y]
    (hY : ∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)) :
    GeneralizingMap (pullback.fst g f) :=
  generalizingMap_of_isPullback_normal_base _ _ g f (.of_hasPullback g f) hY

end Motivic
