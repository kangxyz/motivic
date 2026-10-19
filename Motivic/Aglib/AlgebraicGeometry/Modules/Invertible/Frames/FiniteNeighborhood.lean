/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.Semilocal
public import Motivic.Aglib.RingTheory.Spectrum.Prime.FiniteSemilocal
public import Mathlib.RingTheory.Localization.Free

/-!
# Spreading affine line-bundle trivializations to principal neighborhoods

A unit trivialization after localization of an actual finitely presented
quasicoherent sheaf descends to an actual unit isomorphism on a principal open.
The finite-presentation theorem lifts a singleton basis and its inverse
identities; the affine comparisons return the resulting isomorphism to the
original sheaf on the original scheme.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Module
open scoped TensorProduct ModuleCat.Algebra

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- An actual unit isomorphism of an associated sheaf supplies a singleton
basis of the original module over any commutative ring, including the zero ring. -/
def basisOfTildeUnitIso (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    (e : tilde M ≅ SheafOfModules.unit (Spec R).ringCatSheaf) :
    Basis PUnit.{u + 1} R M := by
  let e' : M ≅ ModuleCat.of R R := tilde.isoTop M ≪≫
    moduleSpecΓFunctor.mapIso e ≪≫ (tilde.isoTop (ModuleCat.of R R)).symm
  exact (Basis.singleton PUnit R).map e'.toLinearEquiv.symm

set_option backward.isDefEq.respectTransparency false in
/-- A trivialization after any submonoid localization of a finitely presented
quasicoherent sheaf spreads to a genuine principal open of the original affine
scheme. Finite presentation is used to descend a basis and its inverse. -/
theorem exists_principal_unitIso_of_localization (R : CommRingCat.{u})
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.FinitePresentation R (moduleSpecΓFunctor.obj M)]
    (S : Submonoid R)
    (e : (Scheme.Modules.pullback
        (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S))))).obj M ≅
      SheafOfModules.unit (Spec (.of (Localization S))).ringCatSheaf) :
    ∃ r : R, r ∈ S ∧
      Nonempty (M.restrict (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)) ≅
        SheafOfModules.unit
          (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)).ringCatSheaf) := by
  let N := moduleSpecΓFunctor.obj M
  let φ : R ⟶ CommRingCat.of (Localization S) :=
    CommRingCat.ofHom (algebraMap R (Localization S))
  let c : (Scheme.Modules.pullback (Spec.map φ)).obj M ≅
      tilde (ModuleCat.of (Localization S) (Localization S ⊗[R] N)) :=
    (Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ).symm ≪≫
      (tildePullbackIso φ).app N ≪≫
        (tilde.functor (.of (Localization S))).mapIso
          (ModuleCat.extendScalarsAlgebraIso R (Localization S) N)
  let b := basisOfTildeUnitIso (.of (Localization S))
    (ModuleCat.of (Localization S) (Localization S ⊗[R] N)) (c.symm ≪≫ e)
  obtain ⟨r, hr, b', _⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    S (TensorProduct.mk R (Localization S) N 1) (Localization S) b
  let d : LocalizedModule.Away r N ≃ₗ[Localization.Away r] Localization.Away r :=
    b'.repr ≪≫ₗ Finsupp.uniqueLinearEquiv _ _ PUnit.unit
  let d' : QuasiCoherent.restrictionGlobalSections R r N ≃ₗ[Localization.Away r]
      Localization.Away r :=
    ((IsLocalizedModule.linearEquiv (Submonoid.powers r)
      (LocalizedModule.mkLinearMap (Submonoid.powers r) N)
      (QuasiCoherent.toRestrictionGlobalSections R r N)).extendScalarsOfIsLocalization
        (Submonoid.powers r) (Localization.Away r)).symm ≪≫ₗ d
  let j := QuasiCoherent.principalOpen R r
  let c' : M.restrict j ≅ SheafOfModules.unit (Spec (.of (Localization.Away r))).ringCatSheaf :=
    (Scheme.Modules.restrictFunctor j).mapIso (asIso M.fromTildeΓ).symm ≪≫
      (asIso ((tilde N).restrict j).fromTildeΓ).symm ≪≫
        (tilde.functor (.of (Localization.Away r))).mapIso
          d'.toModuleIso ≪≫
            tildeSelf
  let a := (basicOpenIsoSpecAway r).hom
  let c'' : Scheme.Modules.restrictFunctor j ⋙ Scheme.Modules.restrictFunctor a ≅
      Scheme.Modules.restrictFunctor
        (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r)) :=
    (Scheme.Modules.restrictFunctorComp a j).symm ≪≫
      Scheme.Modules.restrictFunctorCongr (basicOpenIsoSpecAway_hom_SpecMap r)
  exact ⟨r, hr, ⟨(c''.app M).symm ≪≫
    (Scheme.Modules.restrictFunctor a).mapIso c' ≪≫ Scheme.Modules.restrictUnitIso a⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- A semilocal localization gives a principal-open unit trivialization of
any actual line bundle. The element defining the open belongs to the original
multiplicative set. -/
theorem exists_principal_unitIso_of_semilocalLocalization (R : CommRingCat.{u})
    (S : Submonoid R) [Finite (MaximalSpectrum (Localization S))]
    (L : LineBundle (Spec R)) :
    ∃ r : R, r ∈ S ∧
      Nonempty ((Scheme.Modules.restrictFunctor
        (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj L.val ≅
        SheafOfModules.unit
          (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)).ringCatSheaf) := by
  have : IsFiniteLocallyFree (Spec R) L.val :=
    finiteLocallyFree_of_isLocallyRankOne L.val L.property
  have : L.val.IsLocallyFree := lineBundle_isLocallyFree (Spec R) L
  have : Module.FinitePresentation R (moduleSpecΓFunctor.obj L.val) :=
    finitePresentation_globalSections_of_finiteLocallyFree R L.val
  exact exists_principal_unitIso_of_localization R L.val S
    (semilocalLineBundle_trivial (.of (Localization S))
      (pullbackLineBundle (Spec.map (CommRingCat.ofHom (algebraMap R (Localization S)))) L)).some

set_option backward.isDefEq.respectTransparency false in
/-- An actual line bundle on an affine scheme has a unit trivialization on
one principal open containing any prescribed finite set of points. There is
no Noetherian, reducedness, closed-point, or nonempty-set hypothesis. -/
theorem exists_principal_unitIso_around_finset (R : CommRingCat.{u})
    (L : LineBundle (Spec R)) (s : Finset (PrimeSpectrum R)) :
    ∃ r : R, (∀ p ∈ s, p ∈ PrimeSpectrum.basicOpen r) ∧
      Nonempty ((Scheme.Modules.restrictFunctor
        (Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen r))).obj L.val ≅
        SheafOfModules.unit
          (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen r)).ringCatSheaf) := by
  have := Localization.finite_maximalSpectrum_iInf_primeCompl s
  obtain ⟨r, hr, he⟩ := exists_principal_unitIso_of_semilocalLocalization R
    (⨅ p : s, p.1.asIdeal.primeCompl) L
  exact ⟨r, fun p hp ↦ Submonoid.mem_iInf.mp hr ⟨p, hp⟩, he⟩

set_option backward.isDefEq.respectTransparency false in
/-- An actual line bundle on any affine scheme is trivial on an open containing
any finite set of points, transported along the canonical affine comparison. -/
theorem exists_open_unitIso_around_finite (X : Scheme.{u}) [IsAffine X]
    (L : LineBundle X) (s : Set X) (hs : s.Finite) :
    ∃ U : X.Opens, s ⊆ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj L.val ≅
        SheafOfModules.unit U.toScheme.ringCatSheaf) := by
  classical
  let e := X.isoSpec
  let L' := pullbackLineBundle e.inv L
  let t := (hs.image e.hom).toFinset
  obtain ⟨r, hr, ⟨d⟩⟩ := exists_principal_unitIso_around_finset Γ(X, ⊤) L' t
  let V : (Spec Γ(X, ⊤)).Opens := PrimeSpectrum.basicOpen r
  let U := e.hom ⁻¹ᵁ V
  let c : L.val ≅ (Scheme.Modules.pullback e.hom).obj L'.val :=
    ((Scheme.Modules.pullbackId X).app L.val).symm ≪≫
      ((Scheme.Modules.pullbackCongr e.hom_inv_id).app L.val).symm ≪≫
        ((Scheme.Modules.pullbackComp e.hom e.inv).app L.val).symm
  refine ⟨U, ?_, ⟨?_⟩⟩
  · intro x hx
    exact hr (e.hom x) ((hs.image e.hom).mem_toFinset.mpr ⟨x, hx, rfl⟩)
  · exact (Scheme.Modules.restrictFunctor U.ι).mapIso c ≪≫
      (Scheme.Modules.pullbackRestrictIso e.hom V).app L'.val ≪≫
        (Scheme.Modules.pullback (e.hom ∣_ V)).mapIso d ≪≫
          pullbackUnitIso (e.hom ∣_ V)

end AlgebraicGeometry.Scheme.Modules.Invertible
