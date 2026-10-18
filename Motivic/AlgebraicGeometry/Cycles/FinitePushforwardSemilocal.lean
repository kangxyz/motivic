/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Cycles.FinitePushforwardKoszul
public import Mathlib.RingTheory.LocalProperties.Semilocal

/-!
# Whole finite-algebra modules detected on actual source stalks

For a genuinely given quasi-coherent module sheaf, the entire finite affine
inverse image supplies one coordinate module and its localization at the target
point. Its maximal localizations are identified with the original source
stalks through the actual structure-stalk ring maps. Finite generation and
vanishing can therefore be checked on the whole original source fiber.

These are module finiteness and zero-detection statements. Finite length,
remaining-Koszul support and construction of the first-stage Tor sheaf remain
separate obligations.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace Motivic.FiniteSchemeEuler

open FiniteAffineChart ModuleStalk

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
  {U : Y.Opens} (hU : IsAffineOpen U) (p : Spec Γ(Y, U))

/-- The coordinate algebra is the literal section map of the original finite morphism. -/
local instance semilocalCoordinateAlgebra : Algebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) :=
  (f.app U).hom.toAlgebra

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The original module of sections on the entire finite affine inverse image. -/
abbrev originalCoordinateModule (N : X.Modules) :=
  moduleSpecΓFunctor.obj
    ((Scheme.Modules.restrictFunctor (sourceChart f hU)).obj N)

/-- The whole localized coefficient retains the target infinitesimals and every source branch. -/
abbrev originalWholeLocalizedModule (N : X.Modules) :=
  (ModuleCat.extendScalars
    (algebraMap Γ(X, f ⁻¹ᵁ U) (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p))).obj
      (originalCoordinateModule f hU N)

/-- The original structure-stalk module with its canonical scalar action. -/
abbrev originalSourceStalkModule (N : X.Modules) (x : X) := (functor x).obj N

variable (N : X.Modules) [N.IsQuasicoherent]

/-- The actual tilde-Gamma counit and open stalk map identify the original source module. -/
def wholeChartModuleStalkIso (x : Spec Γ(X, f ⁻¹ᵁ U)) :
    (tilde.functor Γ(X, f ⁻¹ᵁ U) ⋙ functor x).obj (originalCoordinateModule f hU N) ≅
      (ModuleCat.restrictScalars (inv ((sourceChart f hU).stalkMap x)).hom).obj
        (originalSourceStalkModule N (sourceChart f hU x)) :=
  (functor x).mapIso
      (asIso (((Scheme.Modules.restrictFunctor (sourceChart f hU)).obj N).fromTildeΓ)) ≪≫
    (openRestrictionIso (sourceChart f hU) x).app N

variable (q : MaximalSpectrum (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p))

/-- Use canonical commutative-localization structures also for variable maximal ideals. -/
local instance canonicalSemilocalLocalizationRing {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Ring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toRing

/-- Finiteness and tensor products use the same canonical localization semiring. -/
local instance canonicalSemilocalLocalizationSemiring {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] : Semiring (Localization.AtPrime P) :=
  (inferInstance : CommRing (Localization.AtPrime P)).toSemiring

/-- Literal scalar extension of the whole coordinate module to one maximal localization. -/
abbrev originalWholeMaximalModule : ModuleCat.{u} (Localization.AtPrime q.asIdeal) :=
  (ModuleCat.extendScalars (algebraMap
    (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p)
    (Localization.AtPrime q.asIdeal))).obj (originalWholeLocalizedModule f hU p N)

/-- The actual maximal localization of the whole module is the original source stalk,
restricted along the previously constructed literal structure-stalk ring isomorphism. -/
def originalWholeModuleSourceIso :
    originalWholeMaximalModule f hU p N q ≅
      (ModuleCat.restrictScalars (originalSourceLocalizationIso f hU p q).hom.hom).obj
        (originalSourceStalkModule N (wholeAlgebraFiberEquiv f hU p q).1) := by
  have := coordinateFinite f hU
  exact (FiniteFiber.localCoefficientStalkIso Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p q).app
      (originalCoordinateModule f hU N) ≪≫
    (ModuleCat.restrictScalars
      (FiniteFiber.sourceSchemeStalkIso Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p q).hom.hom).mapIso
        (wholeChartModuleStalkIso f hU N (wholeAlgebraSourcePoint f hU p q).1) ≪≫
    (ModuleCat.restrictScalarsComp
      (FiniteFiber.sourceSchemeStalkIso Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p q).hom.hom
      (inv ((sourceChart f hU).stalkMap (wholeAlgebraSourcePoint f hU p q).1)).hom).symm.app
        (originalSourceStalkModule N (wholeAlgebraFiberEquiv f hU p q).1)

private theorem finite_restrict_ringEquiv {R T : Type u} [CommRing R] [CommRing T]
    (e : R ≃+* T) (M : ModuleCat.{u} T) (hM : Module.Finite T M) :
    Module.Finite R ((ModuleCat.restrictScalars e.toRingHom).obj M) := by
  have := hM
  let g : M →ₛₗ[e.symm.toRingHom] (ModuleCat.restrictScalars e.toRingHom).obj M :=
    { toFun := id
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro t m
        change t • m = e (e.symm t) • m
        rw [e.apply_symm_apply] }
  exact Module.Finite.of_surjective g Function.surjective_id

/-- Finite generation of an actual source stalk gives finite generation of the
corresponding genuine maximal localization of the whole coefficient module. -/
theorem originalWholeModuleLocalized_finite
    (hN : Module.Finite (X.presheaf.stalk (wholeAlgebraFiberEquiv f hU p q).1)
      (originalSourceStalkModule N (wholeAlgebraFiberEquiv f hU p q).1)) :
    Module.Finite (Localization.AtPrime q.asIdeal) (originalWholeMaximalModule f hU p N q) := by
  have := hN
  have hres : Module.Finite (Localization.AtPrime q.asIdeal)
      ((ModuleCat.restrictScalars (originalSourceLocalizationIso f hU p q).hom.hom).obj
        (originalSourceStalkModule N (wholeAlgebraFiberEquiv f hU p q).1)) :=
    finite_restrict_ringEquiv (originalSourceLocalizationIso f hU p q).commRingCatIsoToRingEquiv
      (originalSourceStalkModule N (wholeAlgebraFiberEquiv f hU p q).1) hN
  have := hres
  exact Module.Finite.of_surjective
    (originalWholeModuleSourceIso f hU p N q).symm.toLinearEquiv.toLinearMap
    (originalWholeModuleSourceIso f hU p N q).symm.toLinearEquiv.surjective

/-- Finitely generated original source stalks on the full source fiber imply finite
generation over the whole localized finite algebra. No Noetherianity is required. -/
theorem originalWholeModule_finite
    (hN : ∀ x : {x : X // f x = hU.fromSpec p},
      Module.Finite (X.presheaf.stalk x.1) (originalSourceStalkModule N x.1)) :
    Module.Finite (FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p)
      (originalWholeLocalizedModule f hU p N) := by
  have := coordinateFinite f hU
  let S := FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p
  let M := originalWholeLocalizedModule f hU p N
  have : Finite (MaximalSpectrum S) :=
    Module.finiteAlgebra_maximalSpectrum_finite (Localization.AtPrime p.asIdeal) S
  apply Module.Finite.of_isLocalized_maximal M
    (fun P _ => Localization.AtPrime P)
    (fun P _ => Localization.AtPrime P ⊗[S] M)
    (fun P _ => TensorProduct.mk S (Localization.AtPrime P) M 1)
  intro P hP
  have := originalWholeModuleLocalized_finite f hU p N ⟨P, hP⟩
    (hN (wholeAlgebraFiberEquiv f hU p ⟨P, hP⟩))
  let e := LengthEuler.finiteAlgebraExtendScalarsEquiv S (Localization.AtPrime P) M
  exact Module.Finite.of_surjective e.toLinearMap e.surjective

/-- Vanishing of all original source stalks detects vanishing of the entire
localized coefficient, without a product decomposition or finiteness premise. -/
theorem originalWholeModule_subsingleton
    (hN : ∀ x : {x : X // f x = hU.fromSpec p},
      Subsingleton (originalSourceStalkModule N x.1)) :
    Subsingleton (originalWholeLocalizedModule f hU p N) := by
  let S := FiniteFiber.localAlgebra Γ(Y, U) Γ(X, f ⁻¹ᵁ U) p
  let M := originalWholeLocalizedModule f hU p N
  apply Module.subsingleton_of_localization_maximal
    (fun P _ => Localization.AtPrime P ⊗[S] M)
    (fun P _ => TensorProduct.mk S (Localization.AtPrime P) M 1)
  intro P hP
  have hz :=
    (originalWholeModuleSourceIso f hU p N ⟨P, hP⟩).toLinearEquiv.toEquiv.subsingleton_congr.mpr
    (hN (wholeAlgebraFiberEquiv f hU p ⟨P, hP⟩))
  let e := LengthEuler.finiteAlgebraExtendScalarsEquiv S (Localization.AtPrime P) M
  exact e.toEquiv.subsingleton_congr.mp hz

end Motivic.FiniteSchemeEuler
