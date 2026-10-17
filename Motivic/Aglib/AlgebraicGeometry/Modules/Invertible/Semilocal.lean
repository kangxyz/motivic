/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Field
public import Aglib.AlgebraicGeometry.Modules.LocallyFree.Affine.Projective
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.Algebra.Category.ModuleCat.BaseChange
public import Mathlib.RingTheory.PicardGroup

/-!
# Actual trivializations on semilocal affine schemes

Mathlib's semilocal Picard theorem supplies a unit trivialization of the
associated sheaf of an algebraically invertible module. For an arbitrary
locally rank-one sheaf, the affine section and pullback comparisons identify
its closed fibres with the actual residue tensor products. Mathlib's existing
semilocal basis theorem, which also proves semilocal Picard triviality, then
supplies the global rank-one basis. No Noetherian or reducedness assumption
is imposed.

The algebraic source is Stacks Project, Tag 02M9. This is an affine semilocal
result; spreading a trivialization to a neighborhood of a finite set on a
larger scheme is a separate step.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Trivial Picard group gives an actual unit isomorphism for the associated
sheaf, rather than merely equality of its isomorphism class. -/
def tildeUnitIsoOfSubsingletonPic (R : CommRingCat.{u}) (M : ModuleCat.{u} R)
    [Module.Invertible R M] [Subsingleton (CommRing.Pic R)] :
    tilde M ≅ SheafOfModules.unit (Spec R).ringCatSheaf :=
  (tilde.functor R).mapIso
    ((CommRing.Pic.mk_eq_one_iff.mp
      (Subsingleton.elim (CommRing.Pic.mk R M) 1)).some.toModuleIso) ≪≫ tildeSelf

/-- Rank one gives finite local bases on the same actual sheaf. -/
theorem finiteLocallyFree_of_isLocallyRankOne {X : Scheme.{u}} (M : X.Modules)
    (hM : IsLocallyRankOne X M) : IsFiniteLocallyFree X M := by
  obtain ⟨q, hq, hr⟩ := hM
  refine ⟨q, hq, ⟨fun i ↦ ⟨?_⟩⟩⟩
  exact Finite.of_equiv PUnit (hr i).some.symm

/-- An affine line bundle has one-dimensional actual scalar-extension fibres.
The scalar extension is over the original ring, not over a replacement model. -/
theorem finrank_baseChange_globalSections_eq_one (R : CommRingCat.{u})
    (M : (Spec R).Modules) (hM : IsLocallyRankOne (Spec R) M)
    (K : Type u) [Field K] [Algebra R K] :
    Module.finrank K (K ⊗[R] (moduleSpecΓFunctor.obj M)) = 1 := by
  have : IsFiniteLocallyFree (Spec R) M := finiteLocallyFree_of_isLocallyRankOne M hM
  let N := moduleSpecΓFunctor.obj M
  let φ : R ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap R K)
  let e : (Scheme.Modules.pullback (Spec.map φ)).obj M ≅
      tilde (ModuleCat.of K (K ⊗[R] N)) :=
    (Scheme.Modules.pullback (Spec.map φ)).mapIso (asIso M.fromTildeΓ).symm ≪≫
      (tildePullbackIso φ).app N ≪≫
        (tilde.functor (.of K)).mapIso (ModuleCat.extendScalarsAlgebraIso R K N)
  have h := isLocallyRankOne_of_iso _ e (pullback_locallyRankOne (Spec.map φ) M hM)
  let b := basisOfTildeRankOne K (ModuleCat.of K (K ⊗[R] N)) h
  simpa using Module.finrank_eq_card_basis b

set_option backward.isDefEq.respectTransparency false in
/-- Every actual line bundle on a semilocal affine scheme has a unit
trivialization. This reuses the same semilocal basis theorem as Mathlib's
Picard-group instance and descends through the original affine counit. -/
theorem semilocalLineBundle_trivial (R : CommRingCat.{u}) [Finite (MaximalSpectrum R)]
    (L : LineBundle (Spec R)) :
    Nonempty (L.val ≅ SheafOfModules.unit (Spec R).ringCatSheaf) := by
  have : IsFiniteLocallyFree (Spec R) L.val :=
    finiteLocallyFree_of_isLocallyRankOne L.val L.property
  have : L.val.IsLocallyFree := lineBundle_isLocallyFree (Spec R) L
  let N := moduleSpecΓFunctor.obj L.val
  have : Module.Finite R N := finite_globalSections_of_finiteLocallyFree R L.val
  have : Module.Projective R N := projective_globalSections_of_finiteLocallyFree R L.val
  obtain ⟨b⟩ := Module.nonempty_basis_of_flat_of_finrank_eq R N 1 (fun P ↦ by
    let := Ideal.Quotient.field P.asIdeal
    exact finrank_baseChange_globalSections_eq_one R L.val L.property (R ⧸ P.asIdeal))
  let e : N ≃ₗ[R] R := b.repr ≪≫ₗ Finsupp.uniqueLinearEquiv R R (0 : Fin 1)
  exact ⟨(asIso (Scheme.Modules.fromTildeΓ (R := R) L.val)).symm ≪≫
    (tilde.functor R).mapIso e.toModuleIso ≪≫ tildeSelf⟩

end AlgebraicGeometry.Scheme.Modules.Invertible
