/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.Balanced
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Quotient-support actions on actual categorical Tor

Both coefficient annihilators annihilate the actual categorical Tor module.
Consequently Tor of two ideal quotients carries an action by their sum quotient,
without radicality, regularity, or flatness assumptions. Scalar lifting makes
ambient-linear maps between annihilated modules linear over the quotient.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

namespace ModuleCat.TorComparison

variable {R : Type u} [CommRing R]

/-- The coefficient annihilator annihilates every tensor product. -/
theorem annihilator_le_tensorLeft (M N : ModuleCat.{u} R) :
    Module.annihilator R M ≤ Module.annihilator R (M ⊗[R] N) := by
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul m n =>
    change r • (m ⊗ₜ[R] n) = 0
    rw [TensorProduct.smul_tmul', Module.mem_annihilator.mp hr m,
      TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, hx, hy, zero_add]

/-- The annihilator of a chain term annihilates its homology in that degree. -/
theorem annihilator_le_homology (C : ChainComplex (ModuleCat.{u} R) ℕ) (n : ℕ) :
    Module.annihilator R (C.X n) ≤ Module.annihilator R (C.homology n) :=
  ((C.iCycles n).hom.annihilator_le_of_injective
    ((ModuleCat.mono_iff_injective _).mp inferInstance)).trans
      ((C.homologyπ n).hom.annihilator_le_of_surjective
        ((ModuleCat.epi_iff_surjective _).mp inferInstance))

/-- The first coefficient annihilator kills actual categorical Tor in every degree. -/
theorem annihilator_left_le_tor (M N : ModuleCat.{u} R) (n : ℕ) :
    Module.annihilator R M ≤ Module.annihilator R (((Tor (ModuleCat R) n).obj M).obj N) := by
  let P := projectiveResolution N
  let C := (((tensoringLeft (ModuleCat R)).obj M).mapHomologicalComplex _).obj P.complex
  exact ((annihilator_le_tensorLeft M (P.complex.X n)).trans
    (annihilator_le_homology C n)).trans
    (LinearMap.annihilator_le_of_injective
      (P.isoLeftDerivedObj ((tensoringLeft (ModuleCat R)).obj M) n).hom.hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance))

/-- Balance transports the second coefficient annihilator to actual Tor. -/
theorem annihilator_right_le_tor (M N : ModuleCat.{u} R) (n : ℕ) :
    Module.annihilator R N ≤ Module.annihilator R (((Tor (ModuleCat R) n).obj M).obj N) :=
  (annihilator_left_le_tor N M n).trans
    ((torBalanceIso M N n).hom.hom.annihilator_le_of_injective
      ((ModuleCat.mono_iff_injective _).mp inferInstance))

/-- The actual sum ideal, rather than its radical, annihilates quotient Tor. -/
theorem quotient_support_le_annihilator (J K : Ideal R) (n : ℕ) :
    J ⊔ K ≤ Module.annihilator R
      (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj
        (ModuleCat.of R (R ⧸ J))) := by
  apply sup_le
  · simpa only [Ideal.annihilator_quotient] using
      annihilator_right_le_tor (ModuleCat.of R (R ⧸ K)) (ModuleCat.of R (R ⧸ J)) n
  · simpa only [Ideal.annihilator_quotient] using
      annihilator_left_le_tor (ModuleCat.of R (R ⧸ K)) (ModuleCat.of R (R ⧸ J)) n

variable (I : Ideal R) (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M)

/-- The action on an annihilated module factors through its literal ideal quotient. -/
@[instance_reducible] def quotientModuleAction : Module (R ⧸ I) M :=
  Module.compHom M (Ideal.Quotient.lift I (Module.toAddMonoidEnd R M) hM)

/-- A lifted scalar acts by exactly its original ambient action. -/
@[simp] theorem quotientModuleAction_mk_smul (r : R) (m : M) :
    letI := quotientModuleAction I M hM
    (Ideal.Quotient.mk I r) • m = r • m := rfl

/-- The same actual additive group equipped with the constructed quotient action. -/
def quotientModule : ModuleCat.{u} (R ⧸ I) :=
  letI := quotientModuleAction I M hM
  ModuleCat.of (R ⧸ I) M

/-- Scalar restriction recovers the exact original ambient module. -/
def quotientModuleRestrictIso : M ≅
    (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (quotientModule I M hM) :=
  by
    let N : ModuleCat.{u} R :=
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (quotientModule I M hM)
    let e : M ≃ₗ[R] N :=
      { toFun := fun x => x
        invFun := fun x => x
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact e.toModuleIso

variable {M} {N : ModuleCat.{u} R} (hN : I ≤ Module.annihilator R N)

/-- Surjectivity of the quotient map upgrades every ambient-linear map. -/
def quotientLinearMap (f : M ⟶ N) : quotientModule I M hM ⟶ quotientModule I N hN :=
  letI := quotientModuleAction I M hM
  letI := quotientModuleAction I N hN
  ModuleCat.ofHom
    { toFun := f
      map_add' := f.hom.map_add
      map_smul' := by
        intro s x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        exact f.hom.map_smul r x }

/-- Quotient-linear lifting leaves the underlying function unchanged. -/
@[simp] theorem quotientLinearMap_apply (f : M ⟶ N) (x : M) :
    quotientLinearMap I hM hN f x = f x := rfl

/-- Quotient lifting preserves identities. -/
@[simp] theorem quotientLinearMap_id : quotientLinearMap I hM hM (𝟙 M) = 𝟙 _ := rfl

/-- Quotient lifting preserves composition. -/
@[simp] theorem quotientLinearMap_comp {P : ModuleCat.{u} R}
    (hP : I ≤ Module.annihilator R P) (f : M ⟶ N) (g : N ⟶ P) :
    quotientLinearMap I hM hP (f ≫ g) =
      quotientLinearMap I hM hN f ≫ quotientLinearMap I hN hP g := rfl

/-- An actual ambient-linear isomorphism descends to the quotient scalar action. -/
def quotientLinearIso (e : M ≅ N) : quotientModule I M hM ≅ quotientModule I N hN where
  hom := quotientLinearMap I hM hN e.hom
  inv := quotientLinearMap I hN hM e.inv
  hom_inv_id := by rw [← quotientLinearMap_comp, e.hom_inv_id, quotientLinearMap_id]
  inv_hom_id := by rw [← quotientLinearMap_comp, e.inv_hom_id, quotientLinearMap_id]

/-- Canonical quotient-supported Tor, with coefficient-first/source-second convention. -/
def torSupportModule (J K : Ideal R) (n : ℕ) : ModuleCat.{u} (R ⧸ (J ⊔ K)) :=
  quotientModule (J ⊔ K)
    (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj (ModuleCat.of R (R ⧸ J)))
    (quotient_support_le_annihilator J K n)

/-- Restriction of the constructed support module is the original categorical Tor. -/
def torSupportModuleRestrictIso (J K : Ideal R) (n : ℕ) :
    (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj (ModuleCat.of R (R ⧸ J))) ≅
      (ModuleCat.restrictScalars (Ideal.Quotient.mk (J ⊔ K))).obj (torSupportModule J K n) :=
  quotientModuleRestrictIso _ _ _

end ModuleCat.TorComparison
