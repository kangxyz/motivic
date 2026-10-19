/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.QuotientScalarExtensionCoordinates

/-!
# Literal quotient coefficients after scalar extension

Extension of an actual ideal quotient is identified with the actual quotient
by its image ideal. This attaches the canonical flat Tor comparison to literal
target-ring quotient coefficients, rather than leaving extended coefficients
as an unidentified input.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace ModuleCat.TorComparison

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Actual scalar extension uses the usual tensor module with the given algebra
structure; the regular-module comparison explicitly checks the scalar tower. -/
def extendScalarsTensorIso (f : R →+* S) (M : ModuleCat.{u} R) :
    letI := f.toAlgebra
    (ModuleCat.extendScalars f).obj M ≅ ModuleCat.of S (S ⊗[R] M) := by
  letI := f.toAlgebra
  let A := (ModuleCat.restrictScalars f).obj (ModuleCat.of S S)
  letI : IsScalarTower R S A := ⟨fun r s t => by
    change (r • s) • t = f r • (s • t)
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  let e : S ≃ₗ[S] A := LinearEquiv.refl _ _
  exact (TensorProduct.AlgebraTensorModule.congr e (LinearEquiv.refl R M)).symm.toModuleIso

/-- Extension of an actual ideal quotient is the literal quotient by the image ideal. -/
def extendedIdealQuotientIso (f : R →+* S) (I : Ideal R) :
    (ModuleCat.extendScalars f).obj (ModuleCat.of R (R ⧸ I)) ≅
      ModuleCat.of S (S ⧸ I.map f) := by
  letI := f.toAlgebra
  exact extendScalarsTensorIso f (ModuleCat.of R (R ⧸ I)) ≪≫
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm.toLinearEquiv.toModuleIso

/-- The actual quotient-coefficient comparison keeps pure tensor representatives. -/
@[simp] theorem extendedIdealQuotientIso_hom_tmul (f : R →+* S) (I : Ideal R)
    (s : S) (r : R) :
    (extendedIdealQuotientIso f I).hom (s ⊗ₜ[R,f] Ideal.Quotient.mk I r) =
      Ideal.Quotient.mk (I.map f) (s * f r) := by
  let := f.toAlgebra
  change (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).symm
    (s ⊗ₜ[R] Ideal.Quotient.mk I r) = _
  rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul]
  simp only [Algebra.smul_def, mul_comm]
  rfl

/-- Functoriality of actual Tor replaces both scalar-extended quotient coefficients
by their literal target-ring quotients, in coefficient-first convention. -/
def extendedQuotientsTorIso (f : R →+* S) (J K : Ideal R) (n : ℕ) :
    (((Tor (ModuleCat S) n).obj
      ((ModuleCat.extendScalars f).obj (ModuleCat.of R (R ⧸ K)))).obj
      ((ModuleCat.extendScalars f).obj (ModuleCat.of R (R ⧸ J)))) ≅
    (((Tor (ModuleCat S) n).obj (ModuleCat.of S (S ⧸ K.map f))).obj
      (ModuleCat.of S (S ⧸ J.map f))) :=
  ((Tor (ModuleCat S) n).mapIso (extendedIdealQuotientIso f K)).app _ ≪≫
    ((Tor (ModuleCat S) n).obj (ModuleCat.of S (S ⧸ K.map f))).mapIso
      (extendedIdealQuotientIso f J)

/-- The image of the original support ideal annihilates Tor of the literal target quotients. -/
theorem extendedQuotientsTor_support (f : R →+* S) (J K : Ideal R) (n : ℕ) :
    (J ⊔ K).map f ≤ Module.annihilator S
      (((Tor (ModuleCat S) n).obj (ModuleCat.of S (S ⧸ K.map f))).obj
        (ModuleCat.of S (S ⧸ J.map f))) := by
  simpa only [Ideal.map_sup] using quotient_support_le_annihilator (J.map f) (K.map f) n

/-- Canonical flat Tor restriction with actual support scalar extension and literal
quotient coefficients at the target. -/
def flatBaseChangeTorLiteralQuotientIso (f : R →+* S) (hf : f.Flat)
    (J K : Ideal R) (n : ℕ) :
    (ModuleCat.extendScalars (supportQuotientMap f (J ⊔ K))).obj (torSupportModule J K n) ≅
      quotientModule ((J ⊔ K).map f)
        (((Tor (ModuleCat S) n).obj (ModuleCat.of S (S ⧸ K.map f))).obj
          (ModuleCat.of S (S ⧸ J.map f)))
        (extendedQuotientsTor_support f J K n) :=
  quotientScalarExtensionIso f (J ⊔ K) _ (quotient_support_le_annihilator J K n) ≪≫
    flatBaseChangeTorQuotientIso f hf J K n ≪≫
      quotientLinearIso _ _ _ (extendedQuotientsTorIso f J K n)

/-- The actual support ring map with image support written as the sum of image ideals. -/
def supportQuotientMapSup (f : R →+* S) (J K : Ideal R) :
    (R ⧸ (J ⊔ K)) →+* (S ⧸ (J.map f ⊔ K.map f)) :=
  Ideal.quotientMap _ f (by simpa only [← Ideal.map_sup] using Ideal.le_comap_map)

/-- Literal canonical support-module restriction along a flat ambient ring map. -/
def torSupportBaseChangeIso (f : R →+* S) (hf : f.Flat) (J K : Ideal R) (n : ℕ) :
    (ModuleCat.extendScalars (supportQuotientMapSup f J K)).obj (torSupportModule J K n) ≅
      torSupportModule (J.map f) (K.map f) n := by
  have aux (L : Ideal S) (hL : (J ⊔ K).map f = L) :
      (ModuleCat.extendScalars (Ideal.quotientMap L f
        (by rw [← hL]; exact Ideal.le_comap_map))).obj (torSupportModule J K n) ≅
        quotientModule L
          (((Tor (ModuleCat S) n).obj (ModuleCat.of S (S ⧸ K.map f))).obj
            (ModuleCat.of S (S ⧸ J.map f)))
          (by rw [← hL]; exact extendedQuotientsTor_support f J K n) := by
    subst L
    exact flatBaseChangeTorLiteralQuotientIso f hf J K n
  exact aux _ (Ideal.map_sup f J K)

/-- On a pure tensor, restriction is exactly ambient canonical Tor base change followed
by the two literal quotient-coefficient identifications. -/
@[simp] theorem flatBaseChangeTorLiteralQuotientIso_hom_tmul (f : R →+* S) (hf : f.Flat)
    (J K : Ideal R) (n : ℕ) (s : S) (m : torSupportModule J K n) :
    (flatBaseChangeTorLiteralQuotientIso f hf J K n).hom
      (Ideal.Quotient.mk ((J ⊔ K).map f) s ⊗ₜ[R ⧸ (J ⊔ K),supportQuotientMap f (J ⊔ K)] m) =
      (extendedQuotientsTorIso f J K n).hom
        ((flatBaseChangeTorIso f hf (ModuleCat.of R (R ⧸ K))
          (ModuleCat.of R (R ⧸ J)) n).hom (s ⊗ₜ[R,f] m)) := by
  change (extendedQuotientsTorIso f J K n).hom
    ((flatBaseChangeTorIso f hf _ _ n).hom
      ((quotientScalarExtensionIso f (J ⊔ K) _ _).hom _)) = _
  exact congrArg (fun x => (extendedQuotientsTorIso f J K n).hom
    ((flatBaseChangeTorIso f hf (ModuleCat.of R (R ⧸ K))
      (ModuleCat.of R (R ⧸ J)) n).hom x))
    (quotientScalarExtensionIso_hom_tmul f (J ⊔ K) _
      (quotient_support_le_annihilator J K n) s m)

end ModuleCat.TorComparison
