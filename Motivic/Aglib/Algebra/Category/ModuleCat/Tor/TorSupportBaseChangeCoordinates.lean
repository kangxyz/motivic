/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.QuotientCoefficientExtension

/-!
# Literal support Tor restriction on pure tensors

The final map-of-sum to sum-of-maps transport retains the exact underlying
canonical Tor comparison, followed by literal quotient-coefficient identification.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct ChangeOfRings

universe u

namespace ModuleCat.TorComparison

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The final literal support transition retains the canonical pure-tensor formula,
including its dependent transport along the image-of-sum ideal equality. -/
@[simp] theorem torSupportBaseChangeIso_hom_tmul (f : R →+* S) (hf : f.Flat)
    (J K : Ideal R) (n : ℕ) (s : S) (m : torSupportModule J K n) :
    (torSupportBaseChangeIso f hf J K n).hom
      (Ideal.Quotient.mk (J.map f ⊔ K.map f) s ⊗ₜ[R ⧸ (J ⊔ K),supportQuotientMapSup f J K] m) =
      (extendedQuotientsTorIso f J K n).hom
        ((flatBaseChangeTorIso f hf (ModuleCat.of R (R ⧸ K))
          (ModuleCat.of R (R ⧸ J)) n).hom (s ⊗ₜ[R,f] m)) := by
  have aux (L : Ideal S) (hL : (J ⊔ K).map f = L) :
      let e :
        (ModuleCat.extendScalars (Ideal.quotientMap L f
          (by rw [← hL]; exact Ideal.le_comap_map))).obj (torSupportModule J K n) ≅
          quotientModule L
            (((Tor (ModuleCat S) n).obj (ModuleCat.of S (S ⧸ K.map f))).obj
              (ModuleCat.of S (S ⧸ J.map f)))
            (by rw [← hL]; exact extendedQuotientsTor_support f J K n) := by
        subst L
        exact flatBaseChangeTorLiteralQuotientIso f hf J K n
      e.hom (Ideal.Quotient.mk L s ⊗ₜ[R ⧸ (J ⊔ K),Ideal.quotientMap L f
        (by rw [← hL]; exact Ideal.le_comap_map)] m) =
        (extendedQuotientsTorIso f J K n).hom
          ((flatBaseChangeTorIso f hf (ModuleCat.of R (R ⧸ K))
            (ModuleCat.of R (R ⧸ J)) n).hom (s ⊗ₜ[R,f] m)) := by
    subst L
    exact flatBaseChangeTorLiteralQuotientIso_hom_tmul f hf J K n s m
  exact aux _ (Ideal.map_sup f J K)

end ModuleCat.TorComparison
