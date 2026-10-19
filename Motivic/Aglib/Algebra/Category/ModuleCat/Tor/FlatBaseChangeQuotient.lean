/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.QuotientSupportAction
public import Motivic.Aglib.Algebra.Category.ModuleCat.Tor.FlatBaseChange

/-!
# Quotient linearity of actual flat Tor base change

Scalar extension sends an annihilating ideal to an annihilating ideal.
The existing canonical flat-base-change isomorphism therefore descends to
modules over the image support quotient. Its underlying map is exactly that
canonical map. Identity and composition for changing scalar rings remain
separate coherence statements.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace ModuleCat.TorComparison

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Extending scalars maps every annihilating ideal to an annihilating ideal. -/
theorem map_support_le_annihilator_extendScalars (f : R →+* S) (I : Ideal R)
    (M : ModuleCat.{u} R) (hM : I ≤ Module.annihilator R M) :
    Ideal.map f I ≤ Module.annihilator S ((ModuleCat.extendScalars f).obj M) := by
  let := f.toAlgebra
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  apply Module.mem_annihilator.mpr
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s m =>
    change (r • s) ⊗ₜ[R] m = 0
    rw [TensorProduct.smul_tmul, Module.mem_annihilator.mp (hM hr) m,
      TensorProduct.tmul_zero]
  | add x y hx hy =>
    exact (map_add (Module.toAddMonoidEnd S ((ModuleCat.extendScalars f).obj M) (f r))
      x y).trans ((congrArg₂ (fun a b : (ModuleCat.extendScalars f).obj M => a + b)
        hx hy).trans (zero_add _))

/-- The image sum ideal annihilates the source of canonical flat Tor base change. -/
theorem flatBaseChangeTor_source_support (f : R →+* S) (J K : Ideal R) (n : ℕ) :
    Ideal.map f (J ⊔ K) ≤ Module.annihilator S
      ((ModuleCat.extendScalars f).obj
        (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj
          (ModuleCat.of R (R ⧸ J)))) :=
  map_support_le_annihilator_extendScalars f (J ⊔ K) _
    (quotient_support_le_annihilator J K n)

/-- The same image support annihilates the actual target Tor under flat base change. -/
theorem flatBaseChangeTor_target_support (f : R →+* S) (hf : f.Flat)
    (J K : Ideal R) (n : ℕ) :
    Ideal.map f (J ⊔ K) ≤ Module.annihilator S
      (((Tor (ModuleCat S) n).obj
        ((ModuleCat.extendScalars f).obj (ModuleCat.of R (R ⧸ K)))).obj
        ((ModuleCat.extendScalars f).obj (ModuleCat.of R (R ⧸ J)))) :=
  (flatBaseChangeTor_source_support f J K n).trans
    ((flatBaseChangeTorIso f hf (ModuleCat.of R (R ⧸ K))
      (ModuleCat.of R (R ⧸ J)) n).hom.hom.annihilator_le_of_surjective
      ((ModuleCat.epi_iff_surjective _).mp inferInstance))

/-- The genuine canonical base-change isomorphism is linear over the image
scheme-theoretic support quotient, without any flatness of the coefficients. -/
def flatBaseChangeTorQuotientIso (f : R →+* S) (hf : f.Flat)
    (J K : Ideal R) (n : ℕ) :
    quotientModule (Ideal.map f (J ⊔ K))
      ((ModuleCat.extendScalars f).obj
        (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj
          (ModuleCat.of R (R ⧸ J))))
      (flatBaseChangeTor_source_support f J K n) ≅
    quotientModule (Ideal.map f (J ⊔ K))
      (((Tor (ModuleCat S) n).obj
        ((ModuleCat.extendScalars f).obj (ModuleCat.of R (R ⧸ K)))).obj
        ((ModuleCat.extendScalars f).obj (ModuleCat.of R (R ⧸ J))))
      (flatBaseChangeTor_target_support f hf J K n) :=
  quotientLinearIso _ _ _ (flatBaseChangeTorIso f hf _ _ n)

/-- Quotient descent retains exactly the canonical flat Tor comparison on elements. -/
theorem flatBaseChangeTorQuotientIso_hom_apply (f : R →+* S) (hf : f.Flat)
    (J K : Ideal R) (n : ℕ)
    (x : (ModuleCat.extendScalars f).obj
      (((Tor (ModuleCat R) n).obj (ModuleCat.of R (R ⧸ K))).obj
        (ModuleCat.of R (R ⧸ J)))) :
    (flatBaseChangeTorQuotientIso f hf J K n).hom x =
      (flatBaseChangeTorIso f hf (ModuleCat.of R (R ⧸ K)) (ModuleCat.of R (R ⧸ J)) n).hom x :=
  rfl

end ModuleCat.TorComparison
