/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom.Gluing
public import Aglib.AlgebraicGeometry.Modules.Locality.Exactness

/-! # Gluing specified trivializations on disjoint boundary components

The actual module sheaf is retained. Disjointness supplies compatibility, rather than
requiring a matching-family hypothesis or replacing the specified local isomorphisms.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
universe u v
namespace AlgebraicGeometry.Scheme.Modules.InternalHom

/-- Isomorphisms on a disjoint open cover glue with their exact original restrictions. -/
theorem exists_iso_of_disjoint_restrictions {X : Scheme.{u}} {ι : Type v}
    (Y : ι → Scheme.{u}) (a : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (a i)]
    (hcover : ∀ x : X, ∃ (i : ι) (y : Y i), a i y = x)
    (hdisj : Pairwise fun i j => Disjoint (a i).opensRange (a j).opensRange)
    (M N : X.Modules) (e : ∀ i, M.restrict (a i) ≅ N.restrict (a i)) :
    ∃ E : M ≅ N, ∀ i, (Scheme.Modules.restrictFunctor (a i)).map E.hom = (e i).hom := by
  classical
  let H : X.Modules := sheaf X M N
  let A : TopCat.Sheaf Ab X := ⟨H.val.presheaf, H.isSheaf⟩
  let s i : Γ(H, (a i).opensRange) := restrictionHomEquiv (a i) M N (e i).hom
  have hs : TopCat.Presheaf.IsCompatible H.val.presheaf (fun i => (a i).opensRange) s := by
    intro i j
    by_cases hij : i = j
    · subst j
      rfl
    · have hempty : (a i).opensRange ⊓ (a j).opensRange = ⊥ :=
        disjoint_iff.mp (hdisj hij)
      apply A.eq_of_locally_eq' (fun _ : Empty => ⊥) _
        (fun i => nomatch i) (by simp [hempty])
      intro k
      exact k.elim
  obtain ⟨t, ht, _⟩ := A.existsUnique_gluing' (fun i => (a i).opensRange)
    (⊤ : X.Opens) (fun _ => homOfLE le_top) (restrictionRanges_cover Y a hcover).ge s hs
  let F := (globalHomEquiv X M N).symm t
  have hF : ∀ i, (Scheme.Modules.restrictFunctor (a i)).map F = (e i).hom := by
    intro i
    apply (restrictionHomEquiv (a i) M N).injective
    have hh := globalHomEquiv_restrict (a i) M N F
    simp only [F, Equiv.apply_symm_apply] at hh
    exact hh.symm.trans (ht i)
  have : IsIso F := isIso_of_restrict_openCover Y a hcover F (by
    intro i
    rw [hF]
    infer_instance)
  exact ⟨asIso F, hF⟩

end AlgebraicGeometry.Scheme.Modules.InternalHom
