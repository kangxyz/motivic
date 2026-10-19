/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Evaluation
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Henselian

/-!
# Henselian spectra that are actual objects of the smooth Nisnevich site

Suppose the structure map `Spec R → S` is smooth, separated and quasi-compact,
where `R` is henselian local. The existing split-member theorem for a big
Nisnevich covering family gives a section in the smooth site itself, since
that section necessarily commutes with the structure maps. Thus every covering
sieve at this actual object is maximal, and epimorphisms of ordinary abelian
sheaves are surjective on its sections.

The structure-map hypotheses are essential to the object being used here.
No arbitrary henselization is treated as a smooth finite-type object, and no
comparison with henselian stalks or the small Nisnevich site is asserted.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable {S : Scheme.{u}} (R : Type u) [CommRing R] [HenselianLocalRing R]
  (p : Spec (.of R) ⟶ S) [Smooth p] [IsSeparated p] [QuasiCompact p]

set_option backward.isDefEq.respectTransparency false in
/-- A covering family of an actual smooth henselian spectrum contains a smooth-site split map. -/
theorem exists_section_of_mem_nisnevichPrecoverage_of_henselian
    {P : Presieve (mk p)} (hP : P ∈ nisnevichPrecoverage S _) :
    ∃ (Y : SmoothSite S) (f : Y ⟶ mk p), P f ∧ ∃ t : mk p ⟶ Y, t ≫ f = 𝟙 _ := by
  obtain ⟨ι, V, f, rfl⟩ := P.exists_eq_ofArrows
  have hP' : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (f i).left) ∈
      Nisnevich.precoverage (Spec (.of R)) := by
    have h := mem_nisnevichPrecoverage_iff.mp hP
    rw [Presieve.map_ofArrows] at h
    exact h
  obtain ⟨_, _, ⟨i⟩, t, ht⟩ :=
    Nisnevich.exists_section_of_mem_precoverage_of_henselian R hP'
  have hw : (f i).left ≫ p = (V i).hom := MorphismProperty.Over.w (f i)
  let t' : mk p ⟶ V i := homMk t (by
    change t ≫ (V i).hom = p
    rw [← hw, ← Category.assoc, ht, Category.id_comp])
  refine ⟨V i, f i, ⟨i⟩, t', ?_⟩
  apply (forgetScheme S).map_injective
  exact ht

/-- The only covering sieve at an actual smooth henselian spectrum is maximal. -/
theorem nisnevich_covering_sieve_eq_top_of_henselian
    {P : Sieve (mk p)} (hP : P ∈ nisnevichTopology S _) : P = ⊤ := by
  obtain ⟨Q, hQ, hQP⟩ := mem_nisnevichTopology_iff.mp hP
  obtain ⟨Y, f, hf, t, ht⟩ :=
    exists_section_of_mem_nisnevichPrecoverage_of_henselian R p hQ
  apply Sieve.id_mem_iff_eq_top.mp
  simpa only [ht] using P.downward_closed (hQP _ _ hf) t

section Concrete

variable {A : Type v} [Category.{w} A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- Local surjectivity is actual surjectivity on this henselian object's sections. -/
theorem surjective_app_of_isLocallySurjective_of_henselian
    {F G : (SmoothSite S)ᵒᵖ ⥤ A} (φ : F ⟶ G)
    [Presheaf.IsLocallySurjective (nisnevichTopology S) φ] :
    Function.Surjective (φ.app (op (mk p))) := by
  intro s
  have htop := nisnevich_covering_sieve_eq_top_of_henselian R p
    (Presheaf.imageSieve_mem (nisnevichTopology S) φ s)
  have hi : Presheaf.imageSieve φ s (𝟙 _) := by rw [htop]; trivial
  obtain ⟨t, ht⟩ := hi
  exact ⟨t, by simpa using ht⟩

end Concrete

/-- Epimorphisms of ordinary Nisnevich sheaves are surjective at the actual henselian object. -/
theorem surjective_app_of_epi_of_henselian
    {F G : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (mk p))) := by
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat φ).mpr inferInstance
  exact surjective_app_of_isLocallySurjective_of_henselian R p φ.hom

end AlgebraicGeometry.Scheme.SmoothSite
