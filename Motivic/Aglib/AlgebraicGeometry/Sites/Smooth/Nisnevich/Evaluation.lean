/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Topology
public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.FieldEvaluation

/-!
# Exact evaluation at the base field on the smooth Nisnevich site

Every Nisnevich covering family of the actual base object `Spec k` contains
an actual smooth-site morphism with a section. Thus every covering sieve
there is maximal, and evaluation of ordinary abelian sheaves is exact.

The field `k` is arbitrary. Evaluation here is at the base object on its own
smooth finite-type site; no arbitrary field extension is asserted to be an
object of that site.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme.SmoothSite

variable (k : Type u) [Field k]

set_option backward.isDefEq.respectTransparency false in
/-- A Nisnevich covering family of the smooth base object contains a split map.
The section is a literal smooth-site morphism over the base. -/
theorem exists_section_of_mem_nisnevichPrecoverage_base
    {R : Presieve (base (Spec (.of k)))}
    (hR : R ∈ nisnevichPrecoverage (Spec (.of k)) _) :
    ∃ (Y : SmoothSite (Spec (.of k))) (f : Y ⟶ base (Spec (.of k))), R f ∧
      ∃ s : base (Spec (.of k)) ⟶ Y, s ≫ f = 𝟙 _ := by
  obtain ⟨ι, V, f, rfl⟩ := R.exists_eq_ofArrows
  have hR' : Presieve.ofArrows (fun i ↦ (V i).left) (fun i ↦ (f i).left) ∈
      Nisnevich.precoverage (Spec (.of k)) := by
    have h := mem_nisnevichPrecoverage_iff.mp hR
    rw [Presieve.map_ofArrows] at h
    exact h
  obtain ⟨_, _, ⟨i⟩, s, hs⟩ := Nisnevich.exists_section_of_mem_precoverage k hR'
  have hfhom : (f i).left = (V i).hom := by
    have h := MorphismProperty.Over.w (f i)
    change (f i).left ≫ 𝟙 _ = (V i).hom at h
    exact (Category.comp_id _).symm.trans h
  let s' : base (Spec (.of k)) ⟶ V i := homMk s (by
    change s ≫ (V i).hom = 𝟙 _
    simpa only [← hfhom] using hs)
  refine ⟨V i, f i, ⟨i⟩, s', ?_⟩
  apply (forgetScheme (Spec (.of k))).map_injective
  exact hs

/-- The only covering sieve of the smooth base object is the maximal sieve. -/
theorem nisnevich_covering_sieve_base_eq_top
    {R : Sieve (base (Spec (.of k)))}
    (hR : R ∈ nisnevichTopology (Spec (.of k)) _) : R = ⊤ := by
  obtain ⟨Q, hQ, hQR⟩ := mem_nisnevichTopology_iff.mp hR
  obtain ⟨Y, f, hf, s, hs⟩ := exists_section_of_mem_nisnevichPrecoverage_base k hQ
  apply Sieve.id_mem_iff_eq_top.mp
  simpa only [hs] using R.downward_closed (hQR _ _ hf) s

/-- Exact characterization of smooth Nisnevich covering sieves at the base field. -/
theorem mem_nisnevichTopology_base_iff (R : Sieve (base (Spec (.of k)))) :
    R ∈ nisnevichTopology (Spec (.of k)) _ ↔ R = ⊤ :=
  ⟨nisnevich_covering_sieve_base_eq_top k,
    fun h ↦ h ▸ (nisnevichTopology (Spec (.of k))).top_mem _⟩

section Concrete

variable {A : Type v} [Category.{w} A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

/-- Local surjectivity is actual surjectivity on sections at the base field. -/
theorem surjective_app_base_of_isLocallySurjective
    {F G : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ A} (φ : F ⟶ G)
    [Presheaf.IsLocallySurjective (nisnevichTopology (Spec (.of k))) φ] :
    Function.Surjective (φ.app (op (base (Spec (.of k))))) := by
  intro s
  have htop := nisnevich_covering_sieve_base_eq_top k
    (Presheaf.imageSieve_mem (nisnevichTopology (Spec (.of k))) φ s)
  have hi : Presheaf.imageSieve φ s (𝟙 _) := by rw [htop]; trivial
  obtain ⟨t, ht⟩ := hi
  exact ⟨t, by simpa using ht⟩

/-- Local injectivity is actual injectivity on sections at the base field. -/
theorem injective_app_base_of_isLocallyInjective
    {F G : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ A} (φ : F ⟶ G)
    [Presheaf.IsLocallyInjective (nisnevichTopology (Spec (.of k))) φ] :
    Function.Injective (φ.app (op (base (Spec (.of k))))) := by
  intro s t h
  exact (Presheaf.equalizerSieve_eq_top_iff s t).mp
    (nisnevich_covering_sieve_base_eq_top k
      (Presheaf.equalizerSieve_mem (nisnevichTopology (Spec (.of k))) φ s t h))

end Concrete

/-- Ordinary abelian Nisnevich sheafification leaves sections at the base field
unchanged through its actual unit, since local bijectivity is actual bijectivity. -/
theorem isIso_toSheafify_app_base
    (F : (SmoothSite (Spec (.of k)))ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso ((toSheafify (nisnevichTopology (Spec (.of k))) F).app
      (op (base (Spec (.of k))))) := by
  have : Presheaf.IsLocallyInjective (nisnevichTopology (Spec (.of k)))
      (toSheafify (nisnevichTopology (Spec (.of k))) F) :=
    Presheaf.isLocallyInjective_toSheafify' _ F
  have : Presheaf.IsLocallySurjective (nisnevichTopology (Spec (.of k)))
      (toSheafify (nisnevichTopology (Spec (.of k))) F) :=
    Presheaf.isLocallySurjective_toSheafify' _ F
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨injective_app_base_of_isLocallyInjective k _,
      surjective_app_base_of_isLocallySurjective k _⟩

/-- Evaluation of ordinary abelian Nisnevich sheaves at the actual smooth base object. -/
def nisnevichBaseEvaluation :
    Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1} ⥤
      AddCommGrpCat.{u + 1} :=
  sheafToPresheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat ⋙
    (CategoryTheory.evaluation _ _).obj (op (base (Spec (.of k))))

instance : (nisnevichBaseEvaluation k).Additive := by
  unfold nisnevichBaseEvaluation
  infer_instance

instance : PreservesFiniteLimits (nisnevichBaseEvaluation k) := by
  unfold nisnevichBaseEvaluation
  infer_instance

/-- Every epimorphism of ordinary Nisnevich sheaves is surjective at the base field. -/
theorem surjective_app_base_of_epi
    {F G : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (base (Spec (.of k))))) := by
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat φ).mpr inferInstance
  exact surjective_app_base_of_isLocallySurjective k φ.hom

instance : (nisnevichBaseEvaluation k).PreservesEpimorphisms where
  preserves φ _ := (AddCommGrpCat.epi_iff_surjective _).mpr
    (surjective_app_base_of_epi k φ)

/-- Actual base-field evaluation preserves kernels, cokernels, and homology. -/
instance : (nisnevichBaseEvaluation k).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (nisnevichBaseEvaluation k)

/-- Every exact sequence of ordinary Nisnevich sheaves stays exact at the base field. -/
theorem exact_map_nisnevichBaseEvaluation
    (S : ShortComplex (Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}))
    (hS : S.Exact) : (S.map (nisnevichBaseEvaluation k)).Exact :=
  hS.map (nisnevichBaseEvaluation k)

end AlgebraicGeometry.Scheme.SmoothSite
