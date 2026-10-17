/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.NisnevichHenselian
public import Motivic.AlgebraicGeometry.Sites.NisnevichFieldEvaluation

/-!
# Ordinary Nisnevich evaluation at henselian local rings

Locally surjective (respectively injective) maps of ordinary presheaves are
surjective (respectively injective) at a henselian local spectrum, since its
only covering sieve is maximal. Consequently ordinary sheafification leaves
these sections unchanged, under the usual explicit sheafification hypotheses.

For abelian-group-valued sheaves, evaluation preserves epimorphisms, finite
limits, homology, and exact sequences. The target is `AddCommGrpCat.{u + 1}`
for the actual big Nisnevich site `Scheme.{u}`. Local Artinian rings are
included without any reducedness assumption.

The construction reuses the ordinary sheaf APIs used for field evaluation.
It does not construct sheafification with transfers or unbounded derived
functors.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v w

namespace Motivic.Nisnevich

section Concrete

variable {A : Type v} [Category.{w} A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]

private theorem surjective_app_of_covering_sieve_eq_top
    (X : Scheme.{u}) (hX : ∀ S ∈ topology X, S = ⊤)
    {F G : Scheme.{u}ᵒᵖ ⥤ A} (φ : F ⟶ G)
    [Presheaf.IsLocallySurjective topology φ] :
    Function.Surjective (φ.app (op X)) := by
  intro s
  have htop := hX _ (Presheaf.imageSieve_mem topology φ s)
  have hi : Presheaf.imageSieve φ s (𝟙 _) := by rw [htop]; trivial
  obtain ⟨t, ht⟩ := hi
  exact ⟨t, by simpa using ht⟩

private theorem injective_app_of_covering_sieve_eq_top
    (X : Scheme.{u}) (hX : ∀ S ∈ topology X, S = ⊤)
    {F G : Scheme.{u}ᵒᵖ ⥤ A} (φ : F ⟶ G)
    [Presheaf.IsLocallyInjective topology φ] :
    Function.Injective (φ.app (op X)) := by
  intro s t h
  exact (Presheaf.equalizerSieve_eq_top_iff s t).mp
    (hX _ (Presheaf.equalizerSieve_mem topology φ s t h))

/-- Local surjectivity is surjectivity on sections over a henselian local ring. -/
theorem surjective_app_of_isLocallySurjective_of_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {F G : Scheme.{u}ᵒᵖ ⥤ A} (φ : F ⟶ G)
    [Presheaf.IsLocallySurjective topology φ] :
    Function.Surjective (φ.app (op (Spec (.of R)))) :=
  surjective_app_of_covering_sieve_eq_top _
    (fun _ ↦ covering_sieve_eq_top_of_henselian R) φ

/-- Local surjectivity is surjectivity over a possibly nonreduced local Artinian ring. -/
theorem surjective_app_of_isLocallySurjective_of_artinian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    {F G : Scheme.{u}ᵒᵖ ⥤ A} (φ : F ⟶ G)
    [Presheaf.IsLocallySurjective topology φ] :
    Function.Surjective (φ.app (op (Spec (.of R)))) :=
  surjective_app_of_covering_sieve_eq_top _
    (fun _ ↦ covering_sieve_eq_top_of_artinian R) φ

/-- Local injectivity is injectivity on sections over a henselian local ring. -/
theorem injective_app_of_isLocallyInjective_of_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {F G : Scheme.{u}ᵒᵖ ⥤ A} (φ : F ⟶ G)
    [Presheaf.IsLocallyInjective topology φ] :
    Function.Injective (φ.app (op (Spec (.of R)))) :=
  injective_app_of_covering_sieve_eq_top _
    (fun _ ↦ covering_sieve_eq_top_of_henselian R) φ

/-- Local injectivity is injectivity over a possibly nonreduced local Artinian ring. -/
theorem injective_app_of_isLocallyInjective_of_artinian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    {F G : Scheme.{u}ᵒᵖ ⥤ A} (φ : F ⟶ G)
    [Presheaf.IsLocallyInjective topology φ] :
    Function.Injective (φ.app (op (Spec (.of R)))) :=
  injective_app_of_covering_sieve_eq_top _
    (fun _ ↦ covering_sieve_eq_top_of_artinian R) φ

end Concrete

section Sheafification

variable {A : Type v} [Category.{w} A] {FA : A → A → Type*}
  {CA : A → Type (u + 1)}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [HasWeakSheafify topology.{u} A]
  [hcomp : GrothendieckTopology.HasSheafCompose topology.{u} (forget A)]
  [hpres : GrothendieckTopology.PreservesSheafification topology.{u} (forget A)]
  [hreflect : (forget A).ReflectsIsomorphisms]

include hcomp hpres hreflect

/-- The ordinary sheafification unit is an isomorphism at a henselian local spectrum.
The explicit hypotheses are the standard concrete-category sheafification assumptions. -/
theorem isIso_toSheafify_app_of_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R] (F : Scheme.{u}ᵒᵖ ⥤ A) :
    IsIso ((toSheafify topology F).app (op (Spec (.of R)))) := by
  have : Presheaf.IsLocallyInjective topology (toSheafify topology F) :=
    Presheaf.isLocallyInjective_toSheafify' topology F
  have : Presheaf.IsLocallySurjective topology (toSheafify topology F) :=
    Presheaf.isLocallySurjective_toSheafify' topology F
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨injective_app_of_isLocallyInjective_of_henselian R _,
      surjective_app_of_isLocallySurjective_of_henselian R _⟩

/-- The ordinary sheafification unit is an isomorphism at a local Artinian spectrum,
including nonreduced local Artinian rings. -/
theorem isIso_toSheafify_app_of_artinian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (F : Scheme.{u}ᵒᵖ ⥤ A) :
    IsIso ((toSheafify topology F).app (op (Spec (.of R)))) := by
  have : Presheaf.IsLocallyInjective topology (toSheafify topology F) :=
    Presheaf.isLocallyInjective_toSheafify' topology F
  have : Presheaf.IsLocallySurjective topology (toSheafify topology F) :=
    Presheaf.isLocallySurjective_toSheafify' topology F
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    ⟨injective_app_of_isLocallyInjective_of_artinian R _,
      surjective_app_of_isLocallySurjective_of_artinian R _⟩

end Sheafification

/-- Evaluation of ordinary abelian Nisnevich sheaves at the spectrum of a ring. -/
noncomputable def ringEvaluation (R : Type u) [CommRing R] :
    Sheaf topology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  sheafToPresheaf topology AddCommGrpCat ⋙
    (CategoryTheory.evaluation Scheme.{u}ᵒᵖ AddCommGrpCat).obj (op (Spec (.of R)))

instance (R : Type u) [CommRing R] : (ringEvaluation R).Additive := by
  unfold ringEvaluation
  infer_instance

instance (R : Type u) [CommRing R] : PreservesFiniteLimits (ringEvaluation R) := by
  unfold ringEvaluation
  infer_instance

/-- Epimorphisms of abelian Nisnevich sheaves are surjective on henselian local sections. -/
theorem surjective_app_of_epi_of_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    {F G : Sheaf topology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (Spec (.of R)))) := by
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat φ).mpr inferInstance
  exact surjective_app_of_isLocallySurjective_of_henselian R φ.hom

/-- Epimorphisms of abelian Nisnevich sheaves are surjective on local Artinian sections. -/
theorem surjective_app_of_epi_of_artinian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    {F G : Sheaf topology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (Spec (.of R)))) := by
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat φ).mpr inferInstance
  exact surjective_app_of_isLocallySurjective_of_artinian R φ.hom

/-- Henselian local evaluation preserves epimorphisms. -/
instance ringEvaluation_preservesEpimorphisms_of_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (ringEvaluation R).PreservesEpimorphisms where
  preserves φ _ := (AddCommGrpCat.epi_iff_surjective _).mpr
    (surjective_app_of_epi_of_henselian R φ)

/-- Local Artinian evaluation preserves epimorphisms. -/
instance ringEvaluation_preservesEpimorphisms_of_artinian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R] :
    (ringEvaluation R).PreservesEpimorphisms where
  preserves φ _ := (AddCommGrpCat.epi_iff_surjective _).mpr
    (surjective_app_of_epi_of_artinian R φ)

/-- Henselian local evaluation preserves homology. -/
instance ringEvaluation_preservesHomology_of_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R] :
    (ringEvaluation R).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (ringEvaluation R)

/-- Local Artinian evaluation preserves homology. -/
instance ringEvaluation_preservesHomology_of_artinian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R] :
    (ringEvaluation R).PreservesHomology :=
  Functor.preservesHomology_of_preservesEpis_and_kernels (ringEvaluation R)

/-- Exact sequences of ordinary abelian Nisnevich sheaves remain exact at a
henselian local spectrum. -/
theorem exact_map_ringEvaluation_of_henselian
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : ShortComplex (Sheaf topology AddCommGrpCat.{u + 1})) (hS : S.Exact) :
    (S.map (ringEvaluation R)).Exact := hS.map (ringEvaluation R)

/-- Exact sequences of ordinary abelian Nisnevich sheaves remain exact at a
possibly nonreduced local Artinian spectrum. -/
theorem exact_map_ringEvaluation_of_artinian
    (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (S : ShortComplex (Sheaf topology AddCommGrpCat.{u + 1})) (hS : S.Exact) :
    (S.map (ringEvaluation R)).Exact := hS.map (ringEvaluation R)

end Motivic.Nisnevich
