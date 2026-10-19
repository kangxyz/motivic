/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Large.DegreeZero
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.Algebra.Category.Grp.FilteredColimits

/-!
# Local triviality of actual positive-degree ordinary cohomology

An actual degree-one Ext class is the connecting class of a section of the
cokernel of an ordinary injective embedding. The image sieve of that section
under the actual cokernel projection is covering, and the original cohomology
restriction kills the class on every arrow in that sieve. Concrete dimension
shifting gives local triviality in every positive degree.

The coefficient and Ext universes remain explicit. The only injectives used
are ordinary sheaf injectives. This is local effacement, rather than a Cech
comparison or an affine-line acyclicity theorem.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite

universe w t v u

namespace CategoryTheory.Sheaf.LargeCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- A section lift on the actual image sieve kills the corresponding degree-one boundary. -/
theorem boundary_restriction_eq_zero_of_imageSieve
    {S : ShortComplex (Sheaf J AddCommGrpCat.{max v t})} (hS : S.ShortExact)
    {X Y : C} (y : Ext (Hypercohomology.freeAbelianSheaf J X) S.X₃ 0) (f : Y ⟶ X)
    (hf : Presheaf.imageSieve S.g.hom (zeroSections J S.X₃ X y) f) :
    (presheaf J S.X₁ 1).map f.op (y.comp hS.extClass rfl) = 0 := by
  obtain ⟨s, hs⟩ := hf
  let z := (zeroSections J S.X₂ Y).symm s
  have hy : (presheaf J S.X₃ 0).map f.op y =
      ((presheafFunctor J 0).map S.g).app (op Y) z := by
    apply (zeroSections J S.X₃ Y).injective
    rw [zeroSections_restriction, zeroSections_naturality]
    exact hs.symm.trans (congrArg (S.g.hom.app (op Y))
      ((zeroSections J S.X₂ Y).apply_symm_apply s).symm)
  change Ext (Hypercohomology.freeAbelianSheaf J X) S.X₃ 0 at y
  change (Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor J).map f)).comp
    (y.comp hS.extClass rfl) (zero_add 1) = 0
  rw [← Ext.comp_assoc_of_second_deg_zero]
  change ((presheaf J S.X₃ 0).map f.op y).comp hS.extClass rfl = 0
  rw [hy]
  change (z.comp (Ext.mk₀ S.g) (add_zero 0)).comp hS.extClass rfl = 0
  rw [Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{max v t})]

/-- The original ordinary-injective embedding and its actual sheaf cokernel. -/
abbrev injectivePresentation (F : Sheaf J AddCommGrpCat.{max v t}) :
    ShortComplex (Sheaf J AddCommGrpCat.{max v t}) :=
  ShortComplex.cokernelSequence (Injective.ι F)

omit [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})] in
/-- The ordinary injective-cokernel presentation is genuinely short exact. -/
theorem injectivePresentation_shortExact (F : Sheaf J AddCommGrpCat.{max v t}) :
    (injectivePresentation J F).ShortExact where
  exact := ShortComplex.cokernelSequence_exact _
  mono_f := by
    change Mono (Injective.ι F)
    infer_instance
  epi_g := by
    change Epi (cokernel.π (Injective.ι F))
    infer_instance

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max v t}]

/-- Every actual H1 class is killed on the covering image sieve of a section of the
cokernel of its coefficient sheaf's actual ordinary injective embedding. -/
theorem exists_imageSieve_restriction_eq_zero_one
    (F : Sheaf J AddCommGrpCat.{max v t}) (X : C) (x : H J F 1 X) :
    ∃ s : (cokernel (Injective.ι F)).obj.obj (op X),
      Presheaf.imageSieve (cokernel.π (Injective.ι F)).hom s ∈ J X ∧
      ∀ ⦃Y : C⦄ (f : Y ⟶ X),
        Presheaf.imageSieve (cokernel.π (Injective.ι F)).hom s f →
          (presheaf J F 1).map f.op x = 0 := by
  let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι F))
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
    (Hypercohomology.freeAbelianSheaf J X) hS x (Ext.eq_zero_of_injective _) rfl
  let s := zeroSections J S.X₃ X y
  have : Sheaf.IsLocallySurjective (cokernel.π (Injective.ι F)) :=
    (Sheaf.isLocallySurjective_iff_epi' (J := J) AddCommGrpCat
      (cokernel.π (Injective.ι F))).mpr inferInstance
  refine ⟨s, Presheaf.imageSieve_mem J _ s, ?_⟩
  intro Y f hf
  rw [← hy]
  exact boundary_restriction_eq_zero_of_imageSieve J hS y f hf

/-- The zero-restriction sieve of an actual degree-one ordinary cohomology class covers. -/
theorem zeroSieve_mem_one (F : Sheaf J AddCommGrpCat.{max v t})
    (X : C) (x : H J F 1 X) :
    Presheaf.equalizerSieve (F := presheaf J F 1) x 0 ∈ J X := by
  obtain ⟨s, hs, hzero⟩ := exists_imageSieve_restriction_eq_zero_one J F X x
  refine J.superset_covering ?_ hs
  intro Y f hf
  change (presheaf J F 1).map f.op x = (presheaf J F 1).map f.op 0
  rw [map_zero]
  exact hzero f hf

/-- Ordinary-injective dimension shifting makes every positive-degree class locally zero. -/
theorem zeroSieve_mem_succ (F : Sheaf J AddCommGrpCat.{max v t})
    (n : ℕ) (X : C) (x : H J F (n + 1) X) :
    Presheaf.equalizerSieve (F := presheaf J F (n + 1)) x 0 ∈ J X := by
  induction n generalizing F with
  | zero => exact zeroSieve_mem_one J F X x
  | succ n ih =>
    let S := ShortComplex.mk _ _ (cokernel.condition (Injective.ι F))
    have hS : S.ShortExact :=
      { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel S.f) }
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
      (Hypercohomology.freeAbelianSheaf J X) hS x (Ext.eq_zero_of_injective _) rfl
    have hcover := ih S.X₃ y
    refine J.superset_covering ?_ hcover
    intro Y f hf
    change (presheaf J S.X₃ (n + 1)).map f.op y =
      (presheaf J S.X₃ (n + 1)).map f.op 0 at hf
    rw [map_zero] at hf
    change (presheaf J F (n + 1 + 1)).map f.op x =
      (presheaf J F (n + 1 + 1)).map f.op 0
    rw [map_zero, ← hy]
    change (Ext.mk₀ ((Hypercohomology.freeAbelianSheafFunctor J).map f)).comp
      (y.comp hS.extClass rfl) (zero_add (n + 1 + 1)) = 0
    rw [← Ext.comp_assoc _ _ _ (zero_add (n + 1)) rfl (by omega)]
    change ((presheaf J S.X₃ (n + 1)).map f.op y).comp hS.extClass rfl = 0
    rw [hf]
    exact Ext.zero_comp (Hypercohomology.freeAbelianSheaf J Y) (n + 1) hS.extClass _ rfl

end CategoryTheory.Sheaf.LargeCohomology
