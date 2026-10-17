/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.CategoryTheory.Sites.AbelianCechDescent
public import Motivic.Cohomology.SheafCohomologyLocalTriviality

/-!
# A concrete Cech coboundary criterion for actual ordinary H1

Every degree-one ordinary cohomology class comes from a section of the
cokernel of the actual ordinary injective embedding. Its boundary is literal
postcomposition with the extension class, with the covariant Ext convention.
If local lifts of that section have differences given by a Cech coboundary,
the adjusted lifts glue and the original class is zero.

The smooth Nisnevich endpoint uses the original covering family and its
cover-specific pullbacks. Coefficients and Ext have independent universes.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits AlgebraicGeometry Opposite

universe w t v u

namespace Motivic.SheafCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- Local lifts with a literal coboundary of differences kill the corresponding
degree-one extension-class boundary. -/
theorem boundary_eq_zero_of_coboundary
    {S : ShortComplex (Sheaf J AddCommGrpCat.{max v t})} (hS : S.ShortExact)
    {X : C} {ι : Type*} {U : ι → C} (p : ∀ i, U i ⟶ X)
    (hp : Sieve.ofArrows U p ∈ J X)
    [(Presieve.ofArrows U p).HasPairwisePullbacks]
    (y : H J S.X₃ 0 X) (l : ∀ i, S.X₂.obj.obj (op (U i)))
    (hl : ∀ i, S.g.hom.app (op (U i)) (l i) =
      S.X₃.obj.map (p i).op (zeroSections J S.X₃ X y))
    (a : ∀ i, S.X₁.obj.obj (op (U i)))
    (ha : ∀ i j,
      S.X₂.obj.map (pullback.fst (p i) (p j)).op (l i) -
        S.X₂.obj.map (pullback.snd (p i) (p j)).op (l j) =
      S.f.hom.app (op (pullback (p i) (p j)))
        (S.X₁.obj.map (pullback.fst (p i) (p j)).op (a i) -
          S.X₁.obj.map (pullback.snd (p i) (p j)).op (a j))) :
    y.comp hS.extClass rfl = 0 := by
  obtain ⟨s, hs⟩ := Sheaf.exists_section_lift_of_coboundary J S p hp
    (zeroSections J S.X₃ X y) l hl a ha
  have h := boundary_restriction_eq_zero_of_imageSieve J hS y (𝟙 X)
    ⟨s, by simpa using hs⟩
  simpa using h

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

/-- The actual quotient-section boundary, using the covariant extension-class sign. -/
def injectiveSectionBoundary (F : Sheaf J AddCommGrpCat.{max v t}) (X : C) :
    (cokernel (Injective.ι F)).obj.obj (op X) →+ H J F 1 X := by
  change _ →+ Ext (Hypercohomology.freeAbelianSheaf J X) F 1
  let δ : Ext (cokernel (Injective.ι F)) F 1 :=
    (injectivePresentation_shortExact J F).extClass
  let e : (cokernel (Injective.ι F)).obj.obj (op X) →+
      Ext (Hypercohomology.freeAbelianSheaf J X) (cokernel (Injective.ι F)) 0 :=
    (zeroSections.{w, t, v, u} J (cokernel (Injective.ι F)) X).symm.toAddMonoidHom
  exact (δ.postcomp (Hypercohomology.freeAbelianSheaf J X) (a := 0) (b := 1) rfl).comp e

/-- The boundary is literally the degree-zero section class composed with the
extension class, without a hidden change of sign. -/
theorem injectiveSectionBoundary_apply (F : Sheaf J AddCommGrpCat.{max v t}) (X : C)
    (s : (cokernel (Injective.ι F)).obj.obj (op X)) :
    injectiveSectionBoundary J F X s =
      ((zeroSections J (cokernel (Injective.ι F)) X).symm s).comp
        (injectivePresentation_shortExact J F).extClass rfl := rfl

/-- Every actual ordinary H1 class is the boundary of an actual cokernel section. -/
theorem injectiveSectionBoundary_surjective
    (F : Sheaf J AddCommGrpCat.{max v t}) (X : C) :
    Function.Surjective (injectiveSectionBoundary J F X) := by
  intro x
  have : Injective (injectivePresentation J F).X₂ := by
    change Injective (Injective.under F)
    infer_instance
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁
    (Hypercohomology.freeAbelianSheaf J X) (injectivePresentation_shortExact J F)
    x (Ext.eq_zero_of_injective _) rfl
  refine ⟨zeroSections J (cokernel (Injective.ι F)) X y, ?_⟩
  rw [injectiveSectionBoundary_apply, AddEquiv.symm_apply_apply]
  exact hy

end Motivic.SheafCohomology

namespace Motivic.SheafCohomology

variable {B : Scheme.{u}}
  [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]
  [EnoughInjectives (Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})]

/-- Every actual H1 class admits quotient-section representatives and local lifts
on a genuine smooth Nisnevich covering family. -/
theorem exists_nisnevich_local_lifts_of_h_one
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    (X : SmoothSite B) (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology B) F 1 X) :
    ∃ s : (cokernel (Injective.ι F)).obj.obj (op X),
      injectiveSectionBoundary.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology B) F X s = x ∧
      ∃ (ι : Type (u + 1)) (U : ι → SmoothSite B) (p : ∀ i, U i ⟶ X),
        Presieve.ofArrows U p ∈ SmoothSite.nisnevichPrecoverage B X ∧
        ∃ l : ∀ i, (Injective.under F).obj.obj (op (U i)),
          ∀ i, (cokernel.π (Injective.ι F)).hom.app (op (U i)) (l i) =
            (cokernel (Injective.ι F)).obj.map (p i).op s := by
  let J := SmoothSite.nisnevichTopology B
  obtain ⟨s, hs⟩ := injectiveSectionBoundary_surjective.{w, u + 1, u, u + 1} J F X x
  have : Sheaf.IsLocallySurjective (cokernel.π (Injective.ι F)) :=
    (Sheaf.isLocallySurjective_iff_epi' (J := J) AddCommGrpCat.{u + 1}
      (cokernel.π (Injective.ι F))).mpr inferInstance
  obtain ⟨P, hP, hPQ⟩ := SmoothSite.mem_nisnevichTopology_iff.mp
    (Presheaf.imageSieve_mem J (cokernel.π (Injective.ι F)).hom s)
  obtain ⟨ι, U, p, rfl⟩ := P.exists_eq_ofArrows
  choose l hl using fun i => hPQ _ _ (Presieve.ofArrows.mk i)
  exact ⟨s, hs, ι, U, p, hP, l, hl⟩

/-- An actual H1 class is zero if the local lifts of its ordinary-injective
quotient section have a coboundary of differences on a genuine Nisnevich family. -/
theorem h_one_eq_zero_of_nisnevich_coboundary
    (F : Sheaf (SmoothSite.nisnevichTopology B) AddCommGrpCat.{u + 1})
    {X : SmoothSite B} (x : H.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology B) F 1 X)
    (s : (cokernel (Injective.ι F)).obj.obj (op X))
    (hs : injectiveSectionBoundary.{w, u + 1, u, u + 1} (SmoothSite.nisnevichTopology B) F X s = x)
    {ι : Type*} {U : ι → SmoothSite B} (p : ∀ i, U i ⟶ X)
    (hp : Presieve.ofArrows U p ∈ SmoothSite.nisnevichPrecoverage B X)
    (l : ∀ i, (Injective.under F).obj.obj (op (U i)))
    (hl : ∀ i, (cokernel.π (Injective.ι F)).hom.app (op (U i)) (l i) =
      (cokernel (Injective.ι F)).obj.map (p i).op s)
    (a : ∀ i, F.obj.obj (op (U i)))
    (ha : let _ := (SmoothSite.nisnevichPrecoverage B).hasPairwisePullbacks_of_mem hp
      ∀ i j,
        (Injective.under F).obj.map (pullback.fst (p i) (p j)).op (l i) -
          (Injective.under F).obj.map (pullback.snd (p i) (p j)).op (l j) =
        (Injective.ι F).hom.app (op (pullback (p i) (p j)))
          (F.obj.map (pullback.fst (p i) (p j)).op (a i) -
            F.obj.map (pullback.snd (p i) (p j)).op (a j))) :
    x = 0 := by
  let J := SmoothSite.nisnevichTopology B
  let : (Presieve.ofArrows U p).HasPairwisePullbacks :=
    (SmoothSite.nisnevichPrecoverage B).hasPairwisePullbacks_of_mem hp
  have hp' : Sieve.ofArrows U p ∈ J X :=
    SmoothSite.mem_nisnevichTopology_iff.mpr
      ⟨Presieve.ofArrows U p, hp, Sieve.le_generate _⟩
  rw [← hs, injectiveSectionBoundary_apply]
  apply boundary_eq_zero_of_coboundary.{w, u + 1, u, u + 1} J
    (injectivePresentation_shortExact.{u + 1, u, u + 1} J F)
    p hp' _ l ?_ a ha
  intro i
  change (cokernel.π (Injective.ι F)).hom.app (op (U i)) (l i) =
    (cokernel (Injective.ι F)).obj.map (p i).op
      ((zeroSections.{w, u + 1, u, u + 1} J (cokernel (Injective.ι F)) X)
        ((zeroSections.{w, u + 1, u, u + 1} J (cokernel (Injective.ι F)) X).symm s))
  rw [AddEquiv.apply_symm_apply]
  exact hl i

end Motivic.SheafCohomology
