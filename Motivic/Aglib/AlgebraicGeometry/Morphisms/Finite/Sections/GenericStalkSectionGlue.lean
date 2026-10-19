/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Sections.DisjointOpenSectionGlue
public import Mathlib.AlgebraicGeometry.SpreadingOut

/-! # Original stalk sections spread simultaneously on a generic-containing open -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u
namespace AlgebraicGeometry.Scheme

/-- On a locally Noetherian source the actual maps from all stalk spectra detect
scheme morphisms, without reducedness. -/
theorem hom_ext_of_fromSpecStalk {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f g : X ⟶ Y) (h : ∀ x, X.fromSpecStalk x ≫ f = X.fromSpecStalk x ≫ g) : f = g := by
  choose U hx he using fun x => spread_out_unique_of_isGermInjective' f g (h x)
  have hc : IsOpenCover U := .mk (by
    apply top_unique
    intro x _
    exact (le_iSup U x) (hx x))
  exact (X.openCoverOfIsOpenCover U hc).hom_ext f g he

/-- The full original generic-stalk values are preserved, including nilpotent data.
The local sections are glued on disjoint actual opens, so no unjustified
closed-image argument for an open disagreement locus is needed. -/
theorem exists_generic_open_section_of_stalk_sections
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [NoetherianSpace X]
    (p : Y ⟶ X) [LocallyOfFiniteType p]
    (φ : ∀ x : genericPoints X, Spec (X.presheaf.stalk x.val) ⟶ Y)
    (hφ : ∀ x, φ x ≫ p = X.fromSpecStalk x.val) :
    ∃ (O : X.Opens) (hO : genericPoints X ⊆ (O : Set X)) (s : O.toScheme ⟶ Y),
      s ≫ p = O.ι ∧ ∀ x : genericPoints X,
        O.fromSpecStalkOfMem x.val (hO x.property) ≫ s = φ x := by
  classical
  have hl (x : genericPoints X) : ∃ (U : X.Opens) (hx : x.val ∈ U) (s : U.toScheme ⟶ Y),
      U.fromSpecStalkOfMem x.val hx ≫ s = φ x ∧ s ≫ p = U.ι := by
    obtain ⟨U, hx, s, hs, hp⟩ := spread_out_of_isGermInjective' (𝟙 X) p (φ x)
      (by simpa using hφ x)
    exact ⟨U, hx, s, hs.symm, by simpa using hp⟩
  choose U hx s hs hp using hl
  let W (x : genericPoints X) : X.Opens := U x ⊓ genericComponentOpen X x
  have hw (x : genericPoints X) : x.val ∈ W x := ⟨hx x, mem_genericComponentOpen X x⟩
  let a (x : genericPoints X) : (W x).toScheme ⟶ (U x).toScheme := X.homOfLE inf_le_left
  let t (x : genericPoints X) : (W x).toScheme ⟶ Y := a x ≫ s x
  have ht (x) : t x ≫ p = (W x).ι := by simp [t, a, hp]
  have hd : Pairwise fun x y => Disjoint (W x : Set X) (W y : Set X) := by
    intro x y hxy
    exact (genericComponentOpen_pairwiseDisjoint X hxy).mono inf_le_right inf_le_right
  obtain ⟨sO, hsO, he⟩ := exists_section_on_disjoint_open_union p W hd t ht
  let O : X.Opens := ⨆ x, W x
  have hO : genericPoints X ⊆ (O : Set X) := fun x hx =>
    (le_iSup W ⟨x, hx⟩) (hw ⟨x, hx⟩)
  refine ⟨O, hO, sO, hsO, ?_⟩
  intro x
  have h₁ : (W x).fromSpecStalkOfMem x.val (hw x) ≫ X.homOfLE (le_iSup W x) =
      O.fromSpecStalkOfMem x.val (hO x.property) := by
    apply (cancel_mono O.ι).mp
    simp only [O, Category.assoc, homOfLE_ι, Opens.fromSpecStalkOfMem_ι]
  have h₂ : (W x).fromSpecStalkOfMem x.val (hw x) ≫ a x =
      (U x).fromSpecStalkOfMem x.val (hx x) := by
    apply (cancel_mono (U x).ι).mp
    simp only [a, Category.assoc, homOfLE_ι, Opens.fromSpecStalkOfMem_ι]
  rw [← h₁, Category.assoc, he]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫ s x) h₂).trans (hs x))

end AlgebraicGeometry.Scheme
