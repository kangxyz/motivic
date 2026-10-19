/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Etale.Sections.ArtinianEtaleSections
public import Mathlib.AlgebraicGeometry.Restrict
public import Motivic.Aglib.Topology.GenericComponentOpens

/-! # Gluing actual scheme sections on disjoint component neighborhoods -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace
universe u v
namespace AlgebraicGeometry.Scheme

/-- Actual sections on disjoint opens glue on their union, retaining every local map. -/
theorem exists_section_on_disjoint_open_union {X Y : Scheme.{u}} (p : Y ⟶ X)
    {ι : Type v} (U : ι → X.Opens)
    (hd : Pairwise fun i j => Disjoint (U i : Set X) (U j : Set X))
    (s : ∀ i, (U i).toScheme ⟶ Y) (hs : ∀ i, s i ≫ p = (U i).ι) :
    ∃ t : (⨆ i, U i).toScheme ⟶ Y, t ≫ p = (⨆ i, U i).ι ∧
      ∀ i, X.homOfLE (le_iSup U i) ≫ t = s i := by
  classical
  let O : X.Opens := ⨆ i, U i
  let j (i : ι) : (U i).toScheme ⟶ O.toScheme := X.homOfLE (le_iSup U i)
  let C : O.toScheme.OpenCover :=
    { I₀ := ι
      X := fun i => (U i).toScheme
      f := j
      mem₀ := by
        rw [presieve₀_mem_precoverage_iff]
        refine ⟨?_, inferInstance⟩
        intro x
        obtain ⟨i, hi⟩ := Opens.mem_iSup.mp x.property
        refine ⟨i, ⟨x.val, hi⟩, ?_⟩
        apply Subtype.ext
        exact congrArg (fun f => f ⟨x.val, hi⟩) (X.homOfLE_ι (le_iSup U i)) }
  have hc : ∀ i j, pullback.fst (C.f i) (C.f j) ≫ s i =
      pullback.snd (C.f i) (C.f j) ≫ s j := by
    intro i j'
    by_cases hij : i = j'
    · subst j'
      have he : pullback.fst (C.f i) (C.f i) = pullback.snd (C.f i) (C.f i) :=
        (cancel_mono (C.f i)).mp pullback.condition
      rw [he]
    · have : IsEmpty ↥(pullback (C.f i) (C.f j')) := ⟨fun z => by
        have hz := congrArg (fun k : pullback (C.f i) (C.f j') ⟶ O.toScheme =>
          (k z).val) (pullback.condition (f := C.f i) (g := C.f j'))
        simp only [Hom.comp_apply, C, j, homOfLE_apply] at hz
        exact (hd hij).notMem_of_mem_left (pullback.fst (C.f i) (C.f j') z).property
          (hz.symm ▸ (pullback.snd (C.f i) (C.f j') z).property)⟩
      exact isInitialOfIsEmpty.hom_ext _ _
  refine ⟨C.glueMorphisms s hc, ?_, fun i => C.ι_glueMorphisms s hc i⟩
  apply C.hom_ext
  intro i
  rw [← Category.assoc, C.ι_glueMorphisms, hs]
  exact (X.homOfLE_ι (le_iSup U i)).symm

end AlgebraicGeometry.Scheme
