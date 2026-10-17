/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.Additive

/-! # Zero-preserving functors commute with extension of complexes -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Motivic.MapExtension

variable {C D ι ι' : Type*} [Category* C] [Category* D]
  [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroObject C] [HasZeroObject D]
  {c : ComplexShape ι} {c' : ComplexShape ι'}
  (F : C ⥤ D) [F.PreservesZeroMorphisms] (e : c.Embedding c')
  (K : HomologicalComplex C c)

/-- Component of the comparison, including the unoccupied zero terms. -/
def componentIso (j : ι') :
    F.obj ((K.extend e).X j) ≅
      (((F.mapHomologicalComplex c).obj K).extend e).X j := by
  classical
  by_cases h : ∃ i, e.f i = j
  · exact F.mapIso (K.extendXIso e h.choose_spec) ≪≫
      (((F.mapHomologicalComplex c).obj K).extendXIso e h.choose_spec).symm
  · exact IsZero.iso (F.map_isZero (K.isZero_extend_X e j (by simpa using h)))
      (((F.mapHomologicalComplex c).obj K).isZero_extend_X e j (by simpa using h))

lemma componentIso_hom {i : ι} {j : ι'} (h : e.f i = j) :
    (componentIso F e K j).hom =
      F.map (K.extendXIso e h).hom ≫
        (((F.mapHomologicalComplex c).obj K).extendXIso e h).inv := by
  classical
  have he : ∃ i, e.f i = j := ⟨i, h⟩
  have hi : he.choose = i := e.injective_f (he.choose_spec.trans h.symm)
  simp only [componentIso, dite_eq_left he, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  subst i
  rfl

/-- A full chain isomorphism, not just an identification of the individual terms. -/
def iso :
    (F.mapHomologicalComplex c').obj (K.extend e) ≅
      ((F.mapHomologicalComplex c).obj K).extend e := by
  classical
  refine HomologicalComplex.Hom.isoOfComponents (componentIso F e K) ?_
  intro i j _
  by_cases hi : ∃ a, e.f a = i
  · obtain ⟨a, rfl⟩ := hi
    by_cases hj : ∃ b, e.f b = j
    · obtain ⟨b, rfl⟩ := hj
      simp only [Functor.mapHomologicalComplex_obj_d, componentIso_hom F e K rfl,
        HomologicalComplex.extend_d_eq _ e rfl rfl, Functor.map_comp,
        Category.assoc, Iso.inv_hom_id_assoc]
      rw [← F.map_comp_assoc (K.extendXIso e (rfl : e.f b = e.f b)).inv,
        Iso.inv_hom_id, F.map_id, Category.id_comp]
    · exact (((F.mapHomologicalComplex c).obj K).isZero_extend_X e j
        (by simpa using hj)).eq_of_tgt _ _
  · exact (F.map_isZero (K.isZero_extend_X e i (by simpa using hi))).eq_of_src _ _

end Motivic.MapExtension
