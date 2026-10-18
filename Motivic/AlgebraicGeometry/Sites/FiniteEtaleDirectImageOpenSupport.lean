/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Sites.FiniteEtaleFieldObjectEvaluation
public import Motivic.AlgebraicGeometry.Sites.FiniteEtalePointInverseImageComposition

/-! # Actual direct-image fibers away from the source

An étale neighborhood disjoint from the source has empty actual base change.
The empty Nisnevich cover kills sections of any ordinary coefficient sheaf
there. This proves the required outside-support vanishing without an exactness
or closed-support assumption on direct image.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u
namespace Motivic.FiniteEtaleSite
variable {Z U Y : Scheme.{u}} (i : Z ⟶ Y) (j : U ⟶ Y)
  [Etale j] [IsSeparated j] [QuasiCompact j]
  (F : Sheaf (nisnevichTopology Z) AddCommGrpCat.{u + 1})

/-- Actual direct image is zero on every disjoint étale neighborhood, since all
of its test objects have empty base change to the source. -/
theorem etaleRestriction_directImage_isZero_of_disjoint
    (hdisj : Disjoint (Set.range j) (Set.range i)) :
    IsZero ((etaleRestriction j).obj ((directImage i).obj F)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  ext s
  let W := (baseChange i).obj ((etalePostcompose j).obj V.unop)
  have hd : Disjoint (Set.range (V.unop.hom ≫ j)) (Set.range i) :=
    hdisj.mono_left (by
      rintro y ⟨v, rfl⟩
      exact ⟨V.unop.hom v, rfl⟩)
  let : IsEmpty W.left := Scheme.isEmpty_pullback (V.unop.hom ≫ j) i hd
  have hsub : Subsingleton (F.obj.obj (op W)) :=
    sections_subsingleton_of_isEmpty (F.obj ⋙ forget _)
      ((isSheaf_iff_isSheaf_of_type _ _).mp
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget _) F.property)) W
  change (s : F.obj.obj (op W)) = 0
  exact @Subsingleton.elim (F.obj.obj (op W)) hsub s 0

/-- The same vanishing concerns the genuine inverse image, not merely a chosen
presheaf restriction model. -/
theorem inverseImage_directImage_isZero_of_disjoint
    (hdisj : Disjoint (Set.range j) (Set.range i)) :
    IsZero ((inverseImage j).obj ((directImage i).obj F)) :=
  (etaleRestriction_directImage_isZero_of_disjoint i j F hdisj).of_iso
    ((inverseImageEtaleIso j).app ((directImage i).obj F))

section Open
variable [IsOpenImmersion j]

/-- A full field-valued mark lying in a disjoint actual open has zero direct-image
fiber. Its field and its original morphism are retained unchanged. -/
theorem fieldPoint_directImage_isZero_of_mem_disjoint_open
    (hdisj : Disjoint (Set.range j) (Set.range i))
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y) (p : Spec (.of K))
    (hb : b p ∈ Set.range j) :
    IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj ((directImage i).obj F)) :=
  fieldPoint_isZero_of_inverseImage_of_mem_range j K ((directImage i).obj F) b p hb
    (inverseImage_directImage_isZero_of_disjoint i j F hdisj)

/-- The outside-support fiber vanishes for an actual quasi-compact open
complement. No closed-direct-image exactness is used. -/
theorem fieldPoint_directImage_isZero_of_not_mem_range
    (hcomp : Set.range i = (Set.range j)ᶜ)
    (K : Type u) [Field K] (b : Spec (.of K) ⟶ Y) (p : Spec (.of K))
    (hb : b p ∉ Set.range i) :
    IsZero ((relativeFieldPoint b K (𝟙 _)).sheafFiber.obj ((directImage i).obj F)) := by
  classical
  have hdisj : Disjoint (Set.range j) (Set.range i) := by
    rw [hcomp]
    exact disjoint_compl_right
  have hmem : b p ∈ Set.range j := by
    simpa only [hcomp, Set.mem_compl_iff, not_not] using hb
  exact fieldPoint_directImage_isZero_of_mem_disjoint_open i j F hdisj K b p hmem

end Open
end Motivic.FiniteEtaleSite
