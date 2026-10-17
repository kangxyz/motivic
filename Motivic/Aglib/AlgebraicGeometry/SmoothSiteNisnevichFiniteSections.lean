/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichFiniteDescent
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Limits.Types.Products

/-! # Actual sections on finite disjoint unions in the smooth Nisnevich site -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Motivic.SmoothSite

variable {S : Scheme.{u}}

/-- Sections of an ordinary abelian Nisnevich sheaf on an empty smooth object vanish. -/
theorem section_eq_zero_of_isEmpty
    (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    (X : SmoothSite S) [IsEmpty X.left] (s : F.obj.obj (op X)) : s = 0 := by
  have hbot : (⊥ : Sieve X) ∈ nisnevichTopology S X := by
    apply mem_nisnevichTopology_iff.mpr
    refine ⟨⊥, ?_, le_rfl⟩
    rw [mem_nisnevichPrecoverage_iff, Presieve.map_bot, Nisnevich.mem_precoverage_iff]
    exact ⟨fun _ _ h ↦ False.elim h, fun x ↦ isEmptyElim x⟩
  let G := (sheafCompose (nisnevichTopology S) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F
  let h := Types.isTerminalEquivUnique _ (G.isTerminalOfBotCover X hbot)
  exact (h.uniq s).trans (h.uniq (0 : F.obj.obj (op X))).symm

/-- Two sections on the summands of a disjoint union glue without a compatibility hypothesis. -/
theorem exists_section_coproduct
    (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) (X Y : SmoothSite S)
    (x : F.obj.obj (op X)) (y : F.obj.obj (op Y)) :
    ∃ s : F.obj.obj (op (coproduct X Y)),
      F.obj.map (coproductInl X Y).op s = x ∧ F.obj.map (coproductInr X Y).op s = y := by
  have : Mono (coproductInl X Y) := (forgetScheme S).mono_of_mono_map (by
    change Mono (coproductInl X Y).left
    infer_instance)
  have : Mono (coproductInr X Y) := (forgetScheme S).mono_of_mono_map (by
    change Mono (coproductInr X Y).left
    infer_instance)
  let f : ∀ j, pairFunction X Y j ⟶ coproduct X Y :=
    fun j ↦ WalkingPair.casesOn j (coproductInl X Y) (coproductInr X Y)
  have hf : Presieve.ofArrows _ f ∈ nisnevichPrecoverage S _ := by
    rw [ofArrows_mem_nisnevichPrecoverage_iff]
    refine ⟨fun j ↦ ?_, fun z ↦ ?_⟩
    · cases j <;> infer_instance
    · have hz := (isCompl_range_inl_inr X.left Y.left).sup_eq_top.ge (Set.mem_univ z)
      obtain ⟨a, ha⟩ | ⟨b, hb⟩ := hz
      · exact ⟨WalkingPair.left, a, ha, inferInstance⟩
      · exact ⟨WalkingPair.right, b, hb, inferInstance⟩
  have hcover : Sieve.ofArrows _ f ∈ nisnevichTopology S _ :=
    mem_nisnevichTopology_iff.mpr ⟨_, hf, Sieve.le_generate _⟩
  have hsheaf := ((isSheaf_iff_isSheaf_of_type (nisnevichTopology S) _).mp
    ((sheafCompose (nisnevichTopology S)
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F).property).isSheafFor
        (Presieve.ofArrows _ f) hcover
  let a : ∀ j, F.obj.obj (op (pairFunction X Y j)) := fun j ↦ WalkingPair.casesOn j x y
  have hcompat : Presieve.Arrows.Compatible
      (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) f a := by
    rintro (_ | _) (_ | _) W b c h
    · have : b = c := (cancel_mono (coproductInl X Y)).mp h
      subst c
      rfl
    · have : IsEmpty W.left := ⟨fun w ↦
        (isCompl_range_inl_inr X.left Y.left).disjoint.notMem_of_mem_left
          ⟨b.left w, rfl⟩ ⟨c.left w,
            (congrArg (fun f ↦ f.left w) h).symm⟩⟩
      exact (section_eq_zero_of_isEmpty F W _).trans (section_eq_zero_of_isEmpty F W _).symm
    · have : IsEmpty W.left := ⟨fun w ↦
        (isCompl_range_inl_inr X.left Y.left).disjoint.notMem_of_mem_left
          ⟨c.left w, rfl⟩ ⟨b.left w, congrArg (fun f ↦ f.left w) h⟩⟩
      exact (section_eq_zero_of_isEmpty F W _).trans (section_eq_zero_of_isEmpty F W _).symm
    · have : b = c := (cancel_mono (coproductInr X Y)).mp h
      subst c
      rfl
  obtain ⟨s, hs, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp hsheaf a hcompat
  exact ⟨s, hs WalkingPair.left, hs WalkingPair.right⟩

/-- A finite family of actual sections determines a section on the actual disjoint union. -/
theorem exists_section_finiteCoproduct
    (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1})
    {n : ℕ} (Y : Fin n → SmoothSite S) (s : ∀ i, F.obj.obj (op (Y i))) :
    ∃ t : F.obj.obj (op (finiteCoproduct Y)),
      ∀ i, F.obj.map (finiteCoproductι Y i).op t = s i := by
  induction n with
  | zero => exact ⟨0, fun i ↦ Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih (fun i ↦ Y i.succ) (fun i ↦ s i.succ)
    obtain ⟨a, ha₀, hat⟩ := exists_section_coproduct F (Y 0)
      (finiteCoproduct (fun i ↦ Y i.succ)) (s 0) t
    refine ⟨a, fun i ↦ ?_⟩
    refine Fin.cases ha₀ (fun j ↦ ?_) i
    change F.obj.map ((finiteCoproductι (fun i ↦ Y i.succ) j) ≫
      coproductInr _ _).op a = _
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hat, ht]

end Motivic.SmoothSite
