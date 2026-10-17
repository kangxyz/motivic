/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyGenericOpen
public import Motivic.AlgebraicGeometry.SmoothSiteNormal
public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichFiniteSections

/-! # Ordinary quotient sections lift on an open containing every component generic

The construction glues actual sheaf sections on disjoint integral components.
It never treats a positive-cohomology presheaf as a sheaf.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u v

namespace Motivic.SmoothSite

variable {S : Scheme.{u}} [IsNoetherian S]

/-- Local lifts on disjoint open subschemes glue on their actual union. -/
theorem exists_section_lift_on_disjoint_open_union
    {I Q : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}}
    (φ : I ⟶ Q) (X : SmoothSite S) (s : Q.obj.obj (op X))
    {ι : Type v} (A : ι → SmoothSite S) (j : ∀ i, A i ⟶ X)
    [∀ i, IsOpenImmersion (j i).left]
    (hd : Pairwise fun i i' => Disjoint (Set.range (j i).left) (Set.range (j i').left))
    (l : ∀ i, I.obj.obj (op (A i)))
    (hl : ∀ i, φ.hom.app (op (A i)) (l i) = Q.obj.map (j i).op s) :
    ∃ t : I.obj.obj (op ((opensFunctor X).obj (⨆ i, (j i).left.opensRange))),
      φ.hom.app (op ((opensFunctor X).obj (⨆ i, (j i).left.opensRange))) t =
        Q.obj.map (openInclusion X (⨆ i, (j i).left.opensRange)).op s := by
  classical
  let O : X.left.Opens := ⨆ i, (j i).left.opensRange
  let Y := (opensFunctor X).obj O
  have hjO (i : ι) : Set.range (j i).left ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    exact le_iSup (fun i => (j i).left.opensRange) i
  let r (i : ι) : A i ⟶ Y := homMk
    (IsOpenImmersion.lift O.ι (j i).left (hjO i)) (by
      change IsOpenImmersion.lift O.ι (j i).left (hjO i) ≫ (O.ι ≫ X.hom) = _
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact MorphismProperty.Over.w (j i))
  have hr (i : ι) : r i ≫ openInclusion X O = j i := by
    apply MorphismProperty.Over.Hom.ext
    exact IsOpenImmersion.lift_fac _ _ _
  have (i : ι) : IsOpenImmersion (r i).left := by dsimp [r]; infer_instance
  have (i : ι) : Mono (r i) := (forgetScheme S).mono_of_mono_map (by
    change Mono (r i).left
    infer_instance)
  have hcover : Sieve.ofArrows A r ∈ nisnevichTopology S Y := by
    apply mem_nisnevichTopology_iff.mpr
    refine ⟨_, ?_, Sieve.le_generate _⟩
    rw [ofArrows_mem_nisnevichPrecoverage_iff]
    refine ⟨fun i => inferInstance, fun y => ?_⟩
    change O.toScheme at y
    have hy : y.val ∈ O := y.property
    obtain ⟨i, a, ha⟩ := (show ∃ i, ∃ a, (j i).left a = y.val from by
      simpa only [O, Opens.mem_iSup, Scheme.Hom.mem_opensRange] using hy)
    refine ⟨i, a, ?_, inferInstance⟩
    apply Subtype.ext
    exact (congrArg (fun f => f.left a) (hr i)).trans ha
  have hsheaf (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}) :
      Presieve.IsSheafFor (F.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1})
        (Presieve.ofArrows A r) :=
    ((isSheaf_iff_isSheaf_of_type (nisnevichTopology S) _).mp
      ((sheafCompose (nisnevichTopology S)
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F).property).isSheafFor
          (Presieve.ofArrows A r) hcover
  have hcompat : Presieve.Arrows.Compatible
      (I.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u + 1}) r l := by
    intro i i' W a b hab
    by_cases hii : i = i'
    · subst i'
      have : a = b := (cancel_mono (r i)).mp hab
      subst b
      rfl
    · have hcomp : a ≫ j i = b ≫ j i' := by
        rw [← hr i, ← hr i', ← Category.assoc, ← Category.assoc, hab]
      let : IsEmpty W.left := ⟨fun w =>
        (hd hii).notMem_of_mem_left ⟨a.left w, rfl⟩
          ⟨b.left w, (congrArg (fun f => f.left w) hcomp).symm⟩⟩
      exact (section_eq_zero_of_isEmpty I W _).trans
        (section_eq_zero_of_isEmpty I W _).symm
  obtain ⟨t, ht, _⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp (hsheaf I) l hcompat
  change ∀ i, I.obj.map (r i).op t = l i at ht
  refine ⟨t, ?_⟩
  apply (hsheaf Q).isSeparatedFor.ext
  rintro W f ⟨i⟩
  change Q.obj.map (r i).op (φ.hom.app (op ((opensFunctor X).obj O)) t) =
    Q.obj.map (r i).op (Q.obj.map (openInclusion X O).op s)
  rw [← φ.hom.naturality_apply, ht, hl,
    ← Functor.map_comp_apply, ← op_comp, hr]

/-- On an integral model an epimorphic ordinary sheaf section lifts on an
actual generic-containing open. -/
theorem exists_generic_open_section_lift
    {I Q : Sheaf (nisnevichTopology S) AddCommGrpCat.{u + 1}}
    (φ : I ⟶ Q) [Epi φ] (X : SmoothSite S) [IsIntegral X.left]
    (s : Q.obj.obj (op X)) :
    ∃ O : X.left.Opens, genericPoint X.left ∈ O ∧
      ∃ l : I.obj.obj (op ((opensFunctor X).obj O)),
        φ.hom.app (op ((opensFunctor X).obj O)) l =
          Q.obj.map (openInclusion X O).op s := by
  have : Sheaf.IsLocallySurjective φ :=
    (Sheaf.isLocallySurjective_iff_epi' (J := nisnevichTopology S)
      AddCommGrpCat.{u + 1} φ).mpr inferInstance
  obtain ⟨O, hO, hl⟩ := exists_generic_open_mem_covering_sieve X _
    (Presheaf.imageSieve_mem (nisnevichTopology S) φ.hom s)
  exact ⟨O, hO, hl⟩

/-- Every ordinary epimorphic section on a smooth model over an arbitrary
field lifts on a constructed open containing all component generic points.
Empty and disconnected models are included. -/
theorem exists_all_generic_open_section_lift
    {k : Type u} [Field k]
    {I Q : Sheaf (nisnevichTopology (Spec (.of k))) AddCommGrpCat.{u + 1}}
    (φ : I ⟶ Q) [Epi φ] (X : SmoothSite (Spec (.of k)))
    (s : Q.obj.obj (op X)) :
    ∃ O : X.left.Opens, genericPoints X.left ⊆ (O : Set X.left) ∧
      ∃ l : I.obj.obj (op ((opensFunctor X).obj O)),
        φ.hom.app (op ((opensFunctor X).obj O)) l =
          Q.obj.map (openInclusion X O).op s := by
  classical
  let C := componentOpenCover k X
  let B (i : C.I₀) : SmoothSite (Spec (.of k)) := mk (C.f i ≫ X.hom)
  let c (i : C.I₀) : B i ⟶ X := homMk (C.f i) rfl
  have (i : C.I₀) : IsIntegral (B i).left := by dsimp [B, C]; infer_instance
  have hex (i : C.I₀) := exists_generic_open_section_lift φ (B i) (Q.obj.map (c i).op s)
  choose O hO l hl using hex
  let A (i : C.I₀) := (opensFunctor (B i)).obj (O i)
  let j (i : C.I₀) : A i ⟶ X := openInclusion (B i) (O i) ≫ c i
  have (i : C.I₀) : IsOpenImmersion (j i).left := by
    change IsOpenImmersion ((O i).ι ≫ C.f i)
    infer_instance
  have hrange (i : C.I₀) : Set.range (C.f i) = i.val :=
    range_domainStalkComponentOpen_ι (fun _ => inferInstance) i.val i.property
  have hjrange (i : C.I₀) : Set.range (j i).left ⊆ i.val := by
    rintro _ ⟨a, rfl⟩
    rw [← hrange i]
    exact ⟨(O i).ι a, rfl⟩
  have hd : Pairwise fun i i' => Disjoint (Set.range (j i).left) (Set.range (j i').left) := by
    intro i i' hii
    apply ((pairwiseDisjoint_irreducibleComponents k X) i.property i'.property ?_).mono
      (hjrange i) (hjrange i')
    exact fun h => hii (Subtype.ext h)
  have hl' (i : C.I₀) : φ.hom.app (op (A i)) (l i) = Q.obj.map (j i).op s := by
    rw [hl]
    simp only [j, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rfl
  obtain ⟨t, ht⟩ := exists_section_lift_on_disjoint_open_union φ X s A j hd l hl'
  refine ⟨⨆ i, (j i).left.opensRange, ?_, t, ht⟩
  intro x hx
  let i : C.I₀ := ⟨closure ({x} : Set X.left), hx⟩
  have hη : IsGenericPoint ((C.f i) (genericPoint (C.X i))) (closure ({x} : Set X.left)) := by
    have h := (genericPoint_spec (C.X i)).image (C.f i).continuous
    simpa only [Set.image_univ, hrange i, i, closure_closure] using h
  have heq : (C.f i) (genericPoint (C.X i)) = x := hη.eq isGenericPoint_closure
  apply (le_iSup (fun i => (j i).left.opensRange) i)
  exact ⟨⟨genericPoint (C.X i), hO i⟩, heq⟩

end Motivic.SmoothSite
