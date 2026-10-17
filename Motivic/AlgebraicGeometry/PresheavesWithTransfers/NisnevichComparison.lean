/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichSheavesWithTransfers
public import Motivic.AlgebraicGeometry.Correspondences.BinaryCoproducts
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichFiniteDescent
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichCechLocalExactness
public import Motivic.AlgebraicGeometry.Correspondences.NisnevichTopology

/-!
# Comparing Nisnevich descent with and without transfers

The comparison uses actual graph arrows and source-arrow additivity. In
particular no fullness property of the graph functor is assumed.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace Motivic.PresheafWithTransfers

variable {k : Type u} [Field k]

/-- The ordinary singleton sheaf condition implies the corresponding condition
for actual correspondences: compatibility for all correspondences includes
compatibility for graph arrows. -/
theorem isSheafFor_graph_singleton_of_restriction
    (F : (Cor k)ᵒᵖ ⥤ Type v) {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X)
    (hF : Presieve.IsSheafFor ((Cor.graphFunctor k).op ⋙ F) (Presieve.singleton q)) :
    Presieve.IsSheafFor F (Presieve.singleton ((Cor.graphFunctor k).map q)) := by
  rw [Presieve.isSheafFor_singleton] at hF ⊢
  intro s hs
  apply hF s
  intro Z p₁ p₂ hp
  exact hs ((Cor.graphFunctor k).map p₁) ((Cor.graphFunctor k).map p₂)
    (by simpa only [← Functor.map_comp] using congrArg ((Cor.graphFunctor k).map) hp)

/-- Sections on the empty smooth scheme vanish for an additive presheaf with
transfers. This supplies the ordinary empty-family sheaf condition. -/
theorem section_eq_zero_of_isEmpty
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive]
    (E : AddCommGrpCat.{v}) (X : Cor k) [IsEmpty X.toSmoothSite.left]
    (s : E ⟶ F.obj (op X)) : s = 0 := by
  have h : (𝟙 (F.obj (op X))) = 0 := by
    rw [← F.map_id]
    have hzero : (𝟙 (op X)) = 0 := by
      exact congrArg Quiver.Hom.op (Cor.hom_eq_zero_of_isEmpty_source k (𝟙 X))
    rw [hzero, F.map_zero]
  simpa only [Category.comp_id, comp_zero] using congrArg (fun f => s ≫ f) h

/-- An additive presheaf takes the actual binary disjoint union to a product
on sections, with the actual graph restriction maps. -/
theorem binaryCoproduct_sections_bijective
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive]
    (E : AddCommGrpCat.{v}) (X Y : Cor k) :
    Function.Bijective (fun s : E ⟶ F.obj (op (Cor.coproduct k X Y)) =>
      (s ≫ F.map (Cor.coproductInl k X Y).op,
        s ≫ F.map (Cor.coproductInr k X Y).op)) := by
  obtain ⟨p, q, hp, hq, hp', hq', htotal⟩ := Cor.exists_coproduct_projections k X Y
  have recover (s : E ⟶ F.obj (op (Cor.coproduct k X Y))) :
      s = (s ≫ F.map (Cor.coproductInl k X Y).op) ≫ F.map p.op +
        (s ≫ F.map (Cor.coproductInr k X Y).op) ≫ F.map q.op := by
    rw [Category.assoc, Category.assoc, ← Preadditive.comp_add,
      ← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, ← F.map_add, ← op_add,
      htotal, op_id, F.map_id, Category.comp_id]
  constructor
  · intro s t h
    obtain ⟨h₁, h₂⟩ := Prod.mk.inj h
    rw [recover s, recover t, h₁, h₂]
  · rintro ⟨s, t⟩
    refine ⟨s ≫ F.map p.op + t ≫ F.map q.op, ?_⟩
    apply Prod.ext
    · simp only [Preadditive.add_comp, Category.assoc, ← F.map_comp, ← op_comp,
        hp, hq, op_id, op_zero, F.map_id, F.map_zero, Category.comp_id,
        comp_zero, add_zero]
    · simp only [Preadditive.add_comp, Category.assoc, ← F.map_comp, ← op_comp,
        hp', hq', op_id, op_zero, F.map_id, F.map_zero, Category.comp_id,
        comp_zero, zero_add]

/-- The actual finite disjoint union gives a product of section groups.
The zero-component case uses source-arrow additivity at the empty scheme. -/
theorem finiteCoproduct_sections_bijective
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive]
    (E : AddCommGrpCat.{v}) {n : ℕ} (Y : Fin n → SmoothSite (Spec (.of k))) :
    Function.Bijective (fun s : E ⟶ F.obj (op (Cor.mk (SmoothSite.finiteCoproduct Y))) =>
      fun i => s ≫ F.map ((Cor.graphFunctor k).map (SmoothSite.finiteCoproductι Y i)).op) := by
  induction n with
  | zero =>
      constructor
      · intro s t _
        have : IsEmpty (Cor.mk (SmoothSite.finiteCoproduct Y)).toSmoothSite.left :=
          inferInstanceAs (IsEmpty (∅ : Scheme.{u}))
        rw [section_eq_zero_of_isEmpty F E _ s, section_eq_zero_of_isEmpty F E _ t]
      · intro s
        exact ⟨0, funext (fun i => Fin.elim0 i)⟩
  | succ n ih =>
      let Z := SmoothSite.finiteCoproduct (fun i : Fin n => Y i.succ)
      have hb := binaryCoproduct_sections_bijective F E (Cor.mk (Y 0)) (Cor.mk Z)
      constructor
      · intro s t h
        apply hb.injective
        apply Prod.ext
        · exact congrFun h 0
        · apply (ih (fun i : Fin n => Y i.succ)).injective
          funext i
          have hi := congrFun h i.succ
          change s ≫ F.map ((Cor.graphFunctor k).map
            (SmoothSite.finiteCoproductι (fun i : Fin n => Y i.succ) i ≫
              SmoothSite.coproductInr (Y 0) Z)).op =
            t ≫ F.map ((Cor.graphFunctor k).map
            (SmoothSite.finiteCoproductι (fun i : Fin n => Y i.succ) i ≫
              SmoothSite.coproductInr (Y 0) Z)).op at hi
          simpa only [Functor.map_comp, op_comp, Category.assoc, Cor.coproductInr] using hi
      · intro s
        obtain ⟨t, ht⟩ := (ih (fun i : Fin n => Y i.succ)).surjective
          (fun i : Fin n => s i.succ)
        obtain ⟨a, ha⟩ := hb.surjective (s 0, t)
        obtain ⟨ha₁, ha₂⟩ := Prod.mk.inj ha
        refine ⟨a, funext (fun i => ?_)⟩
        refine Fin.cases ha₁ (fun j => ?_) i
        change a ≫ F.map ((Cor.graphFunctor k).map
          (SmoothSite.finiteCoproductι (fun i : Fin n => Y i.succ) j ≫
            SmoothSite.coproductInr (Y 0) Z)).op = s j.succ
        rw [Functor.map_comp, op_comp, F.map_comp, ← Category.assoc]
        change (a ≫ F.map (Cor.coproductInr k (Cor.mk (Y 0)) (Cor.mk Z)).op) ≫ _ = _
        rw [ha₂]
        exact congrFun ht j

/-- Singleton separation implies separation for every actual Nisnevich family,
using a finite total cover and additivity on finite disjoint unions. -/
theorem sections_ext_of_nisnevich_family
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive] (E : AddCommGrpCat.{v})
    (hF : ∀ {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X),
      Etale q.left → (∀ x : X.left, ∃ y : Y.left,
        q.left y = x ∧ IsIso (q.left.residueFieldMap y)) →
      Function.Injective (fun s : E ⟶ F.obj (op (Cor.mk X)) =>
        s ≫ F.map ((Cor.graphFunctor k).map q).op))
    {X : SmoothSite (Spec (.of k))} {ι : Type*}
    {Y : ι → SmoothSite (Spec (.of k))} (f : ∀ i, Y i ⟶ X)
    [∀ i, Etale (f i).left]
    (hf : ∀ x : X.left, ∃ (i : ι) (y : (Y i).left),
      (f i).left y = x ∧ IsIso ((f i).left.residueFieldMap y))
    {s t : E ⟶ F.obj (op (Cor.mk X))}
    (h : ∀ i, s ≫ F.map ((Cor.graphFunctor k).map (f i)).op =
      t ≫ F.map ((Cor.graphFunctor k).map (f i)).op) : s = t := by
  let N := SmoothSite.normalizeFiniteNisnevichCover f hf
  apply hF N.map inferInstance N.residueFieldLifting
  apply (finiteCoproduct_sections_bijective F E (fun i => Y (N.index i))).injective
  funext i
  change (s ≫ F.map ((Cor.graphFunctor k).map N.map).op) ≫
      F.map ((Cor.graphFunctor k).map (N.inclusion i)).op =
    (t ≫ F.map ((Cor.graphFunctor k).map N.map).op) ≫
      F.map ((Cor.graphFunctor k).map (N.inclusion i)).op
  simp only [Category.assoc, ← F.map_comp, ← op_comp, ← Functor.map_comp,
    N.inclusion_map]
  exact h (N.index i)

/-- Pointwise smooth Nisnevich neighborhoods detect equality once actual
singleton-cover restrictions are injective. -/
theorem sections_ext_of_nisnevich_local
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive] (E : AddCommGrpCat.{v})
    (hF : ∀ {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X),
      Etale q.left → (∀ x : X.left, ∃ y : Y.left,
        q.left y = x ∧ IsIso (q.left.residueFieldMap y)) →
      Function.Injective (fun s : E ⟶ F.obj (op (Cor.mk X)) =>
        s ≫ F.map ((Cor.graphFunctor k).map q).op))
    {X : SmoothSite (Spec (.of k))} {s t : E ⟶ F.obj (op (Cor.mk X))}
    (h : ∀ x : X.left, ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X),
      Etale g.left ∧ (∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u)) ∧
      s ≫ F.map ((Cor.graphFunctor k).map g).op =
        t ≫ F.map ((Cor.graphFunctor k).map g).op) : s = t := by
  choose U g hg hu heq using h
  let (x : X.left) : Etale (g x).left := hg x
  exact sections_ext_of_nisnevich_family F E hF g
    (fun x => ⟨x, hu x⟩) heq

/-- Actual local Čech exactness upgrades scheme Čech compatibility to
compatibility for all signed correspondences with the same image. -/
theorem correspondence_compatible_of_cech_compatible
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive] (E : AddCommGrpCat.{v})
    (hF : ∀ {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X),
      Etale q.left → (∀ x : X.left, ∃ y : Y.left,
        q.left y = x ∧ IsIso (q.left.residueFieldMap y)) →
      Function.Injective (fun s : E ⟶ F.obj (op (Cor.mk X)) =>
        s ≫ F.map ((Cor.graphFunctor k).map q).op))
    {Y V : SmoothSite (Spec (.of k))} (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v))
    (s : E ⟶ F.obj (op (Cor.mk V)))
    (hs : s ≫ F.map ((Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q)).op =
      s ≫ F.map ((Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)).op)
    {X : Cor k} (α β : X ⟶ Cor.mk V)
    (hαβ : α ≫ (Cor.graphFunctor k).map q = β ≫ (Cor.graphFunctor k).map q) :
    s ≫ F.map α.op = s ≫ F.map β.op := by
  apply sections_ext_of_nisnevich_local F E hF
  intro x
  have hzero : (α - β) ≫ (Cor.graphFunctor k).map q = 0 := by
    rw [Preadditive.sub_comp, hαβ, sub_self]
  obtain ⟨U, g, hg, u, hu, hgu, δ, hδ⟩ :=
    FiniteCorrespondence.exists_nisnevich_cech_boundary k (α - β) q hq hzero x
  refine ⟨U, g, hg, ⟨u, hu, hgu⟩, ?_⟩
  apply sub_eq_zero.mp
  calc
    (s ≫ F.map α.op) ≫ F.map ((Cor.graphFunctor k).map g).op -
        (s ≫ F.map β.op) ≫ F.map ((Cor.graphFunctor k).map g).op =
      s ≫ F.map ((Cor.graphFunctor k).map g ≫ (α - β)).op := by
        simp only [op_comp, op_sub, F.map_comp, F.map_sub,
          Preadditive.comp_sub, Category.assoc]
    _ = s ≫ F.map
        (δ ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) -
          δ ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)).op := by rw [hδ]
    _ = 0 := by
      simp only [op_sub, F.map_sub, Preadditive.comp_sub, op_comp, F.map_comp,
        ← Category.assoc]
      rw [hs, sub_self]

/-- For an additive presheaf separated on singleton covers, singleton
Nisnevich descent is equivalent before and after restricting to graph arrows. -/
theorem isSheafFor_graph_singleton_iff
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive] (E : AddCommGrpCat.{v})
    (hF : ∀ {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X),
      Etale q.left → (∀ x : X.left, ∃ y : Y.left,
        q.left y = x ∧ IsIso (q.left.residueFieldMap y)) →
      Function.Injective (fun s : E ⟶ F.obj (op (Cor.mk X)) =>
        s ≫ F.map ((Cor.graphFunctor k).map q).op))
    {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X) [Etale q.left]
    (hq : ∀ x : X.left, ∃ y : Y.left,
      q.left y = x ∧ IsIso (q.left.residueFieldMap y)) :
    Presieve.IsSheafFor (F ⋙ coyoneda.obj (op E))
        (Presieve.singleton ((Cor.graphFunctor k).map q)) ↔
      Presieve.IsSheafFor ((Cor.graphFunctor k).op ⋙ F ⋙ coyoneda.obj (op E))
        (Presieve.singleton q) := by
  constructor
  · intro h
    rw [Presieve.isSheafFor_singleton] at h ⊢
    intro s hs
    apply h s
    intro Z α β hαβ
    apply correspondence_compatible_of_cech_compatible F E hF q hq s ?_ α β hαβ
    exact hs (SmoothSite.etalePullbackFst q q) (SmoothSite.etalePullbackSnd q q)
      (SmoothSite.etalePullbackCone q q).condition
  · exact isSheafFor_graph_singleton_of_restriction (F ⋙ coyoneda.obj (op E)) q

/-- A presheaf on actual correspondences is a sheaf for the correspondence
Nisnevich topology exactly when it has descent for genuine singleton graph covers. -/
theorem isSheaf_correspondenceTopology_iff_singletons (F : (Cor k)ᵒᵖ ⥤ Type v) :
    Presieve.IsSheaf (Cor.nisnevichTopology k) F ↔
      ∀ {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X), Cor.IsNisnevichCover k q →
        Presieve.IsSheafFor F (Presieve.singleton ((Cor.graphFunctor k).map q)) := by
  constructor
  · intro h X Y q hq
    exact h.isSheafFor _ (Cor.graph_cover_mem_nisnevichTopology k q hq)
  · intro h X R hR
    obtain ⟨V, q, hq, hRq⟩ := hR
    apply (h q hq).of_singleton hRq
    intro Y α _
    obtain ⟨U, g, hg, β, hβ⟩ := Cor.exists_nisnevich_cover_graph_factorization k α q hq
    exact ⟨Cor.mk U, (Cor.graphFunctor k).map g, β, hβ.symm,
      (h g hg).isSeparatedFor⟩

/-- An ordinary Nisnevich sheaf underlying a transfer presheaf is a sheaf for
actual correspondence sieves. This implication does not require additivity. -/
theorem isSheaf_correspondenceTopology_of_restriction
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v})
    (hF : Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
      ((Cor.graphFunctor k).op ⋙ F)) :
    Presheaf.IsSheaf (Cor.nisnevichTopology k) F := by
  intro E
  apply (isSheaf_correspondenceTopology_iff_singletons (F ⋙ coyoneda.obj (op E))).mpr
  intro X Y q hq
  apply isSheafFor_graph_singleton_of_restriction
  exact (hF E).isSheafFor_of_mem_precoverage
    ((Cor.isNisnevichCover_iff_singleton_mem k q).mp hq)

/-- A correspondence Nisnevich sheaf which is additive in source arrows
has ordinary descent for each genuine singleton Nisnevich cover. -/
theorem isSheafFor_restriction_singleton_of_correspondenceSheaf
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive]
    (hF : Presheaf.IsSheaf (Cor.nisnevichTopology k) F) (E : AddCommGrpCat.{v})
    {X Y : SmoothSite (Spec (.of k))} (q : Y ⟶ X) (hq : Cor.IsNisnevichCover k q) :
    Presieve.IsSheafFor ((Cor.graphFunctor k).op ⋙ F ⋙ coyoneda.obj (op E))
      (Presieve.singleton q) := by
  let : Etale q.left := hq.1
  have hsingle : ∀ {A B : SmoothSite (Spec (.of k))} (r : B ⟶ A),
      Cor.IsNisnevichCover k r → Presieve.IsSheafFor (F ⋙ coyoneda.obj (op E))
        (Presieve.singleton ((Cor.graphFunctor k).map r)) :=
    (isSheaf_correspondenceTopology_iff_singletons
      (F ⋙ coyoneda.obj (op E))).mp (hF E)
  apply (isSheafFor_graph_singleton_iff F E ?_ q hq.2).mp (hsingle q hq)
  intro X Y r hr hr'
  exact Presieve.isSeparatedFor_singleton.mp (hsingle r ⟨hr, hr'⟩).isSeparatedFor

/-- Sheafness for actual correspondence Nisnevich sieves agrees with the
ordinary smooth-site Nisnevich sheaf condition for every additive presheaf.
The proof includes arbitrary covering families and the empty smooth scheme. -/
theorem isSheaf_correspondenceTopology_iff_restriction
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{v}) [F.Additive] :
    Presheaf.IsSheaf (Cor.nisnevichTopology k) F ↔
      Presheaf.IsSheaf (SmoothSite.nisnevichTopology (Spec (.of k)))
        ((Cor.graphFunctor k).op ⋙ F) := by
  constructor
  · intro hF E
    apply (SmoothSite.isSheaf_iff_singleton_of_finiteCoproduct
      ((Cor.graphFunctor k).op ⋙ F ⋙ coyoneda.obj (op E))
      (fun _ Y => finiteCoproduct_sections_bijective F E Y)).mpr
    intro X Y q hq
    exact isSheafFor_restriction_singleton_of_correspondenceSheaf F hF E q
      ((Cor.isNisnevichCover_iff_singleton_mem k q).mpr hq)
  · exact isSheaf_correspondenceTopology_of_restriction F

/-- The project's actual full-subcategory condition for sheaves with transfers
is exactly sheafness on the actual correspondence Nisnevich site. -/
theorem isNisnevichSheaf_iff_correspondenceTopology (P : PresheafWithTransfers.{v} k) :
    IsNisnevichSheaf k P ↔ Presheaf.IsSheaf (Cor.nisnevichTopology k) P.obj :=
  (isSheaf_correspondenceTopology_iff_restriction P.obj).symm

end Motivic.PresheafWithTransfers
