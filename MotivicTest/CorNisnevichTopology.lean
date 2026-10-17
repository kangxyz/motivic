/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichTopology
public import Motivic.Aglib.CategoryTheory.SheafifyAdditive

/-! # Consumers of the actual singleton-cover Nisnevich topology on `Cor` -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u

namespace MotivicTest.CorNisnevichTopology

variable (k : Type u) [Field k]

example (X : Cor k) (R : Sieve X) :
    R ∈ Cor.nisnevichTopology k X ↔
      ∃ (U : SmoothSite (Spec (.of k))) (q : U ⟶ X.toSmoothSite),
        (Etale q.left ∧ ∀ x : X.toSmoothSite.left, ∃ u : U.left,
          q.left u = x ∧ IsIso (q.left.residueFieldMap u)) ∧
          R ((Cor.graphFunctor k).map q) := Cor.mem_nisnevichTopology_iff k

example (X : Cor k) : (⊤ : Sieve X) ∈ Cor.nisnevichTopology k X :=
  (Cor.nisnevichTopology k).top_mem X

example (X : Cor k) : (⊥ : Sieve X) ∉ Cor.nisnevichTopology k X := by
  rintro ⟨_, _, _, h⟩
  exact h

example {X Y V : SmoothSite (Spec (.of k))}
    (α : Cor.mk X ⟶ Cor.mk Y) (q : V ⟶ Y) (hq : Cor.IsNisnevichCover k q) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Cor.IsNisnevichCover k g ∧
      ∃ β : Cor.mk U ⟶ Cor.mk V,
        β ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map g ≫ α :=
  Cor.exists_nisnevich_cover_graph_factorization k α q hq

example {X Y : Cor k} (α : Y ⟶ X) (R : Sieve X)
    (hR : R ∈ Cor.nisnevichTopology k X) :
    R.pullback α ∈ Cor.nisnevichTopology k Y :=
  (Cor.nisnevichTopology k).pullback_stable α hR

example (X : Cor k) (R : Sieve X) (hR : R ∈ Cor.nisnevichTopology k X) :
    ∃ (Y : Cor k) (q : Y ⟶ X), R q ∧
      Sieve.generate (Presieve.singleton q) ∈ Cor.nisnevichTopology k X :=
  Cor.principal_covering_basis k X R hR

example {X U : SmoothSite (Spec (.of k))} (q : U ⟶ X)
    (hq : Cor.IsNisnevichCover k q) :
    Sieve.generate (Presieve.singleton ((Cor.graphFunctor k).map q)) ∈
      Cor.nisnevichTopology k (Cor.mk X) := Cor.graph_cover_mem_nisnevichTopology k q hq

example (X : SmoothSite (Spec (.of k))) (R : Sieve (Cor.mk X))
    (hR : R ∈ Cor.nisnevichTopology k (Cor.mk X)) :
    R.functorPullback (Cor.graphFunctor k) ∈ SmoothSite.nisnevichTopology (Spec (.of k)) X :=
  Cor.graph_functorPullback_mem_nisnevichTopology k hR

example [HasWeakSheafify (Cor.nisnevichTopology k) AddCommGrpCat.{u + 1}]
    [(Cor.nisnevichTopology k).HasSheafCompose (forget AddCommGrpCat.{u + 1})]
    [(Cor.nisnevichTopology k).PreservesSheafification (forget AddCommGrpCat.{u + 1})]
    (F : (Cor k)ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) [F.Additive] :
    (sheafify (Cor.nisnevichTopology k) F).Additive :=
  sheafify_additive_of_principal_covering_basis (Cor.nisnevichTopology k)
    (Cor.principal_covering_basis k) F

end MotivicTest.CorNisnevichTopology
