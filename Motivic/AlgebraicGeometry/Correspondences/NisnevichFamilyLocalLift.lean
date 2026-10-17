/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.NisnevichFamilyGeneratorLift
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichFiniteFamilyLifting
public import Motivic.AlgebraicGeometry.SmoothSiteNisnevichFiniteLifting
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Local lifting of signed correspondences through Nisnevich families

An arbitrary Nisnevich family admits local lifts of every finite correspondence.
Only finitely many branches are used after a pointed refinement of the source;
the family itself may be infinite or empty and branch labels may repeat.
The equalities are in the actual finite-correspondence category, including
all integer coefficients and incidence multiplicities.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace Motivic.FiniteCorrespondenceGenerator

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- A generator lifts through finitely many branches of an arbitrary Nisnevich
family after an actual pointed smooth-site Nisnevich neighborhood. -/
theorem exists_nisnevich_graph_family_factorization
    (A : FiniteCorrespondenceGenerator X.hom Y.hom)
    {I : Type v} (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y)
    [∀ i, Etale (q i).left]
    (hq : ∀ y : Y.left, ∃ (i : I) (v : (V i).left),
      (q i).left v = y ∧ IsIso ((q i).left.residueFieldMap v)) (x : X.left) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ (n : ℕ) (label : Fin n → I) (β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map g ≫ A.cycle := by
  let P (i : I) : Scheme := pullback A.targetProjection (q i).left
  let r (i : I) : P i ⟶ A.scheme := pullback.fst A.targetProjection (q i).left
  have : ∀ i, Etale (r i) := by intro i; dsimp [r, P]; infer_instance
  have : ∀ i, IsSeparated (r i) := by intro i; dsimp [r, P]; infer_instance
  have hr : ∀ z : A.scheme, A.projection z = x →
      ∃ (i : I) (v : P i), r i v = z ∧ IsIso ((r i).residueFieldMap v) := by
    intro z _
    obtain ⟨i, v, hv, hres⟩ := hq (A.targetProjection z)
    have := hres
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := A.targetProjection) (g := (q i).left) z v hv.symm
    refine ⟨i, w, hw₁, ?_⟩
    exact A.targetProjection.isIso_residueFieldMap_pullback_fst (q i).left v w hw₂
  obtain ⟨U, g, hg, u, hu, hgu, n, F, hF, _, hFtop, label, b₀, hb₀⟩ :=
    SmoothSite.exists_nisnevich_family_lift_of_isFinite
      X A.projection x P r hr
  let b (j : Fin n) : (F j).toScheme ⟶ (V (label j)).left :=
    b₀ j ≫ pullback.snd A.targetProjection (q (label j)).left
  have hb (j : Fin n) : b j ≫ (q (label j)).left =
      (F j).ι ≫ pullback.fst A.projection g.left ≫ A.targetProjection := by
    dsimp only [b]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hb₀]
    simp only [Category.assoc]
  obtain ⟨β, hβ⟩ := A.exists_graph_family_factorization_of_support_lift k g V q n F
    (fun j ↦ (hF j).1.1) hFtop label b hb
  exact ⟨U, g, hg, u, hu, hgu, n, label, β, hβ⟩

end Motivic.FiniteCorrespondenceGenerator

namespace Motivic.FiniteCorrespondence

variable (k : Type u) [Field k] {X Y : SmoothSite (Spec (.of k))}

/-- The zero correspondence uses no branches, even when the target family is
empty and no covering hypothesis is available. -/
theorem exists_nisnevich_graph_family_factorization_zero
    {I : Type v} (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y) (x : X.left) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ (label : Fin 0 → I) (β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map g ≫ (0 : Cor.mk X ⟶ Cor.mk Y) := by
  refine ⟨X, 𝟙 X, ?_, x, rfl, ?_, Fin.elim0, (fun j ↦ Fin.elim0 j), ?_⟩
  · change Etale (𝟙 X.left)
    infer_instance
  · change IsIso ((𝟙 X.left : X.left ⟶ X.left).residueFieldMap x)
    infer_instance
  · simp

/-- Every signed finite correspondence lifts through finitely many branches
of an arbitrary Nisnevich covering family after a pointed refinement of its
source. There is no finiteness or nonemptiness assumption on the index type,
and the finite branch labels are not required to be distinct. -/
theorem exists_nisnevich_graph_family_factorization
    (α : Cor.mk X ⟶ Cor.mk Y)
    {I : Type v} (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y)
    [∀ i, Etale (q i).left]
    (hq : ∀ y : Y.left, ∃ (i : I) (v : (V i).left),
      (q i).left v = y ∧ IsIso ((q i).left.residueFieldMap v)) (x : X.left) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ (n : ℕ) (label : Fin n → I) (β : ∀ j, Cor.mk U ⟶ Cor.mk (V (label j))),
      (∑ j, β j ≫ (Cor.graphFunctor k).map (q (label j))) =
        (Cor.graphFunctor k).map g ≫ α := by
  classical
  change FiniteCorrespondence X.hom Y.hom at α
  induction α using Finsupp.induction_linear with
  | zero =>
    obtain ⟨U, g, hg, u, hu, hr, label, β, hβ⟩ :=
      exists_nisnevich_graph_family_factorization_zero k V q x
    exact ⟨U, g, hg, u, hu, hr, 0, label, β, hβ⟩
  | single A c =>
    obtain ⟨U, g, hg, u, hu, hr, n, label, β, hβ⟩ :=
      A.exists_nisnevich_graph_family_factorization k V q hq x
    refine ⟨U, g, hg, u, hu, hr, n, label, fun j ↦ c • β j, ?_⟩
    have hc : Finsupp.single A c = c • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hc, Preadditive.comp_zsmul, ← hβ, Finset.smul_sum]
    simp only [Preadditive.zsmul_comp]
  | add α₀ α₁ h₀ h₁ =>
    obtain ⟨U₀, g₀, hg₀, u₀, hu₀, hr₀, n₀, label₀, β₀, hβ₀⟩ := h₀
    obtain ⟨U₁, g₁, hg₁, u₁, hu₁, hr₁, n₁, label₁, β₁, hβ₁⟩ := h₁
    let Us : Fin 2 → SmoothSite (Spec (.of k)) := ![U₀, U₁]
    let gs : ∀ i, Us i ⟶ X :=
      Fin.cases g₀ (fun i ↦ Fin.cases g₁ (fun j ↦ Fin.elim0 j) i)
    let us : ∀ i, (Us i).left :=
      Fin.cases u₀ (fun i ↦ Fin.cases u₁ (fun j ↦ Fin.elim0 j) i)
    have hgs (i : Fin 2) : Etale (gs i).left := by
      fin_cases i <;> assumption
    have hus (i : Fin 2) : (gs i).left (us i) = x := by
      fin_cases i <;> assumption
    have hrs (i : Fin 2) : IsIso ((gs i).left.residueFieldMap (us i)) := by
      fin_cases i <;> assumption
    obtain ⟨W, h, hh, w, hw, hwr, a, ha, -⟩ :=
      SmoothSite.exists_common_nisnevich_refinement X x 2 Us gs hgs us hus hrs
    let branches₀ (j : Fin n₀) : Σ i : I, Cor.mk W ⟶ Cor.mk (V i) :=
      ⟨label₀ j, (Cor.graphFunctor k).map (a 0) ≫ β₀ j⟩
    let branches₁ (j : Fin n₁) : Σ i : I, Cor.mk W ⟶ Cor.mk (V i) :=
      ⟨label₁ j, (Cor.graphFunctor k).map (a 1) ≫ β₁ j⟩
    let branches := Fin.append branches₀ branches₁
    let evalBranch (b : Σ i : I, Cor.mk W ⟶ Cor.mk (V i)) : Cor.mk W ⟶ Cor.mk Y :=
      b.2 ≫ (Cor.graphFunctor k).map (q b.1)
    refine ⟨W, h, hh, w, hw, hwr, n₀ + n₁,
      fun j ↦ (branches j).1, fun j ↦ (branches j).2, ?_⟩
    have ha₀ : a 0 ≫ g₀ = h := ha 0
    have ha₁ : a 1 ≫ g₁ = h := ha 1
    change (∑ j, evalBranch (branches j)) = (Cor.graphFunctor k).map h ≫ (α₀ + α₁)
    rw [Fin.sum_univ_add]
    simp only [branches, Fin.append_left, Fin.append_right]
    change (∑ j, ((Cor.graphFunctor k).map (a 0) ≫ β₀ j) ≫
        (Cor.graphFunctor k).map (q (label₀ j))) +
      (∑ j, ((Cor.graphFunctor k).map (a 1) ≫ β₁ j) ≫
        (Cor.graphFunctor k).map (q (label₁ j))) = _
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum, ← Preadditive.comp_sum, hβ₀, hβ₁,
      ← Category.assoc, ← Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      ha₀, ha₁, Preadditive.comp_add]

end Motivic.FiniteCorrespondence
