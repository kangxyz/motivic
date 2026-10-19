/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.LocalGeneratorLift
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteLifting

/-!
# Local Nisnevich lifting of signed finite correspondences

The integral-support lifting theorem extends to arbitrary integer coefficients.
A common pointed Nisnevich refinement combines the finitely many summands.
All identities are in the actual finite-correspondence category.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondence
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k]
  {X Y V : SmoothSite (Spec (.of k))}

set_option backward.isDefEq.respectTransparency false in
/-- Every signed finite correspondence lifts through a single smooth-site
Nisnevich covering arrow after a pointed Nisnevich neighborhood of its source. -/
theorem exists_nisnevich_graph_factorization
    (α : Cor.mk X ⟶ Cor.mk Y) (q : V ⟶ Y) [Etale q.left]
    (hq : ∀ y : Y.left, ∃ v : V.left,
      q.left v = y ∧ IsIso (q.left.residueFieldMap v)) (x : X.left) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map g ≫ α := by
  classical
  change FiniteCorrespondence X.hom Y.hom at α
  induction α using Finsupp.induction_linear with
  | zero =>
    refine ⟨X, 𝟙 X, ?_, x, rfl, ?_, 0, ?_⟩
    · change Etale (𝟙 X.left)
      infer_instance
    · change IsIso ((𝟙 X.left : X.left ⟶ X.left).residueFieldMap x)
      infer_instance
    · simp
  | single A n =>
    obtain ⟨U, g, hg, u, hu, hr, β, hβ⟩ :=
      A.exists_nisnevich_graph_factorization k q hq x
    refine ⟨U, g, hg, u, hu, hr, n • β, ?_⟩
    have hn : Finsupp.single A n = n • A.cycle := by
      simp [FiniteCorrespondenceGenerator.cycle]
    rw [hn, Preadditive.zsmul_comp, Preadditive.comp_zsmul, hβ]
  | add α₀ α₁ h₀ h₁ =>
    obtain ⟨U₀, g₀, hg₀, u₀, hu₀, hr₀, β₀, hβ₀⟩ := h₀
    obtain ⟨U₁, g₁, hg₁, u₁, hu₁, hr₁, β₁, hβ₁⟩ := h₁
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
    refine ⟨W, h, hh, w, hw, hwr,
      (Cor.graphFunctor k).map (a 0) ≫ β₀ + (Cor.graphFunctor k).map (a 1) ≫ β₁, ?_⟩
    rw [Preadditive.add_comp, Preadditive.comp_add, Category.assoc, Category.assoc,
      hβ₀, hβ₁, ← Category.assoc, ← Category.assoc,
      ← Functor.map_comp, ← Functor.map_comp]
    have ha₀ : a 0 ≫ g₀ = h := ha 0
    have ha₁ : a 1 ≫ g₁ = h := ha 1
    rw [ha₀, ha₁]

end Motivic.FiniteCorrespondence
