/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.GeneratorLift
public import Motivic.AlgebraicGeometry.Correspondences.Graph.Functor
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteLifting

/-!
# Local generator lifting through one Nisnevich morphism

The entire finite support is lifted through the actual base-changed target
cover. The resulting pointed neighborhood is an actual smooth-site object.
The correspondence factorization retains the original incidence Tor weights.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.FiniteCorrespondenceGenerator
open _root_.AlgebraicGeometry.Scheme

variable (k : Type u) [Field k] {X Y V : SmoothSite (Spec (.of k))}
  (A : FiniteCorrespondenceGenerator X.hom Y.hom)
  (q : V ⟶ Y) [Etale q.left]
  (hq : ∀ y : Y.left, ∃ v : V.left, q.left v = y ∧ IsIso (q.left.residueFieldMap v))
  (x : X.left)

include hq in
/-- A generator lifts locally through a single smooth Nisnevich morphism,
on a genuine pointed smooth Nisnevich neighborhood of every source point. -/
theorem exists_nisnevich_graph_factorization :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ β : Cor.mk U ⟶ Cor.mk V,
      β ≫ (Cor.graphFunctor k).map q = (Cor.graphFunctor k).map g ≫ A.cycle := by
  let r : pullback A.targetProjection q.left ⟶ A.scheme :=
    pullback.fst A.targetProjection q.left
  have : Etale r := by dsimp [r]; infer_instance
  have : IsSeparated r := by dsimp [r]; infer_instance
  have hr : ∀ z : A.scheme, A.projection z = x →
      ∃ v : (pullback A.targetProjection q.left : Scheme),
        r v = z ∧ IsIso (r.residueFieldMap v) := by
    intro z _
    obtain ⟨v, hv, hres⟩ := hq (A.targetProjection z)
    have := hres
    obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := A.targetProjection) (g := q.left) z v hv.symm
    refine ⟨w, hw₁, ?_⟩
    exact A.targetProjection.isIso_residueFieldMap_pullback_fst q.left v w hw₂
  obtain ⟨U, g, hg, u, hu, hgu, b₀, hb₀⟩ :=
    SmoothSite.exists_nisnevich_lift_of_isFinite (S := Spec (.of k))
      X A.projection x r hr
  let b : pullback A.projection g.left ⟶ V.left :=
    b₀ ≫ pullback.snd A.targetProjection q.left
  have hb : b ≫ q.left = pullback.fst A.projection g.left ≫ A.targetProjection := by
    dsimp only [b]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hb₀]
  obtain ⟨β, hβ⟩ := A.exists_graph_factorization_of_support_lift k g q b hb
  exact ⟨U, g, hg, u, hu, hgu, β, hβ⟩

end Motivic.FiniteCorrespondenceGenerator
