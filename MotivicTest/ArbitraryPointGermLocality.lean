/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.Sheaf.Germs.ArbitraryPointLocality
public import Lean.Util.CollectAxioms

/-! # Signed germ locality at genuinely nonclosed source points -/

noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic

universe u v

variable (k : Type u) [Field k] (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y : SmoothSite (Spec (.of k))}

/-- Strict specialization witnesses a nonclosed source point. The original
signed transfer still depends only on its actual finite target fiber germs. -/
example (α : FiniteCorrespondence X.hom Y.hom)
    (x x' : X.left) (hsp : x ⤳ x') (hne : x ≠ x')
    (s t : P.sections (Cor.mk Y))
    (hst : ∀ A ∈ α.support, ∀ z : A.scheme, A.projection z = x →
      SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
          Y (A.targetProjection z) s =
        SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
          Y (A.targetProjection z) t) :
    ¬ IsClosed ({x} : Set X.left) ∧
    SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
        X x (P.transfer α s) =
      SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
        X x (P.transfer α t) := by
  refine ⟨?_, PresheafWithTransfers.transfer_germ_eq_at_point_of_eq_on_support k P α x s t hst⟩
  intro hc
  exact hne (Set.mem_singleton_iff.mp (hsp.mem_closed hc (Set.mem_singleton x))).symm

/-- Empty selected support fibers are allowed, with no fictitious chosen
center or nonempty indexing assumption. -/
example (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    (hempty : ∀ z : A.scheme, A.projection z ≠ x) (s : P.sections (Cor.mk Y)) :
    SmoothSite.sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
      X x (P.transfer A.cycle s) = 0 := by
  apply PresheafWithTransfers.generator_transfer_germ_eq_zero_at_point k P A x s
  intro z hz
  exact False.elim (hempty z hz)

open Lean  _root_.Motivic.PresheafWithTransfers in
run_cmd do
  for name in #[``generator_transfer_germ_eq_zero_at_point,
      ``transfer_germ_eq_zero_at_point, ``transfer_germ_eq_at_point_of_eq_on_support] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Signed finite-support germ locality includes nonclosed and empty-fiber source points."
