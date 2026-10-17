/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Transfers.FiniteSupportGermLocality
public import Lean.Util.CollectAxioms

/-!
# Consumers of signed finite-support germ locality

The base field and coefficient universe are arbitrary. The consumers retain
the actual graph restrictions, signed transfer map, and original point fiber.
The equality theorem applies to existing sections; no arbitrary germ-tuple
action or independence of untracked correspondence lifts is assumed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Motivic Motivic.SmoothSite

universe u v w

variable (k : Type u) [Field k] (P : PresheafWithTransfers.{max (u + 1) v} k)
  {X Y : SmoothSite (Spec (.of k))}

example (A : FiniteCorrespondenceGenerator X.hom Y.hom) (x : X.left)
    {I : Type w} (V : I → SmoothSite (Spec (.of k))) (q : ∀ i, V i ⟶ Y)
    [∀ i, Etale (q i).left]
    (hq : ∀ z : A.scheme, A.projection z = x →
      ∃ (i : I) (v : (V i).left), (q i).left v = A.targetProjection z ∧
        IsIso ((q i).left.residueFieldMap v))
    (s : P.sections (Cor.mk Y))
    (hs : ∀ i, P.transfer ((Cor.graphFunctor k).map (q i)) s = 0) :
    ∃ N : NisnevichNeighborhood X x,
      ((PresheafWithTransfers.toPresheaf k).obj P).map N.toBase.op (P.transfer A.cycle s) = 0 :=
  PresheafWithTransfers.exists_restriction_transfer_eq_zero_of_family k P A x V q hq s hs

variable (α : FiniteCorrespondence X.hom Y.hom)
  (x : X.left) (hx : IsClosed ({x} : Set X.left)) (s t : P.sections (Cor.mk Y))

example (hs : ∀ A ∈ α.support, ∀ z : A.scheme, A.projection z = x →
    sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
      Y (A.targetProjection z) s = 0) :
    sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
      X x (P.transfer α s) = 0 :=
  PresheafWithTransfers.transfer_germ_eq_zero k P α x hx s hs

example (hst : ∀ A ∈ α.support, ∀ z : A.scheme, A.projection z = x →
    sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
      Y (A.targetProjection z) s =
    sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
      Y (A.targetProjection z) t) :
    sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
      X x (P.transfer α s) =
    sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
      X x (P.transfer α t) :=
  PresheafWithTransfers.transfer_germ_eq_of_eq_on_support k P α x hx s t hst

example : sectionToNisnevichPoint ((PresheafWithTransfers.toPresheaf k).obj P)
    X x (P.transfer (0 : Cor.mk X ⟶ Cor.mk Y) s) = 0 := by
  apply PresheafWithTransfers.transfer_germ_eq_zero k P
    (0 : FiniteCorrespondence X.hom Y.hom) x hx s
  simp

open Lean in
run_cmd do
  for name in #[``Motivic.PresheafWithTransfers.exists_restriction_transfer_eq_zero_of_family,
      ``Motivic.PresheafWithTransfers.generator_transfer_germ_eq_zero,
      ``Motivic.PresheafWithTransfers.transfer_germ_eq_zero,
      ``Motivic.PresheafWithTransfers.transfer_germ_eq_of_eq_on_support] do
    let dependencies ← collectAxioms name
    for dependency in dependencies do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Signed finite-support germ locality uses only standard Lean foundations."
