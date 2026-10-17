/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichPointChosenLifting

/-!
# Gluing chosen finite-fiber values on an actual point neighborhood

The already constructed finite clopen pieces have actual maps to one common
étale target and controlled values on the chosen source fiber. Glue those
same maps using the existing disjoint-open-cover lemma. The resulting whole
support map retains the prescribed property of the actual input lift points.

No closed-point hypothesis, global target cover, or second lifting engine is
introduced. This uses the existing smooth-site point index and is not a
standalone upstream extraction.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Motivic.SmoothSite.NisnevichNeighborhood

/-- Glue the actual point-preserving finite pieces into one whole-support
lift, preserving a property of the chosen residue-lift witnesses on its fiber. -/
theorem exists_lift_of_isFinite_with_point_property
    {S : Scheme.{u}} [IsAffine S] {X : SmoothSite S} {x : X.left}
    {Z V : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p]
    (q : V ⟶ Z) [Etale q] [IsSeparated q] (Q : V → Prop)
    (hq : ∀ z : Z, p z = x →
      ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v) ∧ Q v) :
    ∃ (N : NisnevichNeighborhood X x) (b : pullback p N.toBase.left ⟶ V),
      b ≫ q = pullback.fst p N.toBase.left ∧
      ∀ t : (pullback p N.toBase.left : Scheme),
        pullback.snd p N.toBase.left t = N.center → Q (b t) := by
  have hq' : ∀ z : Z, p z = x →
      ∃ (_i : Unit) (v : V), q v = z ∧ IsIso (q.residueFieldMap v) ∧ Q v := by
    intro z hz
    obtain ⟨v, hv, hr, hQ⟩ := hq z hz
    exact ⟨(), v, hv, hr, hQ⟩
  obtain ⟨N, n, F, _, hd, htop, _, c, hc⟩ :=
    exists_family_lift_of_isFinite_with_point_property
      p (fun _ : Unit ↦ V) (fun _ ↦ q) (fun _ ↦ Q) hq'
  obtain ⟨b, hb, hres⟩ := Scheme.exists_lift_of_disjoint_openCover
    (pullback.fst p N.toBase.left) q F hd htop c (fun j ↦ (hc j).1)
  refine ⟨N, b, hb, ?_⟩
  intro t ht
  have hcover : t ∈ (⨆ j, F j : (pullback p N.toBase.left).Opens) := by
    rw [htop]
    trivial
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hcover
  let z : (F j).toScheme := ⟨t, hj⟩
  obtain ⟨v, hQ, hval⟩ := (hc j).2
  have he : b t = c j z :=
    congrArg (fun f : (F j).toScheme ⟶ V ↦ f z) (hres j)
  rw [he, hval z ht]
  exact hQ

end Motivic.SmoothSite.NisnevichNeighborhood
