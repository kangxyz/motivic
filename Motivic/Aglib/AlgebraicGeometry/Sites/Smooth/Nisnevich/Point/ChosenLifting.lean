/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Normalization
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteFamilyLifting

/-!
# Chosen finite-fiber values in the actual Nisnevich point index

The original finite-support lifting construction retains its chosen points
on each clopen piece. Passing to the actual pointed-neighborhood index keeps
these exact values at the distinguished source center. No source or target
point is assumed closed, and target points may specialize to each other.

This smooth-site adapter is not a standalone upstream extraction. It retains
the existing point index and does not construct an envelope or transfer action.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood

set_option backward.isDefEq.respectTransparency false in
/-- Point-indexed finite-support lifting with exact chosen fiber values.
The condition is imposed on the input residue-lift witnesses and transported
by the actual construction to every point of each resulting source fiber. -/
theorem exists_family_lift_of_isFinite_with_point_property
    {S : Scheme.{u}} [IsAffine S] {X : SmoothSite S} {x : X.left}
    {I : Type v} {Z : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p]
    (V : I → Scheme.{u}) (q : ∀ i, V i ⟶ Z) (Q : ∀ i, V i → Prop)
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
    (hq : ∀ z : Z, p z = x →
      ∃ (i : I) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v) ∧ Q i v) :
    ∃ (N : NisnevichNeighborhood X x) (n : ℕ)
      (F : Fin n → (pullback p N.toBase.left).Opens),
      (∀ j, IsClopen (F j : Set (pullback p N.toBase.left : Scheme)) ∧
        IsFinite ((F j).ι ≫ pullback.snd p N.toBase.left)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧ (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → I) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫ pullback.fst p N.toBase.left ∧
        ∃ v : V (label j), Q (label j) v ∧
          ∀ t : (F j).toScheme, ((F j).ι ≫ pullback.snd p N.toBase.left) t = N.center →
            b j t = v := by
  obtain ⟨U, g, hg, u, hu, hr, n, F, hF, hd, ht, label, b, hb⟩ :=
    exists_nisnevich_family_lift_of_isFinite_with_point_property X p x V q Q hq
  let N := ofResidueFieldIso g u hu
  have hcenter : N.center = u := g.left.residueFieldPointLift_apply u hu default
  refine ⟨N, n, F, hF, hd, ht, label, b, ?_⟩
  intro j
  obtain ⟨he, v, hv, hval⟩ := hb j
  refine ⟨he, v, hv, ?_⟩
  intro t ht
  exact hval t (ht.trans hcenter)

end AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood
