/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.Point.Lifting
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteFamilyLifting

/-!
# Labeled finite-support lifts in the actual neighborhood index

The existing finite clopen decomposition and every labeled branch map are
retained while the source neighborhood is placed in the actual category used
for the point fiber. The target family can be empty or arbitrarily large.
This geometric consumer still depends on the existing smooth-site modules.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood

set_option backward.isDefEq.respectTransparency false in
/-- A finite clopen partition of the entire support lifts through finitely many
labeled members of a family, over an actual point-fiber neighborhood. -/
theorem exists_family_lift_of_isFinite
    {S : Scheme.{u}} [IsAffine S] {X : SmoothSite S} {x : X.left}
    {I : Type v} {Z : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p]
    (V : I → Scheme.{u}) (q : ∀ i, V i ⟶ Z)
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
    (hq : ∀ z : Z, p z = x →
      ∃ (i : I) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v)) :
    ∃ (N : NisnevichNeighborhood X x) (n : ℕ)
      (F : Fin n → (pullback p N.obj.obj.hom).Opens),
      (∀ j, IsClopen (F j : Set (pullback p N.obj.obj.hom : Scheme)) ∧
        IsFinite ((F j).ι ≫ pullback.snd p N.obj.obj.hom)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧ (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → I) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫ pullback.fst p N.obj.obj.hom := by
  obtain ⟨U, g, hg, u, hu, hr, n, F, hF, hdisj, htop, label, b, hb⟩ :=
    exists_nisnevich_family_lift_of_isFinite X p x V q hq
  exact ⟨ofResidueFieldIso g u hu, n, F, hF, hdisj, htop, label, b, hb⟩

end AlgebraicGeometry.Scheme.SmoothSite.NisnevichNeighborhood
