/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Nisnevich.Lifting.FiniteFamilyLifting
public import Lean.Util.CollectAxioms

/-! # Exact chosen residue-lift values on finite support fibers at arbitrary points -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

example {Z V S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p]
    (s : S) (z : Z) (hz : p z = s) (huniq : ∀ z' : Z, p z' = s → z' = z)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (v : V) (hv : q v = z) (hres : IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback p g ⟶ V, b ≫ q = pullback.fst p g ∧
      ∀ t : (pullback p g : Scheme), pullback.snd p g t = u → b t = v :=
  exists_nisnevich_lift_of_isFinite_singleton_with_point p s z hz huniq q v hv hres

/-- Exact prescribed points, rather than merely some points in the same fibers,
survive every clopen branch and common refinement. No point is assumed closed. -/
example {I : Type v} {Z S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p] (s : S)
    (V : I → Scheme.{u}) (q : ∀ i, V i ⟶ Z)
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)] (chosen : ∀ i, V i)
    (hq : ∀ z : Z, p z = s →
      ∃ i : I, q i (chosen i) = z ∧ IsIso ((q i).residueFieldMap (chosen i))) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ (n : ℕ) (F : Fin n → (pullback p g).Opens),
      (∀ j, IsClopen (F j : Set (pullback p g : Scheme)) ∧
        IsFinite ((F j).ι ≫ pullback.snd p g)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧ (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → I) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫ pullback.fst p g ∧
        ∀ t : (F j).toScheme, ((F j).ι ≫ pullback.snd p g) t = u →
          b j t = chosen (label j) := by
  have hq' : ∀ z : Z, p z = s → ∃ (i : I) (v : V i),
      q i v = z ∧ IsIso ((q i).residueFieldMap v) ∧ v = chosen i := by
    intro z hz
    obtain ⟨i, hi, hr⟩ := hq z hz
    exact ⟨i, chosen i, hi, hr, rfl⟩
  obtain ⟨U, g, hg, u, hu, hr, n, F, hF, hd, ht, label, b, hb⟩ :=
    exists_nisnevich_family_lift_of_isFinite_with_point_property
      p s V q (fun i v ↦ v = chosen i) hq'
  refine ⟨U, g, hg, u, hu, hr, n, F, hF, hd, ht, label, b, ?_⟩
  intro j
  obtain ⟨he, v, hv, hval⟩ := hb j
  exact ⟨he, fun t htu ↦ (hval t htu).trans hv⟩

open Lean in
run_cmd do
  for name in #[``exists_nisnevich_lift_of_isFinite_singleton_with_point,
      ``exists_nisnevich_family_lift_of_isFinite_with_point_property,
      ``exists_nisnevich_lift_of_isFinite_singleton,
      ``exists_nisnevich_family_lift_of_isFinite] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Finite support lifting retains exact chosen points at arbitrary source points."
