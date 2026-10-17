/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.NisnevichFiniteSplitting
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of complete finite Nisnevich splitting

The tests use the canonical scheme-theoretic pullback, its complete clopen
partition, and the actual residue-field map. They include a nonreduced base
and the empty-fiber case; no point or reduced structure is inserted.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.NisnevichFiniteSplitting

/-- Each piece has an actual singleton fiber, while the pieces cover the
whole pulled-back finite support. -/
theorem complete_singleton_fibers {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] (s : S) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ Function.Bijective (g.residueFieldMap u) ∧
    ∃ (n : ℕ) (V : Fin n → (pullback f g).Opens),
      (⨆ i, V i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧
      ∀ i, IsClopen (V i : Set (pullback f g : Scheme)) ∧
        IsFinite ((V i).ι ≫ pullback.snd f g) ∧
        ∃ v : V i, ((V i).ι ≫ pullback.snd f g) ⁻¹' {u} = {v} := by
  obtain ⟨U, g, hg, u, hu, hres, n, V, hfin, hdisj, htop, hfib⟩ :=
    exists_nisnevich_finiteSplitting f s
  refine ⟨U, g, hg, u, hu, (ConcreteCategory.isIso_iff_bijective _).mp hres,
    n, V, htop, hdisj, ?_⟩
  intro i
  obtain ⟨v, hv, huniq⟩ := hfib i
  refine ⟨(hfin i).1, (hfin i).2, v, ?_⟩
  ext z
  change pullback.snd f g z.1 = u ↔ z = v
  exact ⟨huniq z, fun h ↦ h ▸ hv⟩

/-- In the empty-fiber case, completeness forces the entire pulled-back
support to be empty after shrinking. -/
theorem empty_fiber_empty_neighborhood {X S : Scheme.{u}} (f : X ⟶ S)
    [IsFinite f] (s : S) (hs : ∀ x : X, f x ≠ s) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
      IsEmpty (pullback f g : Scheme) := by
  obtain ⟨U, g, hg, u, hu, hres, n, V, hfin, hdisj, htop, hfib⟩ :=
    exists_nisnevich_finiteSplitting f s
  refine ⟨U, g, hg, u, hu, hres, ⟨fun w ↦ ?_⟩⟩
  have hw : w ∈ ⨆ i, V i := by rw [htop]; trivial
  obtain ⟨i, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hw
  obtain ⟨v, hv, _⟩ := hfib i
  apply hs (pullback.fst f g v.1)
  calc
    f (pullback.fst f g v.1) = g (pullback.snd f g v.1) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    _ = s := by rw [hv, hu]

/-- The whole partition theorem applies over the nonreduced ring `ZMod 4`. -/
example {X : Scheme} (f : X ⟶ Spec (.of (ZMod 4))) [IsFinite f]
    (s : Spec (.of (ZMod 4))) :
    ∃ (U : Scheme) (g : U ⟶ Spec (.of (ZMod 4))), Etale g ∧
    ∃ u : U, g u = s ∧ Function.Bijective (g.residueFieldMap u) ∧
    ∃ (n : ℕ) (V : Fin n → (pullback f g).Opens),
      (⨆ i, V i) = ⊤ ∧ Pairwise (fun i j ↦ Disjoint (V i) (V j)) ∧
      ∀ i, IsClopen (V i : Set (pullback f g : Scheme)) ∧
        IsFinite ((V i).ι ≫ pullback.snd f g) ∧
        ∃ v : V i, ((V i).ι ≫ pullback.snd f g) ⁻¹' {u} = {v} :=
  complete_singleton_fibers f s

end Motivic.MotivicTest.NisnevichFiniteSplitting
