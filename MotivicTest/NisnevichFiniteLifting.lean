/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.NisnevichFiniteLifting
public import Mathlib.Data.ZMod.Basic
public import Lean.Util.CollectAxioms

/-!
# Consumers of whole finite-support Nisnevich lifting

The assumptions are imposed only over the distinguished fiber. MotivicTest retain
the entire canonical pullback, including disconnected and nonreduced
supports. For an empty original fiber the theorem is tested with the empty
étale target, forcing the entire new support to be empty.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MotivicTest.NisnevichFiniteLifting

example {Z V S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p] (s : S)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (hq : ∀ z : Z, p z = s → ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ Function.Bijective (g.residueFieldMap u) ∧
    ∃ b : pullback p g ⟶ V, b ≫ q = pullback.fst p g := by
  obtain ⟨U, g, hg, u, hu, hr, b, hb⟩ := exists_nisnevich_lift_of_isFinite p s q hq
  exact ⟨U, g, hg, u, hu, (ConcreteCategory.isIso_iff_bijective _).mp hr, b, hb⟩

/-- The empty-fiber case removes all support near the chosen base point. -/
theorem empty_fiber_gives_empty_support {Z S : Scheme.{u}}
    (p : Z ⟶ S) [IsFinite p] (s : S) (hs : ∀ z : Z, p z ≠ s) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
      IsEmpty (pullback p g : Scheme) := by
  obtain ⟨U, g, hg, u, hu, hr, b, _⟩ :=
    exists_nisnevich_lift_of_isFinite p s (initial.to Z)
      (fun z hz ↦ (hs z hz).elim)
  exact ⟨U, g, hg, u, hu, hr, ⟨fun x ↦ isEmptyElim (b x)⟩⟩

/-- The actual source can be nonreduced, without discarding its nilpotents. -/
example {V : Scheme} (q : V ⟶ Spec (.of (ZMod 4))) [Etale q] [IsSeparated q]
    (hq : ∀ z : Spec (.of (ZMod 4)),
      ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v)) (s : Spec (.of (ZMod 4))) :
    ∃ (U : Scheme) (g : U ⟶ Spec (.of (ZMod 4))), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback (𝟙 (Spec (.of (ZMod 4)))) g ⟶ V,
      b ≫ q = pullback.fst (𝟙 _) g :=
  exists_nisnevich_lift_of_isFinite (𝟙 _) s q (fun z _ ↦ hq z)

/-- A disconnected finite product support is lifted as a whole. -/
example {R : Type u} [CommRing R] {V : Scheme.{u}}
    (q : V ⟶ Spec (.of (R × R))) [Etale q] [IsSeparated q]
    (hq : ∀ z : Spec (.of (R × R)), ∃ v : V, q v = z ∧ IsIso (q.residueFieldMap v))
    (s : Spec (.of R)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ Spec (.of R)), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback (Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))) g ⟶ V,
      b ≫ q = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))) g := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))
  have : IsFinite p := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  exact exists_nisnevich_lift_of_isFinite p s q (fun z _ ↦ hq z)

example {S : Scheme.{u}} (s : S) (n : ℕ)
    (U : Fin n → Scheme.{u}) (g : ∀ i, U i ⟶ S)
    (hg : ∀ i, Etale (g i)) (u : ∀ i, U i)
    (hu : ∀ i, g i (u i) = s)
    (hr : ∀ i, IsIso ((g i).residueFieldMap (u i))) :
    ∃ (W : Scheme.{u}) (h : W ⟶ S), Etale h ∧
    ∃ w : W, h w = s ∧ IsIso (h.residueFieldMap w) ∧
    ∃ a : ∀ i, W ⟶ U i, (∀ i, a i ≫ g i = h) ∧ (∀ i, a i w = u i) :=
  exists_common_nisnevich_refinement s n U g hg u hu hr

open Lean in
run_cmd do
  for name in #[``Scheme.Hom.isIso_residueFieldMap_pullback_snd,
      ``exists_common_nisnevich_refinement,
      ``Scheme.exists_lift_of_disjoint_openCover,
      ``exists_nisnevich_lift_of_isFinite,
      ``empty_fiber_gives_empty_support] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.NisnevichFiniteLifting
