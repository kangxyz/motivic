/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.FiniteFamilyLifting
public import Mathlib.Data.ZMod.Basic
public import Lean.Util.CollectAxioms

/-!
# Consumers of smooth-site arbitrary-family finite-support lifting

These tests retain actual branch maps on a complete finite clopen partition
and the smooth, separated, finite-type structure of the pointed neighborhood.
They allow unrestricted index universes, empty target families, nonreduced
support, and disconnected finite support.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace MotivicTest.SmoothSiteNisnevichFiniteFamilyLifting

/-- All smooth-site structure and every piece of the finite partition are
retained for an arbitrary family over a field. -/
theorem field_family_lift {k : Type u} [Field k] (X : SmoothSite (Spec (.of k)))
    {I : Type v} {Z : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p] (x : X.left)
    (V : I → Scheme.{u}) (q : ∀ i, V i ⟶ Z)
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
    (hq : ∀ z : Z, p z = x →
      ∃ (i : I) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v)) :
    ∃ (U : SmoothSite (Spec (.of k))) (g : U ⟶ X),
      Smooth U.hom ∧ IsSeparated U.hom ∧ LocallyOfFiniteType U.hom ∧
      QuasiCompact U.hom ∧ Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ Function.Bijective (g.left.residueFieldMap u) ∧
    ∃ (n : ℕ) (F : Fin n → (pullback p g.left).Opens),
      (∀ j, IsClopen (F j : Set (pullback p g.left : Scheme)) ∧
        IsFinite ((F j).ι ≫ pullback.snd p g.left)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧ (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → I) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫ pullback.fst p g.left := by
  obtain ⟨U, g, hg, u, hu, hr, n, F, hF, hd, ht, label, b, hb⟩ :=
    SmoothSite.exists_nisnevich_family_lift_of_isFinite X p x V q hq
  exact ⟨U, g, inferInstance, inferInstance, inferInstance, inferInstance, hg,
    u, hu, (ConcreteCategory.isIso_iff_bijective _).mp hr, n, F, hF, hd, ht, label, b, hb⟩

/-- An empty target family forces zero pieces and empty support without
leaving the smooth site. -/
theorem empty_family_gives_zero_partition {S : Scheme.{u}} [IsAffine S]
    (X : SmoothSite S) {Z : Scheme.{u}} (p : Z ⟶ X.left) [IsFinite p]
    (x : X.left) (hx : ∀ z : Z, p z ≠ x) :
    ∃ (U : SmoothSite S) (g : U ⟶ X), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ F : Fin 0 → (pullback p g.left).Opens,
      (⨆ j, F j) = ⊤ ∧ IsEmpty (pullback p g.left : Scheme) := by
  let V : Empty → Scheme.{u} := fun i ↦ nomatch i
  let q : ∀ i, V i ⟶ Z := fun i ↦ nomatch i
  have : ∀ i, Etale (q i) := fun i ↦ nomatch i
  have : ∀ i, IsSeparated (q i) := fun i ↦ nomatch i
  obtain ⟨U, g, hg, u, hu, hr, n, F, _, _, ht, label, _, _⟩ :=
    SmoothSite.exists_nisnevich_family_lift_of_isFinite X p x V q
      (fun z hz ↦ (hx z hz).elim)
  cases n with
  | zero =>
    refine ⟨U, g, hg, u, hu, hr, F, ht, ⟨fun t ↦ ?_⟩⟩
    have hmem : t ∈ ⨆ j, F j := by rw [ht]; trivial
    obtain ⟨j, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
    exact Fin.elim0 j
  | succ n => exact (label 0).elim

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Infinite families preserve the actual nonreduced support as a literal
scheme pullback. -/
theorem nonreduced_infinite_family (V : ℕ → Scheme)
    (q : ∀ i, V i ⟶ Spec (.of (ZMod 4)))
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
    (hq : ∀ z : Spec (.of (ZMod 4)),
      ∃ (i : ℕ) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v))
    (x : Spec (.of (ZMod 4))) :
    ∃ (U : SmoothSite (Spec (.of (ZMod 4))))
      (g : U ⟶ SmoothSite.base (Spec (.of (ZMod 4)))), Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ (n : ℕ) (F : Fin n → (pullback (𝟙 (Spec (.of (ZMod 4)))) g.left).Opens),
      (∀ j, IsClopen (F j : Set (pullback (𝟙 (Spec (.of (ZMod 4)))) g.left : Scheme)) ∧
        IsFinite ((F j).ι ≫ pullback.snd (𝟙 (Spec (.of (ZMod 4)))) g.left)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧ (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → ℕ) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫ pullback.fst (𝟙 (Spec (.of (ZMod 4)))) g.left :=
  SmoothSite.exists_nisnevich_family_lift_of_isFinite (S := Spec (.of (ZMod 4)))
    (SmoothSite.base _) (𝟙 _) x V q (fun z _ ↦ hq z)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Disconnected finite product support has actual maps to the selected
family members on a complete finite partition. -/
theorem disconnected_family {R : Type u} [CommRing R] {I : Type v}
    (V : I → Scheme.{u}) (q : ∀ i, V i ⟶ Spec (.of (R × R)))
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
    (hq : ∀ z : Spec (.of (R × R)),
      ∃ (i : I) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v))
    (x : Spec (.of R)) :
    ∃ (U : SmoothSite (Spec (.of R))) (g : U ⟶ SmoothSite.base (Spec (.of R))),
      Etale g.left ∧
    ∃ u : U.left, g.left u = x ∧ IsIso (g.left.residueFieldMap u) ∧
    ∃ (n : ℕ)
      (F : Fin n → (pullback (Spec.map (CommRingCat.ofHom (algebraMap R (R × R))))
        g.left).Opens),
      (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → I) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))) g.left := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))
  have : IsFinite p := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  obtain ⟨U, g, hg, u, hu, hr, n, F, _, _, ht, label, b, hb⟩ :=
    SmoothSite.exists_nisnevich_family_lift_of_isFinite (S := Spec (.of R))
      (SmoothSite.base _) p x V q (fun z _ ↦ hq z)
  exact ⟨U, g, hg, u, hu, hr, n, F, ht, label, b, hb⟩

open Lean in
run_cmd do
  for name in
      #[``_root_.AlgebraicGeometry.Scheme.SmoothSite.exists_nisnevich_family_lift_of_isFinite,
      ``field_family_lift, ``empty_family_gives_zero_partition,
      ``nonreduced_infinite_family, ``disconnected_family] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.SmoothSiteNisnevichFiniteFamilyLifting
