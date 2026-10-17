/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.NisnevichFiniteFamilyLifting
public import Mathlib.Data.ZMod.Basic
public import Lean.Util.CollectAxioms

/-!
# Consumers of arbitrary-family finite-support Nisnevich lifting

The index type is unrestricted. MotivicTest retain actual branch maps on a complete
finite clopen partition, allow nonreduced and disconnected supports, and use
an empty index type to force a zero-piece partition and empty support.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace MotivicTest.NisnevichFiniteFamilyLifting

/-- Both the index universe and the family cardinality are unrestricted. -/
example {I : Type v} {Z S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p] (s : S)
    (V : I → Scheme.{u}) (q : ∀ i, V i ⟶ Z)
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
    (hq : ∀ z : Z, p z = s →
      ∃ (i : I) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ Function.Bijective (g.residueFieldMap u) ∧
    ∃ (n : ℕ) (F : Fin n → (pullback p g).Opens),
      (∀ j, IsClopen (F j : Set (pullback p g : Scheme)) ∧
        IsFinite ((F j).ι ≫ pullback.snd p g)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧ (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → I) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫ pullback.fst p g := by
  obtain ⟨U, g, hg, u, hu, hr, n, F, hF, hd, ht, label, b, hb⟩ :=
    exists_nisnevich_family_lift_of_isFinite p s V q hq
  exact ⟨U, g, hg, u, hu, (ConcreteCategory.isIso_iff_bijective _).mp hr,
    n, F, hF, hd, ht, label, b, hb⟩

/-- No target is needed over an empty fiber: the partition has zero pieces. -/
theorem empty_family_gives_zero_partition {Z S : Scheme.{u}}
    (p : Z ⟶ S) [IsFinite p] (s : S) (hs : ∀ z : Z, p z ≠ s) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ F : Fin 0 → (pullback p g).Opens,
      (⨆ j, F j) = ⊤ ∧ IsEmpty (pullback p g : Scheme) := by
  let V : Empty → Scheme.{u} := fun i ↦ nomatch i
  let q : ∀ i, V i ⟶ Z := fun i ↦ nomatch i
  have : ∀ i, Etale (q i) := fun i ↦ nomatch i
  have : ∀ i, IsSeparated (q i) := fun i ↦ nomatch i
  obtain ⟨U, g, hg, u, hu, hr, n, F, _, _, ht, label, _, _⟩ :=
    exists_nisnevich_family_lift_of_isFinite p s V q (fun z hz ↦ (hs z hz).elim)
  cases n with
  | zero =>
    refine ⟨U, g, hg, u, hu, hr, F, ht, ⟨fun t ↦ ?_⟩⟩
    have hmem : t ∈ ⨆ j, F j := by rw [ht]; trivial
    obtain ⟨j, _⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
    exact Fin.elim0 j
  | succ n => exact (label 0).elim

/-- The actual nonreduced support is retained even for an infinite family. -/
example (V : ℕ → Scheme) (q : ∀ i, V i ⟶ Spec (.of (ZMod 4)))
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
    (hq : ∀ z : Spec (.of (ZMod 4)),
      ∃ (i : ℕ) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v))
    (s : Spec (.of (ZMod 4))) :
    ∃ (U : Scheme) (g : U ⟶ Spec (.of (ZMod 4))), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ (n : ℕ) (F : Fin n → (pullback (𝟙 (Spec (.of (ZMod 4)))) g).Opens),
      (∀ j, IsClopen (F j : Set (pullback (𝟙 _) g : Scheme)) ∧
        IsFinite ((F j).ι ≫ pullback.snd (𝟙 _) g)) ∧
      Pairwise (fun i j ↦ Disjoint (F i) (F j)) ∧ (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → ℕ) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫ pullback.fst (𝟙 _) g :=
  exists_nisnevich_family_lift_of_isFinite (𝟙 _) s V q (fun z _ ↦ hq z)

/-- An arbitrary family also lifts a disconnected finite product support. -/
example {R : Type u} [CommRing R] {I : Type v}
    (V : I → Scheme.{u}) (q : ∀ i, V i ⟶ Spec (.of (R × R)))
    [∀ i, Etale (q i)] [∀ i, IsSeparated (q i)]
    (hq : ∀ z : Spec (.of (R × R)),
      ∃ (i : I) (v : V i), q i v = z ∧ IsIso ((q i).residueFieldMap v))
    (s : Spec (.of R)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ Spec (.of R)), Etale g ∧
    ∃ u : U, g u = s ∧ IsIso (g.residueFieldMap u) ∧
    ∃ (n : ℕ)
      (F : Fin n → (pullback (Spec.map (CommRingCat.ofHom (algebraMap R (R × R))))
        g).Opens),
      (⨆ j, F j) = ⊤ ∧
    ∃ (label : Fin n → I) (b : ∀ j, (F j).toScheme ⟶ V (label j)),
      ∀ j, b j ≫ q (label j) = (F j).ι ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))) g := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap R (R × R)))
  have : IsFinite p := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  obtain ⟨U, g, hg, u, hu, hr, n, F, _, _, ht, label, b, hb⟩ :=
    exists_nisnevich_family_lift_of_isFinite p s V q (fun z _ ↦ hq z)
  exact ⟨U, g, hg, u, hu, hr, n, F, ht, label, b, hb⟩

open Lean in
run_cmd do
  for name in #[``exists_nisnevich_family_lift_of_isFinite,
      ``empty_family_gives_zero_partition] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.NisnevichFiniteFamilyLifting
