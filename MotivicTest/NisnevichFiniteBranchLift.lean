/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.NisnevichFiniteBranchLift
public import Mathlib.Data.ZMod.Basic
public import Lean.Util.CollectAxioms

/-!
# Consumers of actual finite-support branch lifting

The endpoint produces a morphism on the entire canonical pullback. Its finite
support has no flatness, reducedness, or separability hypotheses. In particular
the support residue field need not equal the residue field of the base.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace MotivicTest.NisnevichFiniteBranchLift

example {Z V S : Scheme.{u}} (p : Z ⟶ S) [IsFinite p]
    (s : S) (z : Z) (hz : p z = s)
    (huniq : ∀ z' : Z, p z' = s → z' = z)
    (q : V ⟶ Z) [Etale q] [IsSeparated q]
    (v : V) (hv : q v = z) (hres : IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = s ∧ Function.Bijective (g.residueFieldMap u) ∧
    ∃ b : pullback p g ⟶ V, b ≫ q = pullback.fst p g := by
  obtain ⟨U, g, hg, u, hu, hgu, b, hb⟩ :=
    exists_nisnevich_lift_of_isFinite_singleton p s z hz huniq q v hv hres
  exact ⟨U, g, hg, u, hu, (ConcreteCategory.isIso_iff_bijective _).mp hgu, b, hb⟩

/-- Arbitrary finite field extensions are allowed, including inseparable ones. -/
example {k K : Type u} [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    {V : Scheme.{u}} (q : V ⟶ Spec (.of K)) [Etale q] [IsSeparated q]
    (v : V) (hres : IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme.{u}) (g : U ⟶ Spec (.of k)), Etale g ∧
    ∃ u : U, g u = IsLocalRing.closedPoint k ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) g ⟶ V,
      b ≫ q = pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) g := by
  let p := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : IsFinite p := (IsFinite.SpecMap_iff _).mpr
    (RingHom.finite_algebraMap.mpr inferInstance)
  exact exists_nisnevich_lift_of_isFinite_singleton p (IsLocalRing.closedPoint k)
    (q v) (Subsingleton.elim _ _) (fun _ _ ↦ Subsingleton.elim _ _) q v rfl hres

/-- The support can be the nonreduced scheme `Spec (ZMod 4)`. -/
example {V : Scheme} (q : V ⟶ Spec (.of (ZMod 4))) [Etale q] [IsSeparated q]
    (v : V) (hres : IsIso (q.residueFieldMap v)) :
    ∃ (U : Scheme) (g : U ⟶ Spec (.of (ZMod 4))), Etale g ∧
    ∃ u : U, g u = q v ∧ IsIso (g.residueFieldMap u) ∧
    ∃ b : pullback (𝟙 (Spec (.of (ZMod 4)))) g ⟶ V,
      b ≫ q = pullback.fst (𝟙 _) g :=
  exists_nisnevich_lift_of_isFinite_singleton (𝟙 _) (q v) (q v) rfl
    (fun _ h ↦ h) q v rfl hres

example {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (y : Y)
    [IsIso (g.residueFieldMap y)] (t : (pullback f g : Scheme))
    (ht : pullback.snd f g t = y) :
    IsIso ((pullback.fst f g).residueFieldMap t) :=
  f.isIso_residueFieldMap_pullback_fst g y t ht

example {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (y : Y)
    [IsIso (g.residueFieldMap y)] (t t' : (pullback f g : Scheme))
    (ht : pullback.snd f g t = y) (ht' : pullback.snd f g t' = y)
    (he : pullback.fst f g t = pullback.fst f g t') : t = t' :=
  f.pullback_point_ext_of_residueFieldIso g y t t' ht ht' he

open Lean in
run_cmd do
  for name in #[``Scheme.Hom.locallyQuasiFinite_of_etale,
      ``Scheme.Hom.isIso_residueFieldMap_of_surjectiveOnStalks,
      ``Scheme.Hom.isPreimmersion_fiberι_comp_pullback_fst,
      ``Scheme.Hom.isIso_residueFieldMap_pullback_fst,
      ``Scheme.Hom.pullback_point_ext_of_residueFieldIso,
      ``exists_nisnevich_lift_of_isFinite_singleton] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.NisnevichFiniteBranchLift
