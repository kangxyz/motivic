/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.NisnevichQuasiFinite
public import Mathlib.Data.ZMod.Basic

/-!
# Consumers of pointed Nisnevich branch isolation

These consumers extract bijectivity of the actual residue-field map and a
singleton set-theoretic fiber of the finite component. They also recover the
older unpointed conclusion and specialize to finite morphisms over an arbitrary,
possibly nonreduced base. No abstract isomorphism between residue-field types is
substituted for the map induced by the neighborhood morphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.NisnevichQuasiFinite

/-- The actual finite component has exactly the chosen point over the
Nisnevich point, and the actual residue map is bijective. -/
theorem singleton_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsSeparated f] (x : X) (hx : f.QuasiFiniteAt x) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = f x ∧ Function.Bijective (g.residueFieldMap u) ∧
    ∃ (V : (pullback f g).Opens) (v : V),
      IsFinite (V.ι ≫ pullback.snd f g) ∧ pullback.fst f g v.1 = x ∧
      (V.ι ≫ pullback.snd f g) ⁻¹' {u} = {v} := by
  obtain ⟨U, g, hg, u, hu, hres, V, W, v, hVW, hfin, hvx, hvu, huniq⟩ :=
    exists_nisnevich_isCompl_of_quasiFiniteAt f rfl hx
  refine ⟨U, g, hg, u, hu, (ConcreteCategory.isIso_iff_bijective _).mp hres,
    V, v, hfin, hvx, ?_⟩
  ext z
  change pullback.snd f g z.1 = u ↔ z = v
  exact ⟨huniq z, fun h ↦ h ▸ hvu⟩

/-- Dropping the pointing and uniqueness recovers the existing étale
finite-component theorem without further hypotheses. -/
theorem unpointed_conclusion {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsSeparated f] {x : X} {s : S}
    (h : f x = s) (hx : f.QuasiFiniteAt x) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧ s ∈ Set.range g ∧
    ∃ (V W : (pullback f g).Opens) (v : V),
      IsCompl V W ∧ IsFinite (V.ι ≫ pullback.snd f g) ∧ pullback.fst f g v.1 = x := by
  obtain ⟨U, g, hg, u, hu, hres, V, W, v, hVW, hfin, hvx, hvu, huniq⟩ :=
    exists_nisnevich_isCompl_of_quasiFiniteAt f h hx
  exact ⟨U, g, hg, ⟨u, hu⟩, V, W, v, hVW, hfin, hvx⟩

/-- Every point of a finite morphism has the strengthened neighborhood. -/
theorem finite_morphism {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] (x : X) :
    ∃ (U : Scheme.{u}) (g : U ⟶ S), Etale g ∧
    ∃ u : U, g u = f x ∧ Function.Bijective (g.residueFieldMap u) ∧
    ∃ (V : (pullback f g).Opens) (v : V),
      IsFinite (V.ι ≫ pullback.snd f g) ∧ pullback.fst f g v.1 = x ∧
      (V.ι ≫ pullback.snd f g) ⁻¹' {u} = {v} :=
  singleton_fiber f x (f.quasiFiniteAt x)

/-- No reducedness assumption is needed on the base. -/
example {X : Scheme} (f : X ⟶ Spec (.of (ZMod 4))) [IsFinite f] (x : X) :
    ∃ (U : Scheme) (g : U ⟶ Spec (.of (ZMod 4))), Etale g ∧
    ∃ u : U, g u = f x ∧ Function.Bijective (g.residueFieldMap u) ∧
    ∃ (V : (pullback f g).Opens) (v : V),
      IsFinite (V.ι ≫ pullback.snd f g) ∧ pullback.fst f g v.1 = x ∧
      (V.ι ≫ pullback.snd f g) ⁻¹' {u} = {v} :=
  finite_morphism f x

end Motivic.MotivicTest.NisnevichQuasiFinite
