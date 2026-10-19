/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ResidualFiber

/-! # The whole residual open under an actual marked Cartesian square

Complementary opens commute with the actual marked pullback. The resulting
map retains both injections and hence transports an existing factorization
through a thickened boundary without passing through a reduced closed subscheme.


Intended upstream module: `Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ResidualFiberPullback`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.BaseChangeSquare`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace AlgebraicGeometry.Scheme

/-- The actual Cartesian square identifies the full inverse image of its marked range. -/
theorem range_snd_eq_preimage_of_isPullback {Z Z' F F' : Scheme.{u}}
    (a : Z' ⟶ Z) (i' : Z' ⟶ F') (i : Z ⟶ F) (v : F' ⟶ F)
    (H : IsPullback a i' i v) : Set.range i' = v ⁻¹' Set.range i := by
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨a z, congrArg (fun f : Z' ⟶ F => f z) H.w⟩
  · rintro ⟨z, hz⟩
    obtain ⟨w, _, hw⟩ := Scheme.Pullback.exists_preimage_pullback z x hz
    refine ⟨H.isoPullback.inv w, ?_⟩
    exact (congrArg (fun f => f w) H.isoPullback_inv_snd).trans hw

variable {C X Y Z C' X' Y' Z' : Scheme.{u}}
  (f : C ⟶ X) [IsFinite f] (j : Y ⟶ C) [IsOpenImmersion j]
  (z : Z ⟶ X) [IsClosedImmersion z] (s : Z ⟶ Y) (hs : (s ≫ j) ≫ f = z)
  (f' : C' ⟶ X') [IsFinite f'] (j' : Y' ⟶ C') [IsOpenImmersion j']
  (z' : Z' ⟶ X') [IsClosedImmersion z'] (s' : Z' ⟶ Y')
  (hs' : (s' ≫ j') ≫ f' = z')
  (a : Z' ⟶ Z) (v : pullback f' z' ⟶ pullback f z)
  (H : IsPullback a (markedFiberSection f' j' z' s' hs')
    (markedFiberSection f j z s hs) v)

omit [IsOpenImmersion j] [IsClosedImmersion z] [IsOpenImmersion j'] [IsClosedImmersion z']

include H in
/-- The actual residual open is the full inverse image of the original residual open. -/
theorem residualMarkedFiberOpen_eq_preimage :
    residualMarkedFiberOpen f' j' z' s' hs' = v ⁻¹ᵁ residualMarkedFiberOpen f j z s hs := by
  ext x
  change x ∉ Set.range (markedFiberSection f' j' z' s' hs') ↔
    v x ∉ Set.range (markedFiberSection f j z s hs)
  rw [range_snd_eq_preimage_of_isPullback a _ _ v H]
  rfl

/-- Canonical map between the full residual open schemes of an actual marked square. -/
def residualMarkedFiberPullbackMap :
    (residualMarkedFiberOpen f' j' z' s' hs').toScheme ⟶
      (residualMarkedFiberOpen f j z s hs).toScheme :=
  IsOpenImmersion.lift (residualMarkedFiberOpen f j z s hs).ι
    ((residualMarkedFiberOpen f' j' z' s' hs').ι ≫ v) (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (le_of_eq
        (residualMarkedFiberOpen_eq_preimage f j z s hs f' j' z' s' hs' a v H)) x.property)

/-- Both original fiber injections commute literally with the residual map. -/
@[reassoc (attr := simp)] theorem residualMarkedFiberPullbackMap_ι :
    residualMarkedFiberPullbackMap f j z s hs f' j' z' s' hs' a v H ≫
      (residualMarkedFiberOpen f j z s hs).ι =
    (residualMarkedFiberOpen f' j' z' s' hs').ι ≫ v :=
  IsOpenImmersion.lift_fac _ _ _

/-- An existing scheme-theoretic thickened-boundary factorization transports
through the actual residual map, with its original compactification map intact. -/
theorem residualMarkedFiberPullbackMap_boundary {D : Scheme.{u}}
    (d : D ⟶ C) (b : (residualMarkedFiberOpen f j z s hs).toScheme ⟶ D)
    (hb : b ≫ d = residualMarkedFiberMap f j z s hs) :
    (residualMarkedFiberPullbackMap f j z s hs f' j' z' s' hs' a v H ≫ b) ≫ d =
      (residualMarkedFiberOpen f' j' z' s' hs').ι ≫ v ≫ pullback.fst f z := by
  rw [Category.assoc, hb]
  simp only [residualMarkedFiberMap, ← Category.assoc, residualMarkedFiberPullbackMap_ι]

end AlgebraicGeometry.Scheme
