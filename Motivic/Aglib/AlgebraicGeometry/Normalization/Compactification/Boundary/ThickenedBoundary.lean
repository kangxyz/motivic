/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Morphisms.Finite.Marked.ResidualFiber
public import Motivic.Aglib.AlgebraicGeometry.Morphisms.ClosedImmersion.ThickenedBoundary

/-!
# A full scheme-theoretic compactification boundary

Adjoin the actual residual marked fiber and the full inverse image of target
infinity to an existing finite boundary. The residual scheme is constructed from
the original marked pullback, not supplied as a new hypothesis. No reduction of
either added scheme is taken. Finiteness of the old boundary is an explicit input,
usually obtained by an earlier restriction of the original base.


Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.ThickenedBoundary`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.ThickenedTwistFrames`,
Module prefix: `Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.`
Module suffix: `RelativeAffineLine.RestrictedThickenedBoundary`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme

/-- The enlarged boundary retains the whole residual marked scheme and the whole
scheme inverse image of target infinity, with their literal maps into the original
compactification. The marked component remains disjoint from this boundary. -/
theorem exists_thickened_compactification_boundary
    {C X S Y U Z D I : Scheme.{u}}
    (f : C ⟶ X) [IsFinite f] (q : C ⟶ S) [IsProper q]
    (j : Y ⟶ C) [IsOpenImmersion j]
    (d : D ⟶ C) [IsClosedImmersion d] [IsFinite (d ≫ q)]
    (hd : Set.range d = (Set.range j)ᶜ)
    (z : Z ⟶ X) [IsClosedImmersion z] (s : Z ⟶ Y)
    (hs : (s ≫ j) ≫ f = z) (H : IsPullback s (𝟙 Z) (j ≫ f) z)
    (i : I ⟶ X) [IsClosedImmersion i]
    (p : Y ⟶ U) (k : U ⟶ X) (hp : p ≫ k = j ≫ f)
    (hi : Disjoint (Set.range k) (Set.range i)) :
    ∃ (D' : Scheme.{u}) (d' : D' ⟶ C), IsClosedImmersion d' ∧
      Set.range d' = (Set.range j)ᶜ ∧
      Disjoint (Set.range j) (Set.range d') ∧
      Disjoint (Set.range (s ≫ j)) (Set.range d') ∧ IsFinite (d' ≫ q) ∧
      ∃ (a : D ⟶ D')
        (b : (residualMarkedFiberOpen f j z s hs).toScheme ⟶ D')
        (c : pullback f i ⟶ D'),
        a ≫ d' = d ∧ b ≫ d' = residualMarkedFiberMap f j z s hs ∧
          c ≫ d' = pullback.fst f i := by
  let e := residualMarkedFiberMap f j z s hs
  have : IsClosedImmersion e := residualMarkedFiberMap_closed f j z s hs H
  have he : Set.range e ⊆ Set.range d := by
    rw [hd]
    intro x hx
    exact fun hj => Set.disjoint_left.mp
      (residualMarkedFiberMap_disjoint f j z s hs H) hj hx
  have hInfinity : Set.range (pullback.fst f i) ⊆ Set.range d := by
    rw [hd]
    rintro x ⟨w, rfl⟩ ⟨y, hy⟩
    have hxy : k (p y) = i ((pullback.snd f i) w) := by
      calc
        k (p y) = f (j y) := by
          simpa only [Scheme.Hom.comp_apply] using congrArg (fun m => m y) hp
        _ = f ((pullback.fst f i) w) := congrArg f hy
        _ = i ((pullback.snd f i) w) := by
          simpa only [Scheme.Hom.comp_apply] using
            congrArg (fun m => m w) (pullback.condition (f := f) (g := i))
    exact Set.disjoint_left.mp hi ⟨p y, hxy⟩ ⟨(pullback.snd f i) w, rfl⟩
  have hdisjoint : Disjoint (Set.range j) (Set.range d) := by
    rw [hd]
    exact disjoint_compl_right
  obtain ⟨D', d', hclosed, hrange, hj, hfinite, a, b, c, ha, hb, hc⟩ :=
    exists_thickened_closed_boundary q j d e (pullback.fst f i) he hInfinity hdisjoint
  have hmarked : Disjoint (Set.range (s ≫ j)) (Set.range d') := by
    apply hj.mono_left
    rintro _ ⟨w, rfl⟩
    exact ⟨s w, rfl⟩
  exact ⟨D', d', hclosed, hrange.trans hd, hj, hmarked, hfinite, a, b, c, ha, hb, hc⟩

end AlgebraicGeometry.Scheme
