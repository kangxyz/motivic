/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.ThickenedBoundary
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Boundary.Frames.FiniteCoproduct

/-! # Actual thickened infinity and marked support on one affine coefficient neighborhood

Intended upstream module:
`Aglib.AlgebraicGeometry.Normalization.Compactification.Boundary.ThickenedTwistFrames`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules
universe u
namespace AlgebraicGeometry.Scheme

/-- Construct the full thickened boundary once and frame its actual restricted coproduct
with the marked support. The residual and target-infinity scheme maps are retained. -/
theorem exists_thickened_boundary_base_open_twist_frames
    (R : Type u) [CommRing R] (ι : Type u)
    {C X Y U Z D I : Scheme.{u}}
    (f : C ⟶ X) [IsFinite f] (g : C ⟶ ProjectiveSpace R ι)
    [IsProper (g ≫ toSpec R ι)]
    (j : Y ⟶ C) [IsOpenImmersion j]
    (d : D ⟶ C) [IsClosedImmersion d] [IsFinite (d ≫ (g ≫ toSpec R ι))]
    (hd : Set.range d = (Set.range j)ᶜ)
    (z : Z ⟶ X) [IsClosedImmersion z] (s : Z ⟶ Y)
    (hs : (s ≫ j) ≫ f = z) (H : IsPullback s (𝟙 Z) (j ≫ f) z)
    [IsFinite ((s ≫ j) ≫ (g ≫ toSpec R ι))]
    (i : I ⟶ X) [IsClosedImmersion i]
    (p : Y ⟶ U) (k : U ⟶ X) (hp : p ≫ k = j ≫ f)
    (hi : Disjoint (Set.range k) (Set.range i)) (x : Spec (.of R)) :
    ∃ (D' : Scheme.{u}) (d' : D' ⟶ C), IsClosedImmersion d' ∧
      Set.range d' = (Set.range j)ᶜ ∧
      Disjoint (Set.range j) (Set.range d') ∧
      Disjoint (Set.range (s ≫ j)) (Set.range d') ∧
      IsFinite (d' ≫ (g ≫ toSpec R ι)) ∧
      ∃ (a : D ⟶ D')
        (b : (residualMarkedFiberOpen f j z s hs).toScheme ⟶ D')
        (c : pullback f i ⟶ D'),
        a ≫ d' = d ∧ b ≫ d' = residualMarkedFiberMap f j z s hs ∧
          c ≫ d' = pullback.fst f i ∧
        ∃ (O : (Spec (.of R)).Opens) (hO : IsAffineOpen O),
          let : IsAffine O.toScheme := hO
          x ∈ O ∧ Nonempty ((n : ℕ) →
            (Modules.pullback
              (coprod.desc (Hom.boundaryBaseWholeMap (g ≫ toSpec R ι) d' O)
                (Hom.boundaryBaseWholeMap (g ≫ toSpec R ι) (s ≫ j) O) ≫
                  Hom.boundaryBaseProjectiveMap R ι g O)).obj
              (twistingSheaf Γ(O.toScheme, ⊤) ι (n : ℤ)) ≅
                SheafOfModules.unit
                  ((((d' ≫ (g ≫ toSpec R ι)) ⁻¹ᵁ O).toScheme ⨿
                    (((s ≫ j) ≫ (g ≫ toSpec R ι)) ⁻¹ᵁ O).toScheme)).ringCatSheaf) := by
  obtain ⟨D', d', hclosed, hrange, hj, hmarked, hfinite, a, b, c, ha, hb, hc⟩ :=
    exists_thickened_compactification_boundary f (g ≫ toSpec R ι) j d hd z s hs H
      i p k hp hi
  let := hfinite
  obtain ⟨O, hO, hx, eFull⟩ :=
    Hom.exists_base_open_coproduct_boundary_twist_frames R ι g d' (s ≫ j) x
  exact ⟨D', d', hclosed, hrange, hj, hmarked, hfinite, a, b, c, ha, hb, hc,
    O, hO, hx, eFull⟩

end AlgebraicGeometry.Scheme
