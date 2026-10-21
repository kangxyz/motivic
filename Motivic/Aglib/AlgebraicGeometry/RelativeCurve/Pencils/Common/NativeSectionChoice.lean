/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.NativeSimultaneousSectionChoice

/-! # Produce the common coefficient open before the simultaneous section choice

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Common.NativeSectionChoice`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible Scheme.Hom RelativeProjectiveLine
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil

/-- The open immersion instance used in this module. -/
local instance nativeSectionChoiceOpenImmersion {S X Y C : Scheme.{u}} (q : X ⟶ S) (p : Y ⟶ X)
    (π : C ⟶ S) (j : Y ⟶ C) [IsOpenImmersion j] (hj : j ≫ π = p ≫ q)
    (U : X.Opens) (V : S.Opens) :
    IsOpenImmersion (boundaryBaseCoverInclusion q p π j hj U V) :=
  boundaryBaseCoverInclusion_open q p π j hj U V

/-- The smoothness instance used in this module. -/
local instance nativeSectionChoiceSmooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f
/-- The relative-dimension instance used in this module. -/
local instance nativeSectionChoiceSmoothRelativeDimension1 (R : Type u) [CommRing R] :
    SmoothOfRelativeDimension 1 (boundaryLineProjection R) :=
  Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

/-- The relative-dimension instance used in this module. -/
local instance nativeSectionChoiceSmoothRelativeDimension2
    (R : Type u) [CommRing R] : SmoothOfRelativeDimension 1
    (chart R 0 ≫ ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) := by
  simpa only [Category.id_comp, chart_toSpec] using
    Scheme.AffineLineEtaleCompactification.polynomialProjection_smooth_one R

variable (k : Type u) [Field k] (R : Type u) [CommRing R] [IsNoetherianRing R]
  (ι : Type u) (m : ℕ) (eι : ι ≃ Fin (m + 1)) [Finite ι]
  {Y A Z C D T D₀ T₀ : Scheme.{u}}
  [IsAffine Y] [IsAffine A] [IsAffine T]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (p : Y ⟶ Spec (.of (Polynomial R))) [Etale p] (a : A ⟶ Spec (.of (Polynomial R)))
      [IsOpenImmersion a]
  (f : C ⟶ ProjectiveSpace R ι) [IsFinite f] (j : Y ⟶ C) [IsOpenImmersion j]
  (hj : j ≫ (f ≫ toSpec R ι) = p ≫ (boundaryLineProjection R))
  (z : Z ⟶ Spec (.of (Polynomial R))) (s : Z ⟶ Y) (hs : s ≫ p = z)
  (H : IsPullback s (𝟙 Z) p z)
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]
  (hd : Disjoint (Set.range j) (Set.range d))
  (v : T ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ (f ≫ toSpec R ι))]
  (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
  (φ : pullback p a ⟶ T) (hφ : φ ≫ v = pullback.fst p a ≫ j)


variable [IsFinite (z ≫ boundaryLineProjection R)]
  [IsClosedImmersion (z ≫ chart R 0)]
  (d₀ : D₀ ⟶ ProjectiveSpace R (ULift.{u} (Fin 2))) [IsClosedImmersion d₀]
  (hd₀ : Disjoint (Set.range (chart R 0)) (Set.range d₀))
  [IsAffine T₀] (v₀ : T₀ ⟶ ProjectiveSpace R (ULift.{u} (Fin 2)))
  [IsOpenImmersion v₀]
  [SmoothOfRelativeDimension 1 (v₀ ≫ ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2))))]
  (hc₀ : ∀ x, x ∈ Set.range v₀ ∨ x ∈ Set.range d₀ ∨ x ∈ Set.range (z ≫ chart R 0))


variable [IsFinite (d ≫ (f ≫ toSpec R ι))]
  [IsFinite (d₀ ≫ toSpec R (ULift.{u} (Fin 2)))]

include hs H ha hd hc m eι hd₀ hc₀ in
/-- Choose the common raw boundary frames and affine coefficient neighborhood first,
then make the single source and single target section choices. The original point and
prior base restriction are retained; no frame, free family, or homotopy is supplied. -/
theorem exists_common_native_boundary_sections
    (W : (Spec (.of R)).Opens) (x : Spec (.of R)) (hx : x ∈ W) :
    ∃ (O : (Spec (.of R)).Opens) (hO : IsAffineOpen O),
      let : IsAffine O.toScheme := hO
      x ∈ O ∧ O ≤ W ∧
        NativeSourceBoundarySections (R := R) (ι := ι) (p := p) (a := a)
          (f := f) (j := j) (hj := hj) (z := z) (s := s) (hs := hs) (H := H)
          (d := d) (V := O) ∧
        NativeTargetBoundarySections (R := R) (z := z) (V := O)
          (d₀ := d₀) (hd₀ := hd₀) (v₀ := v₀) := by
  have : IsFinite ((s ≫ j) ≫ (f ≫ toSpec R ι)) := by
    rw [Category.assoc, hj, ← Category.assoc, hs]
    infer_instance
  have : IsFinite (d₀ ≫ ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) := by
    simpa only [Category.id_comp] using
      (inferInstance : IsFinite (d₀ ≫ toSpec R (ULift.{u} (Fin 2))))
  have : IsFinite ((z ≫ chart R 0) ≫
      ((𝟙 _) ≫ toSpec R (ULift.{u} (Fin 2)))) := by
    simpa only [Category.id_comp, Category.assoc, chart_toSpec] using
      (inferInstance : IsFinite (z ≫ boundaryLineProjection R))
  obtain ⟨O, hO, hxO, hOW, ⟨⟨e₁, e₂⟩⟩⟩ :=
    exists_common_base_boundary_unit_frames R ι (ULift.{u} (Fin 2))
      f d (s ≫ j) (𝟙 _) d₀ (z ≫ chart R 0) W x hx
  let : IsAffine O.toScheme := hO
  refine ⟨O, hO, hxO, hOW, ?_⟩
  exact exists_simultaneous_native_boundary_sections
    (R := R) (ι := ι) (m := m) (eι := eι) (p := p) (a := a)
    (f := f) (j := j) (hj := hj) (z := z) (s := s) (hs := hs) (H := H)
    (ha := ha) (d := d) (hd := hd) (v := v) (hc := hc) (V := O)
    (d₀ := d₀) (hd₀ := hd₀) (v₀ := v₀) (hc₀ := hc₀) e₁ e₂

end AlgebraicGeometry.Scheme.RelativeCurvePencil
