/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.RelativeCurve.FullBoundaryTwistFrames

/-! # Retain one Serre choice from one frame on the full target boundary

Intended upstream module:
`Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.FullBoundarySectionData`.
Incoming project consumers:
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.BoundaryBaseSectionData`,
`Motivic.Aglib.AlgebraicGeometry.RelativeCurve.Pencils.Data.NativeBoundarySectionData`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.RelativeCurvePencil
local instance {X Y : Scheme.{u}} (f : X ⟶ Y) [SmoothOfRelativeDimension 1 f] :
    Smooth f := SmoothOfRelativeDimension.smooth 1 f

variable (k : Type u) [Field k] (R : Type u) [CommRing R]
  (ι : Type u) (m : ℕ) (eι : ι ≃ Fin (m + 1)) [Finite ι]
  {X Y A B Z C D V : Scheme.{u}}
  [IsAffine Y] [IsAffine A] [IsAffine B] [IsAffine V]
  (t : Spec (.of R) ⟶ Spec (.of k)) [Smooth t]
  (q : X ⟶ Spec (.of R)) [IsSeparated q] [SmoothOfRelativeDimension 1 q]
  (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
  (j : Y ⟶ C) [IsOpenImmersion j]
  [hY : SmoothOfRelativeDimension 1 (j ≫ (f ≫ toSpec R ι))]
  (p : Y ⟶ X) [Flat p] (hq : j ≫ (f ≫ toSpec R ι) = p ≫ q)
  (a : A ⟶ X) [IsOpenImmersion a]
  (α : B ⟶ Y) [Smooth α] (β : B ⟶ A) [Flat β] (h : α ≫ p = β ≫ a)
  (z : Z ⟶ X) (s : Z ⟶ Y) (hs : s ≫ p = z) (H : IsPullback s (𝟙 _) p z)
  (e : SheafOfModules.unit (pullback q (z ≫ q)).ringCatSheaf ≅
    Hom.idealModule (Hom.boundaryGraphTarget q z))
  (ha : Disjoint (Set.range a) (Set.range z)) (d : D ⟶ C)
  (hd : Disjoint (Set.range j) (Set.range d))
  [IsNoetherianRing Γ(Y, ⊤)] [IsNoetherianRing Γ(A, ⊤)]
  [IsLocallyNoetherian (pullback (j ≫ (f ≫ toSpec R ι)) (f ≫ toSpec R ι))]
  [IsLocallyNoetherian (pullback (a ≫ q) (f ≫ toSpec R ι))]
  [IsClosedImmersion d] [IsClosedImmersion (s ≫ j)]

include m eι hq H e ha hd hY in
/-- Both coefficient systems come from the same supplied full-target frame.
The rich output retains the original sections for every subsequent identity. -/
theorem exists_boundarySectionData_of_full_target_frame
    (v : V ⟶ C) [IsOpenImmersion v] [SmoothOfRelativeDimension 1 (v ≫ (f ≫ toSpec R ι))]
    (hc : ∀ c : C, c ∈ Set.range v ∨ c ∈ Set.range d ∨ c ∈ Set.range (s ≫ j))
    (eFull : ∀ n : ℕ, (Modules.pullback (fullTargetBoundaryMap j s d ≫ f)).obj
      (twistingSheaf R ι (n : ℤ)) ≅ SheafOfModules.unit (D ⨿ Z).ringCatSheaf) :
    Nonempty (BoundarySectionData q (f ≫ toSpec R ι) j p hq a z s hs H e ha d hd) :=
  exists_boundarySectionData_of_boundaryFrames
    (R := R) (ι := ι) (m := m) (eι := eι) (q := q) (f := f) (j := j)
    (p := p) (hq := hq) (a := a) (z := z) (s := s) (hs := hs) (H := H)
    (e := e) (ha := ha) (d := d) (hd := hd) v hc
    (lambdaTwistFramesOfFullTargetFrame R ι f j s d eFull)
    (psiTwistFramesOfFullTargetFrame R ι q f j p hq a z s hs d eFull)

end AlgebraicGeometry.Scheme.RelativeCurvePencil
