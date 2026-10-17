/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Motivic.Aglib.AlgebraicGeometry.Moving.OneSidedSerreSections
public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.AffineSourceDivisorPairs
/-! # One-sided moving sections on the original affine parameter scheme

The spectrum presentation is used only inside Serre lifting. Both the retained
curve and its polynomial family remain over the unchanged parameter scheme.
-/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ProjectiveSpace
open Scheme.Modules Scheme.Modules.Invertible
universe u
namespace AlgebraicGeometry.Scheme.Moving

/-- Serre produces the sections on a literal constant-target product, without
changing the affine parameter source or the original larger homotopy target. -/
theorem exists_oneSidedAffineSections
    (R : Type u) [CommRing R] (K : Type u) [CommRing K]
    (ι : Type u) (n : ℕ) (eι : ι ≃ Fin (n + 1))
    {S C B D X V : Scheme.{u}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
    (b : S ⟶ Spec (.of R)) (bS : S ⟶ Spec (.of K))
    (f : C ⟶ ProjectiveSpace R ι) [IsFinite f]
    [IsLocallyNoetherian (pullback b (f ≫ toSpec R ι))]
    (z : B ⟶ pullback b (f ≫ toSpec R ι)) [IsClosedImmersion z] (i : D ⟶ B)
    (eQ : ∀ d : ℕ, (moduleTensorLeftFunctor B
      ((Modules.pullback z).obj ((Modules.pullback
        (ConstantCurve.affineSourceToProjectiveSpace R ι b f)).obj
          (twistingSheaf Γ(S, ⊤) ι (d : ℤ))))).obj
      ((Modules.pullback z).obj
        (SheafOfModules.unit (pullback b (f ≫ toSpec R ι)).ringCatSheaf)) ≅
          SheafOfModules.unit B.ringCatSheaf)
    (j : X ⟶ pullback b (f ≫ toSpec R ι)) [IsOpenImmersion j] [X.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ pullback.fst b (f ≫ toSpec R ι))]
    (v : V ⟶ pullback b (f ≫ toSpec R ι)) [IsOpenImmersion v] [V.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (v ≫ pullback.fst b (f ≫ toSpec R ι))]
    (hX : ∀ x : (pullback b (f ≫ toSpec R ι) : Scheme),
      x ∈ Set.range j ∨ x ∈ Set.range (i ≫ z))
    (hV : ∀ x : (pullback b (f ≫ toSpec R ι) : Scheme),
      x ∈ Set.range v ∨ x ∈ Set.range z)
    (I : LineBundle (pullback b (f ≫ toSpec R ι)))
    (φ : I.val ⟶ SheafOfModules.unit (pullback b (f ≫ toSpec R ι)).ringCatSheaf)
    (E : (Modules.pullback z).obj (dualLineBundle _ I).val ≅
      SheafOfModules.unit B.ringCatSheaf)
    (hδ : pullbackSectionMap (i ≫ z) (canonicalDualHom _ I.val φ) ≫
      (compositeBoundaryFrame i z (dualLineBundle _ I).val E).hom = 𝟙 _) :
    ∃ T : LineBundle (pullback b (f ≫ toSpec R ι)),
      Nonempty (OneSidedSections bS (pullback.fst b (f ≫ toSpec R ι)) z i j v I T φ E) := by
  let : Finite ι := Finite.of_equiv (Fin (n + 1)) eι.symm
  have : IsProper (f ≫ toSpec R ι) := inferInstance
  obtain ⟨N, hN⟩ := CoherentGraph.exists_affineSource_normalized_divisor_pair
    R ι n eι b f z eQ v hV (dualLineBundle _ I) E
  obtain ⟨a, c, ha, hai, hci, haf, hcf⟩ := hN N le_rfl
  let T := pullbackLineBundle (ConstantCurve.affineSourceToProjectiveSpace R ι b f)
    (twistingLineBundle Γ(S, ⊤) ι (N : ℤ))
  let := hai
  exact ⟨T, ⟨⟨a, c, ha, hai, hci, haf, hcf,
    oneSided_pencil_finite_flat bS (pullback.fst b (f ≫ toSpec R ι))
      j z i hX I T φ E a c ha hδ⟩⟩⟩

end AlgebraicGeometry.Scheme.Moving
