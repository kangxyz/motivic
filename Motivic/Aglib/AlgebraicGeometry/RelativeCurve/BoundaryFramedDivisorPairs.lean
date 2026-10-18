/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.RelativeCurve.NormalizedDivisorPairs
public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.BoundaryFramedTensor

/-!
# Boundary-framed classes of the actual Serre divisor pairs

The existing geometric producer supplies the sections and their full finite-flat
zero schemes. Its literal boundary equation identifies their framed classes.
The finite projective presentation and all-twist boundary frames remain explicit;
this is not a general relative Picard representability theorem.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

namespace AlgebraicGeometry.Scheme.CoherentGraph

/-- The original normalized pair, its finite-flat zeros, and its boundary-framed class
are produced together without replacing either section or its zero scheme. -/
theorem exists_boundaryFramed_divisor_pair
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {C W U : Scheme.{u}} [IsLocallyNoetherian C]
    (a : C ⟶ ProjectiveSpace R ι) [IsFinite a]
    (z : W ⟶ C) [IsClosedImmersion z]
    (eQ : ∀ d : ℕ, (moduleTensorLeftFunctor W
      ((Modules.pullback z).obj ((Modules.pullback a).obj (twistingSheaf R ι (d : ℤ))))).obj
        ((Modules.pullback z).obj (SheafOfModules.unit C.ringCatSheaf)) ≅
          SheafOfModules.unit W.ringCatSheaf)
    (j : U ⟶ C) [IsOpenImmersion j] [U.IsQuasiAffine]
    [SmoothOfRelativeDimension 1 (j ≫ a ≫ toSpec R ι)]
    (hcover : ∀ x : C, x ∈ Set.range j ∨ x ∈ Set.range z)
    (M : BoundaryFramedLineBundle z) :
    ∃ B : ℕ, ∀ d : ℕ, B ≤ d →
      let T := pullbackLineBundle a (twistingLineBundle R ι (d : ℤ))
      ∃ s : SheafOfModules.unit C.ringCatSheaf ⟶ (tensorLineBundle C T M.lineBundle).val,
      ∃ t : SheafOfModules.unit C.ringCatSheaf ⟶ T.val,
      ∃ hs : IsIso (pullbackSectionMap z s), ∃ ht : IsIso (pullbackSectionMap z t),
        pullbackSectionMap z s ≫ pullbackTensorMap z T.val M.lineBundle.val =
          tensorUnitSection (pullbackSectionMap z t) M.frame.inv ∧
        SectionDivisorFiniteFlat (a ≫ toSpec R ι) j (tensorLineBundle C T M.lineBundle) s ∧
        SectionDivisorFiniteFlat (a ≫ toSpec R ι) j T t ∧
        BoundaryFramedLineBundle.classOf
            (@BoundaryFramedLineBundle.ofSection _ _ z (tensorLineBundle C T M.lineBundle) s hs) =
          BoundaryFramedLineBundle.tensorClass
            (BoundaryFramedLineBundle.classOf (@BoundaryFramedLineBundle.ofSection _ _ z T t ht))
            (BoundaryFramedLineBundle.classOf M) := by
  obtain ⟨B, hB⟩ := exists_normalized_boundary_divisor_pair R ι n e a z eQ j hcover
    M.lineBundle M.frame
  refine ⟨B, fun d hd => ?_⟩
  obtain ⟨s, t, hst, hs, ht, hsff, htff⟩ := hB d hd
  let := hs
  let := ht
  exact ⟨s, t, hs, ht, hst, hsff, htff,
    BoundaryFramedLineBundle.classOf_normalizedSection _ M s t hst⟩

end AlgebraicGeometry.Scheme.CoherentGraph
