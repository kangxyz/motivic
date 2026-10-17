module

public import Motivic.Cohomology.RelativeSheafCohomologyNaturality
public import Motivic.Aglib.CategoryTheory.Sites.FreeAbelianSheafPushout
public import Motivic.Aglib.AlgebraicGeometry.SmoothSiteNisnevichDistinguishedSquare
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels

/-! # Nisnevich excision for actual relative Ext

A geometric Nisnevich distinguished square gives a pushout of the actual
free abelian sheaves, hence an isomorphism of the existing relative sources.
All relative Ext degrees are preserved, with the existing signed boundary.
No homotopy invariance or purity hypothesis is used.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

universe w t v u

namespace Motivic.SheafCohomology

section General

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max v t}]
  (sq : Square C)

/-- Section descent identifies the actual relative cokernel map. -/
theorem isIso_relativeSourceMap_of_section_descent
    (h : ∀ F : Sheaf J AddCommGrpCat.{max v t}, (sq.op.map F.obj).IsPullback) :
    IsIso (relativeSourceMap J sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm) := by
  exact isIso_cokernel_map_of_isPushout
    (Hypercohomology.freeAbelianSheaf_isPushout J sq h).flip

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{max v t})]

/-- The existing relative restriction is an isomorphism in every Ext degree. -/
theorem isIso_relativeRestriction_of_section_descent
    (h : ∀ F : Sheaf J AddCommGrpCat.{max v t}, (sq.op.map F.obj).IsPullback)
    (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    IsIso (relativeRestriction J sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm F n) := by
  let := isIso_relativeSourceMap_of_section_descent J sq h
  change IsIso (((extFunctor n).map
    (relativeSourceMap J sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm).op).app F)
  infer_instance

end General

section Nisnevich

variable {S : Scheme.{u}} [HasSheafify (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}]
  (sq : Square (SmoothSite S)) (hpb : sq.IsPullback)
  [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
  {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
  [IsIso (pullback.snd sq.f₃₄.left z)]

include hpb z hcomp

/-- Genuine Nisnevich excision of the actual relative source. -/
theorem isIso_relativeSourceMap_nisnevich :
    IsIso (relativeSourceMap (SmoothSite.nisnevichTopology S)
      sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm) :=
  isIso_relativeSourceMap_of_section_descent _ sq
    (SmoothSite.isPullback_op_map_of_iso_complement sq hpb z hcomp)

variable [HasExt.{w} (Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t})]

/-- Genuine Nisnevich excision in every relative cohomological degree. -/
theorem isIso_relativeRestriction_nisnevich
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}) (n : ℕ) :
    IsIso (relativeRestriction (SmoothSite.nisnevichTopology S)
      sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm F n) :=
  isIso_relativeRestriction_of_section_descent _ sq
    (SmoothSite.isPullback_op_map_of_iso_complement sq hpb z hcomp) F n

/-- The actual restriction, packaged as the Nisnevich excision isomorphism. -/
def relativeNisnevichExcisionIso
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}) (n : ℕ) :
    relativeH (SmoothSite.nisnevichTopology S) sq.f₂₄ F n ≅
      relativeH (SmoothSite.nisnevichTopology S) sq.f₁₃ F n := by
  letI := isIso_relativeRestriction_nisnevich sq hpb z hcomp F n
  exact asIso (relativeRestriction (SmoothSite.nisnevichTopology S)
    sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm F n)

local instance : Mono sq.f₂₄ := (SmoothSite.forgetScheme S).mono_of_mono_map (by
  change Mono sq.f₂₄.left
  infer_instance)

/-- The excision isomorphism commutes with the standard signed boundary. -/
theorem relativeNisnevichExcisionIso_boundary
    (F : Sheaf (SmoothSite.nisnevichTopology S) AddCommGrpCat.{max u t}) (n : ℕ)
    (x : H (SmoothSite.nisnevichTopology S) F n sq.X₂) :
    letI : Mono sq.f₁₃ := hpb.mono_snd_of_mono
    (relativeNisnevichExcisionIso sq hpb z hcomp F (n + 1)).hom
        (relativeBoundary (SmoothSite.nisnevichTopology S) sq.f₂₄ F n x) =
      relativeBoundary (SmoothSite.nisnevichTopology S) sq.f₁₃ F n
        ((presheaf (SmoothSite.nisnevichTopology S) F n).map sq.f₁₂.op x) := by
  let : Mono sq.f₁₃ := hpb.mono_snd_of_mono
  exact relativeBoundary_restriction _ _ _ _ _ _ F n x

end Nisnevich

end Motivic.SheafCohomology
