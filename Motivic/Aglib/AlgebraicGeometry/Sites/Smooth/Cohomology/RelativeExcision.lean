module

public import Motivic.Aglib.CategoryTheory.Sites.SheafCohomology.Relative.Excision
public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Nisnevich.DistinguishedSquare

/-!
# Relative excision on smooth sites
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite AlgebraicGeometry

universe w t v u

namespace CategoryTheory.Sheaf.LargeCohomology
open _root_.AlgebraicGeometry.Scheme
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

end CategoryTheory.Sheaf.LargeCohomology
