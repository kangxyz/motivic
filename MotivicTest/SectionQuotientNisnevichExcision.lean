module
import Motivic.Cohomology.A1.Boundary.NisnevichSectionExcision
/-! # Actual neighborhood relations reflect without homotopy invariance -/
set_option linter.hashCommand false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe v u
namespace Motivic.SmoothSite
open _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.SmoothSite
variable {S : Scheme.{u}} (sq : Square (SmoothSite S))
  (F : Sheaf (nisnevichTopology S) AddCommGrpCat.{v})
  (hpb : sq.IsPullback) [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
  {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
  (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
  [IsIso (pullback.snd sq.f₃₄.left z)]
example : Mono (sectionQuotientRestriction sq F) :=
  sectionQuotientRestriction_mono sq F hpb z hcomp
example (a : F.obj.obj (op sq.X₂)) (c : F.obj.obj (op sq.X₃))
    (h : F.obj.map sq.f₁₂.op a = F.obj.map sq.f₁₃.op c) :
    ∃ b : F.obj.obj (op sq.X₄), F.obj.map sq.f₂₄.op b = a ∧
      F.obj.map sq.f₃₄.op b = c :=
  exists_section_extension_of_neighborhood sq F hpb z hcomp a c h
#print axioms sectionQuotientRestriction_mono
#print axioms exists_section_extension_of_neighborhood
end Motivic.SmoothSite
