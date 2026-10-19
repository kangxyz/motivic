module

public import Motivic.Aglib.AlgebraicGeometry.Sites.Smooth.Cohomology.RelativeExcision

/-! # Direct checks of geometric relative Nisnevich excision -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite)

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry
open  _root_.CategoryTheory.Sheaf.LargeCohomology

universe w u

example {S : Scheme.{u}}
    [HasSheafify (_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology S) AddCommGrpCat.{u +
        1}]
    [HasExt.{w} (Sheaf (_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology S)
        AddCommGrpCat.{u + 1})]
    (sq : Square (SmoothSite S)) (hpb : sq.IsPullback)
    [IsOpenImmersion sq.f₂₄.left] [Etale sq.f₃₄.left]
    {Z : Scheme.{u}} (z : Z ⟶ sq.X₄.left) [IsClosedImmersion z]
    (hcomp : Set.range z = (Set.range sq.f₂₄.left)ᶜ)
    [IsIso (pullback.snd sq.f₃₄.left z)]
    (F : Sheaf (_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology S) AddCommGrpCat.{u +
        1}) (n : ℕ) :
    IsIso (relativeRestriction.{w, u + 1, u, u + 1}
        (_root_.AlgebraicGeometry.Scheme.SmoothSite.nisnevichTopology S)
      sq.f₁₃ sq.f₂₄ sq.f₁₂ sq.f₃₄ sq.fac.symm F n) :=
  isIso_relativeRestriction_nisnevich.{w, u + 1, u} sq hpb z hcomp F n

