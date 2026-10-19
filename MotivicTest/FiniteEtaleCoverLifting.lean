module

import Motivic.Aglib.AlgebraicGeometry.Sites.Etale.SeparatedFiniteType.CoverLifting

/-! # Regression tests for actual small-site cover lifting -/

open _root_.AlgebraicGeometry.Scheme (SmoothSite EtaleSeparatedFiniteType)
open CategoryTheory AlgebraicGeometry

universe u

example {B : Scheme.{u}} (X : SmoothSite B) :
    (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.toSmoothSite X).IsCocontinuous
      (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.nisnevichTopology X.left)
          (SmoothSite.nisnevichTopology B) :=
  inferInstance

example {B : Scheme.{u}} (X : SmoothSite B) (U : EtaleSeparatedFiniteType X.left)
    (R : Sieve ((_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.toSmoothSite X).obj U))
    (hR : R ∈ SmoothSite.nisnevichTopology B _) :
    R.functorPullback (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.toSmoothSite X) ∈
      _root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.nisnevichTopology X.left U :=
  (_root_.AlgebraicGeometry.Scheme.EtaleSeparatedFiniteType.toSmoothSite X).cover_lift _ _ hR

