module

import Motivic.AlgebraicGeometry.Sites.FiniteEtaleCoverLifting

/-! # Regression tests for actual small-site cover lifting -/

open CategoryTheory AlgebraicGeometry Motivic

universe u

example {B : Scheme.{u}} (X : SmoothSite B) :
    (FiniteEtaleSite.toSmoothSite X).IsCocontinuous
      (FiniteEtaleSite.nisnevichTopology X.left) (SmoothSite.nisnevichTopology B) :=
  inferInstance

example {B : Scheme.{u}} (X : SmoothSite B) (U : FiniteEtaleSite X.left)
    (R : Sieve ((FiniteEtaleSite.toSmoothSite X).obj U))
    (hR : R ∈ SmoothSite.nisnevichTopology B _) :
    R.functorPullback (FiniteEtaleSite.toSmoothSite X) ∈
      FiniteEtaleSite.nisnevichTopology X.left U :=
  (FiniteEtaleSite.toSmoothSite X).cover_lift _ _ hR

