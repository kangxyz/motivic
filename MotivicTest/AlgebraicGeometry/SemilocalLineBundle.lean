/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Frames.FiniteFiber
public import Mathlib.Data.ZMod.Basic

/-! # Actual semilocal and whole-fibre trivialization consumers -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.Invertible

universe u

/-- The semilocal hypothesis supplies the existing Picard instance. -/
example (R : CommRingCat.{u}) [Finite (MaximalSpectrum R)] (M : ModuleCat.{u} R)
    [Module.Invertible R M] :
    tilde M ≅ SheafOfModules.unit (Spec R).ringCatSheaf :=
  tildeUnitIsoOfSubsingletonPic R M

/-- The locally rank-one sheaf is unchanged in the constructed isomorphism. -/
example (R : CommRingCat.{u}) [Finite (MaximalSpectrum R)]
    (M : (Spec R).Modules) (hM : IsLocallyRankOne (Spec R) M) :
    Nonempty (M ≅ SheafOfModules.unit (Spec R).ringCatSheaf) :=
  semilocalLineBundle_trivial R ⟨M, hM⟩

/-- The pulled-back original line bundle is trivial on the entire finite
scheme-theoretic fibre, with no reduced-fibre replacement. -/
example {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (y : Y) (L : LineBundle X) :
    Nonempty ((Scheme.Modules.pullback (f.fiberι y)).obj L.val ≅
      SheafOfModules.unit (f.fiber y).ringCatSheaf) :=
  finiteFiberLineBundle_trivial f y (pullbackLineBundle (f.fiberι y) L)

/-- The nonreduced affine scheme Spec(Z/4) is included. -/
example (L : LineBundle (Spec (.of (ZMod 4)))) :
    Nonempty (L.val ≅ SheafOfModules.unit (Spec (.of (ZMod 4))).ringCatSheaf) :=
  semilocalLineBundle_trivial (.of (ZMod 4)) L

/-- The empty affine scheme Spec(Z/1) is included. -/
example (L : LineBundle (Spec (.of (ZMod 1)))) :
    Nonempty (L.val ≅ SheafOfModules.unit (Spec (.of (ZMod 1))).ringCatSheaf) :=
  semilocalLineBundle_trivial (.of (ZMod 1)) L
