/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Modules.Invertible.Semilocal
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Unit trivializations on complete finite fibres

A finite affine scheme has semilocal global sections. Transport along the
actual affine comparison therefore trivializes every line bundle. Applying
this to the scheme-theoretic fibre of a finite morphism gives a unit
trivialization on the whole fibre, including all nilpotents and components.
This does not extend that trivialization to a neighborhood of the fibre.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Invertible

/-- Every line bundle on an affine scheme with finitely many points is
trivial. Finite carrier does not mean the scheme must be reduced. -/
theorem finiteAffineLineBundle_trivial (X : Scheme.{u}) [IsAffine X] [Finite X]
    (L : LineBundle X) : Nonempty (L.val ≅ SheafOfModules.unit X.ringCatSheaf) := by
  have : Finite (PrimeSpectrum Γ(X, ⊤)) :=
    Finite.of_equiv X X.isoSpec.hom.homeomorph.toEquiv
  have : Finite (MaximalSpectrum Γ(X, ⊤)) :=
    Finite.of_injective MaximalSpectrum.toPrimeSpectrum MaximalSpectrum.toPrimeSpectrum_injective
  obtain ⟨e⟩ := semilocalLineBundle_trivial Γ(X, ⊤) (pullbackLineBundle X.isoSpec.inv L)
  exact ⟨((Scheme.Modules.pullbackId X).app L.val).symm ≪≫
    ((Scheme.Modules.pullbackCongr X.isoSpec.hom_inv_id).app L.val).symm ≪≫
    ((Scheme.Modules.pullbackComp X.isoSpec.hom X.isoSpec.inv).app L.val).symm ≪≫
    (Scheme.Modules.pullback X.isoSpec.hom).mapIso e ≪≫ pullbackUnitIso X.isoSpec.hom⟩

/-- A line bundle on the actual entire scheme-theoretic fibre of a finite
morphism has a unit trivialization. No flatness, Noetherianity, reducedness,
nonemptiness or rational-point hypothesis is used. -/
theorem finiteFiberLineBundle_trivial {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (y : Y) (L : LineBundle (f.fiber y)) :
    Nonempty (L.val ≅ SheafOfModules.unit (f.fiber y).ringCatSheaf) := by
  have : IsAffine (f.fiber y) := by
    dsimp [Scheme.Hom.fiber]
    infer_instance
  exact finiteAffineLineBundle_trivial (f.fiber y) L

end AlgebraicGeometry.Scheme.Modules.Invertible
