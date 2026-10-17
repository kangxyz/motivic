/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.EffectiveCartierDivisor.Diagonal

/-! # Original diagonal ideals and their specified canonical sections -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Hom Scheme.Modules.Invertible

universe u

namespace Motivic.MotivicTest.DiagonalIdeal

/-- No smoothness of the ambient complement, or reduction of the closed scheme,
is part of the locality interface. -/
example {D X : Scheme.{u}} (i : D ⟶ X) [IsClosedImmersion i]
    (U : X.Opens) (hU : Set.range i ⊆ U)
    (h : IsLocallyRankOne U.toScheme (idealModule (i ∣_ U))) :
    IsLocallyRankOne X (idealModule i) :=
  idealModule_isLocallyRankOne_of_neighborhood i U hU h

/-- The finite-flat relative divisor is retained as the original closed map. -/
example {S X D : Scheme.{u}} (p : X ⟶ S) (i : D ⟶ X) [IsClosedImmersion i]
    [IsFinite (i ≫ p)] [Flat (i ≫ p)] [LocallyOfFinitePresentation (i ≫ p)]
    (U : X.Opens) (hU : Set.range i ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ p)] :
    IsLocallyRankOne X (idealModule i) :=
  idealModule_isLocallyRankOne_of_smooth_near_range p i U hU

/-- A canonical section is constructed, rather than supplied as a hypothesis. -/
example {S X : Scheme.{u}} (p : X ⟶ S) (s : S ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ p = 𝟙 S) (U : X.Opens) (hU : Set.range s ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ p)] :
    Γ((sectionDivisorLineBundle p s hs U hU).val, ⊤) :=
  sectionDivisorCanonicalSection p s hs U hU

/-- The line-bundle object is definitionally the original ideal. -/
example {S X : Scheme.{u}} (p : X ⟶ S) (s : S ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ p = 𝟙 S) (U : X.Opens) (hU : Set.range s ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ p)] :
    (sectionIdealLineBundle p s hs U hU).val = idealModule s := rfl

/-- The produced section retains the specified ideal inclusion exactly. -/
example {S X : Scheme.{u}} (p : X ⟶ S) (s : S ⟶ X) [IsClosedImmersion s]
    (hs : s ≫ p = 𝟙 S) (U : X.Opens) (hU : Set.range s ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ p)] :
    Scheme.Modules.InternalHom.sectionHomEquiv X (idealModule s)
        (SheafOfModules.unit X.ringCatSheaf) ⊤
        (sectionDivisorCanonicalSection p s hs U hU) =
      (SheafOfModules.overFunctor X.ringCatSheaf ⊤).map (idealInclusion s) :=
  sectionDivisorCanonicalSection_eq_inclusion p s hs U hU

/-- The original diagonal ideal, not a substitute Picard representative. -/
example {S C : Scheme.{u}} (p : C ⟶ S) [IsSeparated p]
    (U : (pullback p p).Opens) (hU : Set.range (pullback.diagonal p) ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ pullback.fst p p)] :
    IsLocallyRankOne (pullback p p) (idealModule (pullback.diagonal p)) :=
  diagonal_idealModule_isLocallyRankOne p U hU

/-- In the mixed product the compactification has no smoothness hypothesis. -/
example {S C X : Scheme.{u}} (j : C ⟶ X) (p : X ⟶ S) [IsSeparated p]
    (U : (pullback (j ≫ p) p).Opens)
    (hU : Set.range (pullback.lift (𝟙 C) j (Category.id_comp (j ≫ p))) ⊆ U)
    [SmoothOfRelativeDimension 1 (U.ι ≫ pullback.fst (j ≫ p) p)] :
    IsLocallyRankOne (pullback (j ≫ p) p)
      (idealModule (pullback.lift (𝟙 C) j (Category.id_comp (j ≫ p)))) :=
  graph_idealModule_isLocallyRankOne j p U hU

#print axioms graph_idealModule_isLocallyRankOne
#print axioms idealModule_isLocallyRankOne_of_neighborhood
#print axioms section_idealModule_isLocallyRankOne
#print axioms sectionDivisorCanonicalSection_eq_inclusion
#print axioms diagonal_idealModule_isLocallyRankOne

end Motivic.MotivicTest.DiagonalIdeal
