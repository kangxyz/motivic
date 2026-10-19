/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Composition.Incidence.IntermediateModules

/-! # Literal scalar-action consumers for actual intermediate homology -/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Motivic.MotivicTest.IntermediateTorModules
open _root_.AlgebraicGeometry.Scheme.Products

variable {S X Y Z : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} {h : Z ⟶ S}
  (F : FiniteCorrespondenceGenerator f g) (G : FiniteCorrespondenceGenerator g h)

section Tor

variable [Flat f] [Smooth g] [IsSeparated g] [Flat h]
  (w : F.incidence G) (n : ℕ)

/-- The actual Tor recovery has the original element, not an arbitrary chosen representative. -/
theorem actualTorRecovered (x : F.incidenceTor G w n) :
    (F.incidenceTorOnIncidenceRestrictIso G w n).hom x = x := rfl

/-- The constructed incidence action recovers multiplication by every ambient scalar. -/
theorem actualTorScalar (r : F.incidenceAmbientStalk G w) (x : F.incidenceTor G w n) :
    (F.incidenceTorOnIncidenceRestrictIso G w n).hom (r • x) =
      r • (F.incidenceTorOnIncidenceRestrictIso G w n).hom x :=
  map_smul (F.incidenceTorOnIncidenceRestrictIso G w n).hom.hom r x

end Tor

variable [IsSeparated g] (w : F.incidence G)
  (s : List (F.incidenceAmbientStalk G w))
  (hker : RingHom.ker ((correspondenceTripleInclusion f g h).stalkMap
    (F.incidenceInclusion G w)).hom = Ideal.ofList s) (n : ℕ)

/-- Actual coefficient homology descends without a regular-sequence premise. -/
theorem actualKoszulRecovered
    (x : (_root_.ChainComplex.Koszul.coefficientComplex (F.incidenceSupportStalkModule G w)
        s).homology n) :
    (F.incidenceKoszulOnIncidenceRestrictIso G w s hker n).hom x = x := rfl

/-- All ambient scalar actions are retained on the genuinely descended homology. -/
theorem actualKoszulScalar (r : F.incidenceAmbientStalk G w)
    (x : (_root_.ChainComplex.Koszul.coefficientComplex (F.incidenceSupportStalkModule G w)
        s).homology n) :
    (F.incidenceKoszulOnIncidenceRestrictIso G w s hker n).hom (r • x) =
      r • (F.incidenceKoszulOnIncidenceRestrictIso G w s hker n).hom x :=
  map_smul (F.incidenceKoszulOnIncidenceRestrictIso G w s hker n).hom.hom r x

end Motivic.MotivicTest.IntermediateTorModules
