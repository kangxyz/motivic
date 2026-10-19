/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.AlgebraicGeometry.Correspondences.Nisnevich.Cech.IncidencePairing
public import Lean.Util.CollectAxioms

/-!
# Čech pairing with the genuine incidence Tor coefficient function

The supplied alternate support map is unrestricted except for its two literal
compatibility equations. No flatness, reduction or separability is assumed.
-/

@[expose] public noncomputable section

open _root_.AlgebraicGeometry.Scheme (IntegralCycle)
open _root_.AlgebraicGeometry.Scheme (SmoothSite)
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Motivic
open Motivic.FiniteCorrespondenceGenerator

universe u

namespace MotivicTest.NisnevichCechIncidencePairing

variable {k : Type u} [Field k] {T X Y V : SmoothSite (Spec (.of k))}

example (G : FiniteCorrespondenceGenerator T.hom X.hom)
    (A : FiniteCorrespondenceGenerator X.hom V.hom)
    (m : G.incidence A ⟶ pullback T.hom V.hom) [IsFinite m]
    (q : V ⟶ Y) [Etale q.left]
    (hs : G.incidenceMap A ≫ pullback.fst T.hom V.hom = m ≫ pullback.fst T.hom V.hom)
    (ht : G.incidenceMap A ≫ pullback.snd T.hom V.hom ≫ q.left =
      m ≫ pullback.snd T.hom V.hom ≫ q.left) :
    ∃ β : Cor.mk T ⟶ Cor.mk (SmoothSite.etalePullback q q),
      β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackFst q q) =
        G.incidenceTorCorrespondence k A ∧
      FiniteCorrespondence.toIntegralCycle (f := T.hom) (g := V.hom)
        (β ≫ (Cor.graphFunctor k).map (SmoothSite.etalePullbackSnd q q)) =
        IntegralCycle.finitePushforward m (IntegralCycle.ofGenericCoefficients (G.incidence A)
          (G.incidenceTorCoefficient (S := Spec (.of k)) A)) :=
  exists_cech_pairing_of_incidenceTor k G A m q hs ht

open Lean in
run_cmd do
  for name in #[``exists_cech_pairing_of_generic_coefficients,
      ``exists_cech_pairing_of_incidenceTor] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"

end MotivicTest.NisnevichCechIncidencePairing
