/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Aglib.AlgebraicGeometry.Sites.NisnevichHenselianEvaluation

/-!
# Consumers of ordinary henselian Nisnevich evaluation

These consumers exercise exact evaluation and the actual ordinary sheafification
unit for the big Nisnevich site. Local Artinian hypotheses do not include
reducedness. Type-valued and abelian-group-valued sheafification are both tested
at the size supported by the existing ordinary sheafification APIs.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Motivic.Nisnevich

universe u

example (R : Type u) [CommRing R] [HenselianLocalRing R]
    {F G : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)} (φ : F ⟶ G)
    [Presheaf.IsLocallySurjective topology φ] :
    Function.Surjective (φ.app (op (Spec (.of R)))) :=
  surjective_app_of_isLocallySurjective_of_henselian R φ

example (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    {F G : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}} (φ : F ⟶ G)
    [Presheaf.IsLocallyInjective topology φ] :
    Function.Injective (φ.app (op (Spec (.of R)))) :=
  injective_app_of_isLocallyInjective_of_artinian R φ

example (R : Type u) [CommRing R] [HenselianLocalRing R]
    (F : Scheme.{u}ᵒᵖ ⥤ Type (u + 1)) :
    IsIso ((toSheafify topology F).app (op (Spec (.of R)))) :=
  isIso_toSheafify_app_of_henselian R F

example (R : Type u) [CommRing R] [HenselianLocalRing R]
    (F : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso ((toSheafify topology F).app (op (Spec (.of R)))) :=
  isIso_toSheafify_app_of_henselian R F

example (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (F : Scheme.{u}ᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    IsIso ((toSheafify topology F).app (op (Spec (.of R)))) :=
  isIso_toSheafify_app_of_artinian R F

example (R : Type u) [CommRing R] :
    (ringEvaluation R).Additive := inferInstance

example (R : Type u) [CommRing R] :
    PreservesFiniteLimits (ringEvaluation R) := inferInstance

example (R : Type u) [CommRing R] [HenselianLocalRing R]
    {F G : Sheaf topology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    Epi ((ringEvaluation R).map φ) := inferInstance

example (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    {F G : Sheaf topology AddCommGrpCat.{u + 1}} (φ : F ⟶ G) [Epi φ] :
    Function.Surjective (φ.hom.app (op (Spec (.of R)))) :=
  surjective_app_of_epi_of_artinian R φ

example (R : Type u) [CommRing R] [HenselianLocalRing R]
    (S : ShortComplex (Sheaf topology AddCommGrpCat.{u + 1})) (hS : S.Exact) :
    (S.map (ringEvaluation R)).Exact := exact_map_ringEvaluation_of_henselian R S hS

example (R : Type u) [CommRing R] [IsLocalRing R] [IsArtinianRing R]
    (S : ShortComplex (Sheaf topology AddCommGrpCat.{u + 1})) (hS : S.Exact) :
    (S.map (ringEvaluation R)).Exact := exact_map_ringEvaluation_of_artinian R S hS

example (K : Type u) [Field K] : ringEvaluation K = fieldEvaluation topology K := rfl

set_option linter.hashCommand false in
#print axioms Motivic.Nisnevich.surjective_app_of_isLocallySurjective_of_henselian
set_option linter.hashCommand false in
#print axioms Motivic.Nisnevich.injective_app_of_isLocallyInjective_of_artinian
set_option linter.hashCommand false in
#print axioms Motivic.Nisnevich.isIso_toSheafify_app_of_henselian
set_option linter.hashCommand false in
#print axioms Motivic.Nisnevich.isIso_toSheafify_app_of_artinian
set_option linter.hashCommand false in
#print axioms Motivic.Nisnevich.surjective_app_of_epi_of_henselian
set_option linter.hashCommand false in
#print axioms Motivic.Nisnevich.surjective_app_of_epi_of_artinian
set_option linter.hashCommand false in
#print axioms Motivic.Nisnevich.exact_map_ringEvaluation_of_henselian
set_option linter.hashCommand false in
#print axioms Motivic.Nisnevich.exact_map_ringEvaluation_of_artinian
