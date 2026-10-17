/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
import Motivic.Aglib.RingTheory.Bertini.MovingPointCoefficientDimension
import Lean.Util.CollectAxioms

/-! # The actual generated coefficient field, including finite residue extensions -/
open QuadraticIncidence.MovingPointChart

example (k R B : Type) [Field k] [CommRing R] [IsDomain R] [CommRing B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    [Module.Finite R B] (d : ℕ) (i₀ : Fin d) (t : B)
    (E : Type) [Field E] [Algebra k E] [Algebra (Ring B d i₀ t) E]
    [IsScalarTower k (Ring B d i₀ t) E]
    (hd : Algebra.trdeg k R = (d + 1 : ℕ)) :
    Algebra.trdeg k (IncidenceCoefficientField.field k (Ring B d i₀ t) E) ≤
      (2 * d : ℕ) :=
  trdeg_coefficientField_le_twice k R B d i₀ t E hd

open IncidenceCoefficientField Lean in
run_cmd do
  for name in #[``lift, ``lift_coe, ``tower_ground, ``tower_target,
      ``image_tower_ground, ``image_tower_target, ``fractionRing, ``imageMap_surjective,
      ``trdeg_coefficientField_le, ``trdeg_coefficientField_le_twice] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual moving-point coefficient field bound: standard foundations only."
