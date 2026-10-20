/-
Copyright (c) 2026 Motivic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.DenseOpen.AffineDetection

/-!
# Affine local zero detection from a nonempty open

Over an infinite field, a section of a homotopy-invariant presheaf with transfers
on a smooth integral affine scheme that vanishes on an original nonempty open
vanishes on actual affine neighborhoods covering every point. The original open
need not be affine. No sheaf hypothesis is required.

This infinite-field entry retains local-zero conclusions. The arbitrary-smooth
and actual generic-model sheafification detection results have the separate
`Motivic.Cohomology.A1.LocalVanishing.DenseOpen.Detection` and
`Motivic.Cohomology.A1.LocalVanishing.Presheaf.GenericModel.Detection` owners.
For finite-field local-zero results and their own coefficient-universe and
good-open hypotheses, see
`Motivic.Cohomology.A1.LocalVanishing.FiniteField.IntegralAffineLocalZero`.
-/
