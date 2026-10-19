/-
Copyright (c) 2026 Motivic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.LocalVanishing.GenericBase.PositiveZero

/-!
# Original relative affine-line classes over a generic base open

Over any field and a smooth integral affine base, each original ordinary
Nisnevich cohomology class in degree at least two becomes zero after two nonzero
base localizations and restriction over an affine generic base open. No homotopy
invariance is assumed in those degrees. For homotopy-invariant Nisnevich sheaves
with transfers, the same assertion holds in every positive degree, including H1.

The whole affine-line parameter and literal original restriction maps are
retained. Coefficient universe and ordinary HasExt remain explicit. The open may
depend on the class; this does not assert strict A1 invariance on smooth schemes.
-/
