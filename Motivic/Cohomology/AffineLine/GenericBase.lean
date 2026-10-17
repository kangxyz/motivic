/-
Copyright (c) 2026 Motivic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.SheafCohomologyRelativeLineHigherVanishing

/-!
# Original relative affine-line higher classes over a generic base open

Over any field and a smooth integral affine base, each original ordinary
Nisnevich cohomology class in degree at least two becomes zero after two nonzero
base localizations and restriction over an affine generic base open. The whole
affine-line parameter and original restriction maps are retained. Coefficient
universe and ordinary HasExt remain explicit; no homotopy invariance is assumed.

The open may depend on the class. Generic-base H1 and the all-positive generic
rank-zero join are not supplied by this entry.
-/
