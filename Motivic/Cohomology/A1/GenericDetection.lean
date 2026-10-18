/-
Copyright (c) 2026 Motivic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.A1.DenseOpenAffineDetection

/-!
# Affine local zero detection from a nonempty open

Over an infinite field, a section of a homotopy-invariant presheaf with transfers
on a smooth integral affine scheme that vanishes on an original nonempty open
vanishes on actual affine neighborhoods covering every point. The original open
need not be affine. No sheaf hypothesis is required.

This entry retains local-zero conclusions. Arbitrary smooth objects and actual
sheafification detection are handled in the separate `DenseOpenLocalDetection`
and `PresheafGenericModelDetection` leaves. Finite fields remain a separate obligation.
-/
