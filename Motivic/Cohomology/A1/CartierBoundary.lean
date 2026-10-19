/-
Copyright (c) 2026 Motivic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Motivic.Cohomology.Cartier.DirectImage
public import Motivic.Cohomology.A1.Boundary.Presheaf.EtaleExcision

/-!
# Original Cartier boundaries and positive open direct images

The public ordinary-cohomology endpoint retains the original section quotient,
small sheafification, genuine closed inverse image and positive right-derived
open direct image. It requires an infinite field, current positive-degree
cohomology invariance, the original boundary epimorphism, ordinary HasExt in
universe u+1, and a supplied smooth Cartier complement. No PerfectField input
is needed once that smooth pair is given.

General presheaf coefficient and etale-excision comparisons retain their own
weaker hypotheses. This entry does not supply the original Epi producer,
current-degree invariance or full strict A1 invariance.
-/
