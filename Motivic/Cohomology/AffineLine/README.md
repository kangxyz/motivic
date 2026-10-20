# Ordinary affine-line cohomology

`Motivic.Cohomology.AffineLine` selects the original ordinary big-smooth
Nisnevich vanishing results. Over any field, `H^(n+2)(A1,F)=0` for arbitrary
abelian coefficients; `H^(n+1)(A1,F)=0` for HI sheaves with transfers. Ordinary
`HasExt` and coefficient universe `u+1` remain explicit. The groups and maps
are original ordinary cohomology. These statements do not supply a general
small-site comparison or strict invariance on arbitrary smooth schemes.

`Motivic.Cohomology.AffineLine.GenericBase` selects classwise eventual higher
vanishing for arbitrary ordinary coefficients over any field and a smooth
integral affine base, plus all-positive vanishing for HI transfer sheaves. It
keeps the original whole line, restrictions, coefficient universe and `HasExt`; the base open may
depend on the cohomology class. See
[generic-base local vanishing](../A1/LocalVanishing/README.md).

The independent [ordinary transfer construction](../../Transfers/Cohomology/README.md)
supplies actual transfer actions. [Strict invariance](../A1/README.md) is a
separate endpoint with its own field and coefficient conditions. General
[large sheaf cohomology](../../Aglib/CategoryTheory/Sites/SheafCohomology/Large/README.md)
provides the native groups and original restriction maps.
