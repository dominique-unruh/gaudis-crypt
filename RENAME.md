# Planned renamings

- [x] fvP_extend -> Lens.liftProbLensRange (also move to Lenses.lean)
- [x] Lens.update -> Lens.liftFunction, Lens.updateK -> Lens.liftSubProbability (to have a nice family of Lens.lift... functions)
- [x] type Program -> ProgramDenotation (also SubProbability.toProgram -> toProgramDenotation, incl. wp_/inRange_ theorem names; range/footprint *file* names kept as-is)
- [x] type ProbLensRange -> Footprint (also TotLensRange -> DetermFootprint; prob-infixed names like inProbRange -> inFootprint, probRange -> footprint, etc.; exception: wp_shift_input_prob kept as-is)
