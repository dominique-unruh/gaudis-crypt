# Planned renamings

- [x] fvP_extend -> Lens.liftProbLensRange (also move to Lenses.lean)
- [x] Lens.update -> Lens.liftFunction, Lens.updateK -> Lens.liftSubProbability (to have a nice family of Lens.lift... functions)
- [ ] type Program -> ProgramDenotation
- [x] type ProbLensRange -> Footprint (also TotLensRange -> DetermFootprint; prob-infixed names like inProbRange -> inFootprint, probRange -> footprint, etc.; exception: wp_shift_input_prob kept as-is)
- [ ] Maybe: add `Lens.lift [LensLift T] (Lens a b) (T a) : T b` to be able to uniformly write
  `lens.lift footprint/program/deterministic_function...` Also Lens.updateK and Lens.update and 
  fall under the same concept. [Dominique tried: tricky because of instance search and universes and stuff]
