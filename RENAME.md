# Planned renamings

- [ ] Lens.lean -> Lenses.lean (also the namespace)
- [ ] type Program -> Denotation
- [ ] type ProbLensRange -> Footprint
- [ ] fvP_extend -> ProbLensRange.lift or Lens.liftFootprint (also move to Lenses.lean)
- [ ] Maybe: add `Lens.lift [LensLift T] (Lens a b) (T a) : T b` to be able to uniformly write
  `lens.lift footprint/program/deterministic_function...` Also Lens.updateK and Lens.update and 
  fall under the same concept.
- [ ] Various names with `prob` in them that were called so merely because of the transition from TotLensRange.
