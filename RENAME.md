# Planned renamings

- [x] fvP_extend -> Lens.liftProbLensRange (also move to Lenses.lean)
- [x] Lens.update -> Lens.liftFunction, Lens.updateK -> Lens.liftSubProbability (to have a nice family of Lens.lift... functions)
- [x] type Program -> ProgramDenotation (also SubProbability.toProgram -> toProgramDenotation, incl. wp_/inRange_ theorem names; range/footprint *file* names kept as-is)
- [x] type ProbLensRange -> Footprint (also TotLensRange -> DetermFootprint; prob-infixed names like inProbRange -> inFootprint, probRange -> footprint, etc.; exception: wp_shift_input_prob kept as-is)
- [x] class disjoint -> Lens.Disjoint (also disjoint.iff/disjoint.symm -> Lens.Disjoint.iff/.symm; snake_case lemma names like `Lens.footprint_le_compl_of_disjoint`, `disjoint3`/`disjoint3'` kept as-is, Mathlib-style; the unrelated `GranularitySpec.disjoint` *field* is untouched)
- [x] paramListToTuple -> typeListToTuple
- [x] type LocalVariableState -> ProcedureScope (incl. ProcedureSignature.LocalVariableState -> ProcedureSignature.ProcedureScope, field vars -> localVars, LocalVariableState.varsL -> ProcedureScope.localVarsL, Lens.intoVars -> Lens.intoLocalVars)
- [x] ProcedureState.localL -> ProcedureState.scopedL
- [x] file Attic/TypesModules.lean -> Attic/TypedModules.lean
