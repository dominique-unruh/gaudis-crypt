import GaudisCrypt.Syntax.Syntax
import GaudisCrypt.Lib.EC.List
import GaudisCrypt.Logic.PRHLWp

/-!
# EasyCrypt's iteration of a procedure over a list (`theories/looping/IterProc.eca`)

The abstract type `t` is a section variable, so a `clone` is an application.  Only what ported
developments use is here.

`Iter(O).iter l` is denotationally the calls of `O.f` on the elements of `l`, in order
(`Iter.iter_denotation`, through `iterDen`).  From that:

* `iter_ll` and `iter_inv` are EC's, as stated there;
* `iter_cat`, `iter_perm` and `iter1_perm` are EC's `equiv`s with `={glob O}` as **denotational
  equalities** (exception E9): stronger, valid for any `O`, and used by rewriting.  EC's
  `Iter(O).iters(l₁, l₂)` and `Iter(O).iter_1s(x, l)` are spelled as the composite denotations
  they stand for, and EC's `iter2_eq` (`iter_12 ~ iter_21`) is the commutation of two calls of
  `O.f`.
-/

namespace GaudisCrypt.EC.IterProc

open GaudisCrypt GaudisCrypt.EC

variable (t : Type) [Inhabited t]

moduletype Orcl {
  proc f (x : t) -> Unit;
}

module Iter using (O : Orcl t) {
  proc iter (l : List t) : Unit {
    while (!(List.isEmpty $l)) {
      _ <- call O.f (head (default : t) $l);
      l <- drop 1 $l;
    }
    return ()
  };
}

/-! ## The lemmas -/

variable {t : Type} [Inhabited t]

/-- The calls of `f` on the elements of a list, in order: what `Iter(O).iter` computes. -/
noncomputable def iterDen (f : t → ProgramDenotation VariableAssignment Unit) :
    List t → ProgramDenotation VariableAssignment Unit
  | [] => pure ()
  | x :: xs => f x >>= fun _ => iterDen f xs

/-- A loop calling `f` on the head of the list in slot `lv` and dropping it, from a state whose
slot holds `xs`: the calls of `f` on `xs`, the slot emptied. -/
theorem iter_loop (lv : VariableName) (hlv : lv.type = List t) (c : Getter Bool ProgramState)
    (f : Procedure (procsig (t) → Unit)) (args : Getter t ProgramState)
    (y : Setter (List t) ProgramState) (e : Getter (List t) ProgramState)
    (get : VariableAssignment → List t) (set : List t → VariableAssignment → VariableAssignment)
    (hset_get : ∀ v m, get (set v m) = v) (hset_set : ∀ v w m, set w (set v m) = set w m)
    (hget_set : ∀ m, set (get m) m = m)
    (hc : ∀ σ, c.get σ = !(get σ.locals).isEmpty)
    (ha : ∀ σ, args.get σ = EC.head default (get σ.locals))
    (hy : ∀ v σ, y.set v σ = ⟨σ.globals, set v σ.locals⟩)
    (he : ∀ σ, e.get σ = EC.drop 1 (get σ.locals)) :
    ∀ (xs : List t) (τ : ProgramState), get τ.locals = xs →
      programDenotation (StmtWithHoles.while c
          (StmtWithHoles.seq (Stmt.call Setter.throwaway f args) (StmtWithHoles.assign y e))) τ =
        (iterDen (fun x => procedureDenotation f x) xs τ.globals).hbind fun r =>
          pure ((), ⟨r.2, set [] τ.locals⟩)
  | [], τ, hl => by
      rw [programDenotation_while_of_false (by rw [hc, hl]; rfl)]
      show _ = (pure ((), τ.globals) : SubProbability _).hbind _
      rw [SubProbability.pure_hbind, ← hl, hget_set]
  | x :: xs, τ, hl => by
      rw [programDenotation_while_unfold, if_pos (by rw [hc, hl]; rfl)]
      simp only [programDenotation_seq, ProgramDenotation.bind_apply, Stmt.call,
        StmtWithHoles.call, programDenotation_call'_apply, SubProbability.bind_assoc,
        SubProbability.pure_bind, programDenotation_assign_apply]
      have hx : args.get τ = x := by rw [ha, hl]; rfl
      have key : ∀ z : Unit × ProgramState,
          programDenotation (StmtWithHoles.while c
            (StmtWithHoles.seq (Stmt.call Setter.throwaway f args) (StmtWithHoles.assign y e)))
            (y.set (e.get (Setter.throwaway.set (f.return_val.get z.2)
                (ProgramState.globalL.set z.2.globals τ)))
              (Setter.throwaway.set (f.return_val.get z.2)
                (ProgramState.globalL.set z.2.globals τ))) =
          (iterDen (fun x => procedureDenotation f x) xs z.2.globals).hbind fun r =>
            pure ((), ⟨r.2, set [] τ.locals⟩) := by
        intro z
        have hs : y.set (e.get (Setter.throwaway.set (f.return_val.get z.2)
            (ProgramState.globalL.set z.2.globals τ))) (Setter.throwaway.set (f.return_val.get z.2)
              (ProgramState.globalL.set z.2.globals τ)) = ⟨z.2.globals, set xs τ.locals⟩ := by
          rw [hy, he]
          show (⟨z.2.globals, set (EC.drop 1 (get τ.locals)) τ.locals⟩ : ProgramState) = _
          rw [hl]; rfl
        rw [hs, iter_loop lv hlv c f args y e get set hset_get hset_set hget_set hc ha hy he xs _
          (hset_get _ _)]
        simp only [hset_set]
      rw [hx]
      refine (congrArg (fun k => programDenotation f.body _ >>= k) (funext key)).trans ?_
      show _ = ((procedureDenotation f x >>= fun _ => iterDen (fun x => procedureDenotation f x) xs)
        τ.globals).hbind _
      rw [ProgramDenotation.bind_apply]
      simp only [procedureDenotation, SubProbability.hbind_bind, SubProbability.pure_bind,
        SubProbability.hbind_assoc]
      rw [SubProbability.hbind_eq_bind]
      rfl

theorem Iter.iter_denotation (O : Orcl t) (l : List t) :
    procedureDenotation (Module.app (Iter.iter t) O).procedure l =
      iterDen (fun x => procedureDenotation (Orcl.f t O).procedure x) l := by
  rw [Iter.iter.apply_simp, Module.procedure_proc']
  funext g
  simp only [procedureDenotation, ProcedureWithHoles.instantiate, Iter.iter.procedure,
    StmtWithHoles.instantiate]
  let lv : VariableName := .mk "l" (List t)
  refine (congrArg (fun μ => SubProbability.hbind μ _) (iter_loop lv rfl _
    (Orcl.f t O).procedure _ _ _ (fun m => m lv)
    (fun v m => (varLens lv).set v m) (fun v m => (varLens lv).set_get m v)
    (fun v w m => (varLens lv).set_set m v w) (fun m => (varLens lv).get_set m)
    ?_ ?_ ?_ ?_ l _ ?_)).trans ?_
  · exact fun _ => rfl
  · exact fun _ => rfl
  · exact fun _ _ => rfl
  · exact fun _ => rfl
  · exact (varLens lv).set_get _ _
  · rw [SubProbability.hbind_assoc]
    simp only [SubProbability.pure_hbind]
    rw [SubProbability.hbind_eq_bind]
    exact SubProbability.bind_pure _


section Lemmas

variable (f : t → ProgramDenotation VariableAssignment Unit)

omit [Inhabited t] in
theorem iterDen_append : ∀ l₁ l₂ : List t,
    iterDen f (l₁ ++ l₂) = iterDen f l₁ >>= fun _ => iterDen f l₂
  | [], l₂ => by
      show iterDen f l₂ = (pure () : ProgramDenotation VariableAssignment Unit) >>= _
      rw [ProgramDenotation.pure_bind]
  | x :: l₁, l₂ => by
      show (f x >>= fun _ => iterDen f (l₁ ++ l₂)) = (f x >>= fun _ => iterDen f l₁) >>= _
      rw [iterDen_append l₁ l₂, ProgramDenotation.bind_assoc]

omit [Inhabited t] in
/-- Calls of `f` that commute can be iterated in any order. -/
theorem iterDen_perm (hcomm : ∀ x y, (f x >>= fun _ => f y) = (f y >>= fun _ => f x)) :
    ∀ {l₁ l₂ : List t}, l₁.Perm l₂ → iterDen f l₁ = iterDen f l₂
  | _, _, .nil => rfl
  | _, _, .cons x h => by
      show (f x >>= fun _ => iterDen f _) = (f x >>= fun _ => iterDen f _)
      rw [iterDen_perm hcomm h]
  | _, _, .swap x y l => by
      show (f y >>= fun _ => f x >>= fun _ => iterDen f l) =
        (f x >>= fun _ => f y >>= fun _ => iterDen f l)
      rw [← ProgramDenotation.bind_assoc, ← ProgramDenotation.bind_assoc, hcomm]
  | _, _, .trans h₁ h₂ => (iterDen_perm hcomm h₁).trans (iterDen_perm hcomm h₂)

end Lemmas

variable (O : Orcl t)

/-- EC's `iter_ll`. -/
theorem iter_ll (hf : (Orcl.f t O).procedure.IsLossless) :
    (Module.app (Iter.iter t) O).procedure.IsLossless := by
  intro l g
  simp only [Procedure.ewp, Iter.iter_denotation]
  induction l generalizing g with
  | nil =>
      show (pure ((), g) : SubProbability _).expected _ = 1
      rw [expected_pure]
  | cons x l ih =>
      show (procedureDenotation (Orcl.f t O).procedure x >>= fun _ => iterDen _ l).wp _ g = 1
      rw [wp_bind]
      refine Eq.trans ?_ (hf x g)
      unfold Procedure.ewp
      congr 1
      funext r
      exact ih r.2

/-- EC's `iter_inv`. -/
theorem iter_inv (P : t → Prop) (Inv : VariableAssignment → VariableAssignment → Prop)
    (hf : prhlProc (sig₁ := procsig (t) → Unit) (sig₂ := procsig (t) → Unit)
      (fun a₁ g₁ a₂ g₂ => a₁ = a₂ ∧ P a₁ ∧ Inv g₁ g₂)
      (Orcl.f t O).procedure (Orcl.f t O).procedure (fun _ g₁ _ g₂ => Inv g₁ g₂)) :
    prhlProc (sig₁ := procsig (List t) → Unit) (sig₂ := procsig (List t) → Unit)
      (fun l₁ g₁ l₂ g₂ => l₁ = l₂ ∧ (∀ x ∈ (show List t from l₁), P x) ∧ Inv g₁ g₂)
      (Module.app (Iter.iter t) O).procedure (Module.app (Iter.iter t) O).procedure
      (fun _ g₁ _ g₂ => Inv g₁ g₂) := by
  intro l₁ l₂
  rw [Iter.iter_denotation, Iter.iter_denotation]
  intro g₁ g₂ ⟨hl, hP, hI⟩
  subst hl
  suffices H : ∀ l : List t, (∀ x ∈ l, P x) →
      ProgramDenotation.prhl2 Inv
        (iterDen (fun x => procedureDenotation (Orcl.f t O).procedure x) l)
        (iterDen (fun x => procedureDenotation (Orcl.f t O).procedure x) l)
        (fun u v => Inv u.2 v.2) from H l₁ hP g₁ g₂ hI
  intro l
  induction l with
  | nil => exact fun _ => ProgramDenotation.prhl2.pure_pure fun _ _ h => h
  | cons x l ih =>
      intro hP
      exact ProgramDenotation.prhl2.bind
        ((hf x x).conseq (fun _ _ h => ⟨rfl, hP x (List.mem_cons_self ..), h⟩) (fun _ _ h => h))
        (fun _ _ => ih fun y hy => hP y (List.mem_cons_of_mem _ hy))

/-- EC's `iter_cat`, denotationally: iterating over `l₁ ++ l₂` is iterating over `l₁`, then
`l₂` (EC's `Iter(O).iters`). -/
theorem iter_cat (l₁ l₂ : List t) :
    procedureDenotation (Module.app (Iter.iter t) O).procedure (l₁ ++ l₂) =
      (procedureDenotation (Module.app (Iter.iter t) O).procedure l₁ >>= fun _ =>
        procedureDenotation (Module.app (Iter.iter t) O).procedure l₂) := by
  rw [Iter.iter_denotation, Iter.iter_denotation, Iter.iter_denotation]
  exact iterDen_append _ l₁ l₂

/-- EC's `iter_perm`, denotationally, under EC's `iter2_eq` (two calls of `O.f` commute): the
iteration does not depend on the order of the list. -/
theorem iter_perm
    (iter2_eq : ∀ t₁ t₂ : t, (procedureDenotation (Orcl.f t O).procedure t₁ >>= fun _ =>
        procedureDenotation (Orcl.f t O).procedure t₂) =
      (procedureDenotation (Orcl.f t O).procedure t₂ >>= fun _ =>
        procedureDenotation (Orcl.f t O).procedure t₁))
    {l₁ l₂ : List t} (h : l₁.Perm l₂) :
    procedureDenotation (Module.app (Iter.iter t) O).procedure l₁ =
      procedureDenotation (Module.app (Iter.iter t) O).procedure l₂ := by
  simp only [Iter.iter_denotation]
  exact iterDen_perm _ iter2_eq h

/-- EC's `iter1_perm`, denotationally (EC's `Iter(O).iter_1s(t, l)` is `O.f(t); iter(l)`). -/
theorem iter1_perm
    (iter2_eq : ∀ t₁ t₂ : t, (procedureDenotation (Orcl.f t O).procedure t₁ >>= fun _ =>
        procedureDenotation (Orcl.f t O).procedure t₂) =
      (procedureDenotation (Orcl.f t O).procedure t₂ >>= fun _ =>
        procedureDenotation (Orcl.f t O).procedure t₁))
    {x : t} {l l₂ : List t} (h : (x :: l).Perm l₂) :
    (procedureDenotation (Orcl.f t O).procedure x >>= fun _ =>
        procedureDenotation (Module.app (Iter.iter t) O).procedure l) =
      procedureDenotation (Module.app (Iter.iter t) O).procedure l₂ := by
  rw [← iter_perm O iter2_eq h]
  simp only [Iter.iter_denotation]
  rfl

end GaudisCrypt.EC.IterProc
