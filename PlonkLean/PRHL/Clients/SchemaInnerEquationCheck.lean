import PlonkLean.PRHL.Clients.SchemaInnerEquation
import PlonkLean.RO.OneWayness_GameHop.GuessExperiment

/-!
# Cross-check: the relational proof subsumes the unary original

`PRHLSchema.schema_inner_equation_prhl` instantiated at the concrete OW
`state` yields exactly the statement of `schema_inner_equation`
(`GuessExperiment.lean`), with the original's full hypothesis list. This
certifies that the relational client is a drop-in replacement for the
~950-line unary block (the lemma proper plus its private support lemmas).
The original is left untouched until migration is decided.
-/

example
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T]
    (target_var : Lens T state) (matched_var : Lens Bool state)
    (queries_list_var : Lens (List T) state)
    [disjoint matched_var queries_list_var]
    [disjoint matched_var target_var]
    [disjoint queries_list_var target_var]
    (q_body q_final : Program state T)
    (h_q_body_matched : q_body.inRange matched_var.compl.range)
    (h_q_body_qs : q_body.inRange queries_list_var.compl.range)
    (h_q_body_target : q_body.inRange target_var.compl.range)
    (h_q_final_matched : q_final.inRange matched_var.compl.range)
    (h_q_final_qs : q_final.inRange queries_list_var.compl.range)
    (h_q_final_target : q_final.inRange target_var.compl.range)
    (n : ℕ) (σ' : state) (t : T) :
    (Program.set target_var t >>= fun _ : Unit =>
     Program.set matched_var false >>= fun _ : Unit =>
     loop_n n (q_body >>= fun a : T =>
        if a = t then Program.set matched_var true else (pure () : Program state Unit))
      >>= fun _ : Unit =>
     (q_final >>= fun a : T =>
        if a = t then Program.set matched_var true else (pure () : Program state Unit))
      >>= fun _ : Unit =>
     Program.get matched_var).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ'
    = (Program.set queries_list_var [] >>= fun _ : Unit =>
       loop_n n (q_body >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
       (q_final >>= fun a : T =>
          Program.get queries_list_var >>= fun qs : List T =>
          Program.set queries_list_var (qs ++ [a])) >>= fun _ : Unit =>
       Program.get queries_list_var >>= fun qs =>
       Program.set matched_var (decide (t ∈ qs)) >>= fun _ : Unit =>
       Program.get matched_var).wp
       (fun bσ : Bool × state => if bσ.1 then (1 : ENNReal) else 0) σ' :=
  -- the original, for reference (same statement):
  -- schema_inner_equation target_var matched_var queries_list_var q_body q_final
  --   h_q_body_matched h_q_body_qs h_q_body_target
  --   h_q_final_matched h_q_final_qs h_q_final_target n σ' t
  PRHLSchema.schema_inner_equation_prhl target_var matched_var queries_list_var
    q_body q_final h_q_body_matched h_q_body_qs h_q_body_target
    h_q_final_matched h_q_final_qs h_q_final_target n σ' t
