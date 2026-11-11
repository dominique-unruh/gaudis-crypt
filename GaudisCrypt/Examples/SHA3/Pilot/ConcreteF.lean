import GaudisCrypt.Examples.SHA3.Pilot.SLCommon
import GaudisCrypt.Examples.SHA3.SmartCounter.ConcreteF
import GaudisCrypt.Lib.EC.Strong_RP_RF
import GaudisCrypt.Logic.ECLoop
import GaudisCrypt.Logic.ECTrans
import GaudisCrypt.Logic.ECAlias
import GaudisCrypt.Logic.ECWhile

/-!
# From the permutation to a random function (EasyCrypt `proof/smart_counter/ConcreteF.eca`) —
EC-fidelity port

The real game with the ideal permutation is close to the same game with `PF`, a random function
with an inverse, up to the PRP/PRF switching bound (`Real_Concrete`).

Translation (as `Pilot/SLCommon.lean`):
* `local clone import Strong_RP_RF as Switching with type D <- state, op uD <- dstate, …` is the
  namespace `Switching`: the clone's module variables (`PRPi.m`, `ARP.coll`, `DBounder.FBounder.c`,
  …) `global_var`s, its modules the library's (`Lib/EC/Strong_RP_RF.lean`) at them, its realized
  axioms lemmas.  (EC's `local` has no counterpart: the clone's names stay visible.)
* `declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo}` and `declare axiom D_ll` as in
  EC; the local modules `GReal'`, `D'` are definitions (`D'` with `D` a Lean parameter, as
  `DRestr`).
-/

namespace GaudisCrypt.SHA3.Pilot.ConcreteF

open GaudisCrypt GaudisCrypt.EC GaudisCrypt.EC.FSet
open GaudisCrypt.SHA3.Common hiding PRIMITIVE
open GaudisCrypt.SHA3.SLCommon GaudisCrypt.SHA3.SLCommon.Prefix
open GaudisCrypt.SHA3.Pilot.SLCommon

variable [SLCommon.Params]

/-- EC's `state` (`SLCommonCore`'s, named here: a root `state` exists). -/
abbrev state := GaudisCrypt.SHA3.SLCommon.state

-- EC's `PF.m`, `PF.mi`, `PF`: the first port's (`SmartCounter/ConcreteF.lean`), one declaration
-- per EC variable, shared with the pilots of `Handle`, `Gcol`, `Gext`, `Gconcl`
open GaudisCrypt.SHA3.ConcreteF (PF PF.m PF.mi)

/-- `module CF(D : DISTINGUISHER) = Indif(SqueezelessSponge(PF), PF, D)`. -/
noncomputable abbrev CF (D : DISTINGUISHER) : procmod () → Bool :=
  Module.app Indif (Module.pair (Module.app SqueezelessSponge (PF : DPRIMITIVE))
    (Module.pair PF D))

/-! `local clone import Strong_RP_RF as Switching with type D <- state, op uD <- dstate,
type K <- unit, op dK <- (MUnit.dunit<:unit> tt), op q <- max_size`. -/

namespace Switching

global_var PRPi.m : FMap state state
global_var PRPi.mi : FMap state state
global_var ARP.coll : Bool
global_var ARP.m : FMap state state
global_var ARP.mi : FMap state state
global_var DBounder.FBounder.c : ℤ

set_option linter.dupNamespace false in
-- EasyCrypt names the module after its theory (exception E1)
/-- The clone's `PRPi.PRPi` (the theory's `clone import RP as PRPi`). -/
noncomputable abbrev PRPi.PRPi := Strong_RP_RF.PRPi.PRPi state dstate PRPi.m PRPi.mi
/-- The clone's `ARP`. -/
noncomputable abbrev ARP := Strong_RP_RF.ARP state dstate ARP.coll ARP.m ARP.mi
/-- The clone's `DBounder`. -/
noncomputable abbrev DBounder := Strong_RP_RF.DBounder state max_size DBounder.FBounder.c
abbrev PRPSec.PRP := EC.PRP.StrongPRP.PRP state
abbrev PRPSec.SPRP_Oracles := EC.PRP.StrongPRP.SPRP_Oracles state
abbrev PRPSec.Distinguisher := EC.PRP.StrongPRP.Distinguisher state
noncomputable abbrev PRPSec.IND := EC.PRP.StrongPRP.IND state

/-- `realize ge0_q by smt w=max_ge0`. -/
theorem ge0_q : 0 ≤ (max_size : ℤ) := max_ge0

/-- `realize uD_uf_fu`: `dstate` is uniform, lossless and full. -/
theorem uD_uf_fu : dstate.1 Set.univ = 1 ∧ ∀ x y, dstate.1 {x} = dstate.1 {y} := by
  refine ⟨dprod_ll BitWord.dunifin_ll BitWord.dunifin_ll, ?_⟩
  rintro ⟨x1, x2⟩ ⟨y1, y2⟩
  rw [dstate, dprod1E, dprod1E, bdistr, cdistr, Block.DBlock.dunifin, Capacity.DCapacity.dunifin,
    BitWord.dunifin_funi x1 y1, BitWord.dunifin_funi x2 y2]

end Switching

open Switching

omit [SLCommon.Params] in
/-- EC's `lemma size_behead (l : 'a list) : l <> [] => size (behead l) = size l - 1`. -/
theorem size_behead {α : Type} (l : List α) : l ≠ [] → size (behead l) = size l - 1 := by
  cases l with
  | nil => intro h; exact absurd rfl h
  | cons a l => intro _; simp [size, behead]

/-! EC's `smt(domE mem_set get_setE take_size cat_take_drop)` in `DoubleBounding`'s `conseq`,
the facts `smt_close` does not find: the query `bs₀` added, with its block `sa`. -/

theorem db_query_block (Q : FMap (List block) block) (P R : FMap (List block) state)
    (bs₀ : List block) (sa : block) (sc : capacity) (x : List block)
    (hx : (Q.set bs₀ sa).dom x) (hinv : prefix_inv Q P) (hPR : ∀ y, P.dom y → P.get y = R.get y)
    (hQP : ∀ y, Q.dom y → P.dom y) (hR : R.get (take (size bs₀) bs₀) = some (sa, sc)) :
    oget ((Q.set bs₀ sa).get x) = (oget (R.get x)).1 := by
  rw [FMap.get_setE]
  split_ifs with h
  · subst h; rw [take_size] at hR; rw [hR]; rfl
  · have hd : Q.dom x := by
      rcases (FMap.mem_set _ _ _ _).1 hx with h' | h'
      · exact h'
      · exact absurd h' h
    rw [hinv.1 x hd, hPR x (hQP x hd)]

theorem db_query_prefixes (Q : FMap (List block) block) (P R : FMap (List block) state)
    (bs₀ : List block) (sa : block) (x : List block) (i : ℤ)
    (hx : (Q.set bs₀ sa).dom x) (hinv : prefix_inv Q P)
    (hR : ∀ y, R.dom y ↔ P.dom y ∨ ∃ j, 0 ≤ j ∧ j ≤ size bs₀ ∧ y = take j bs₀) :
    R.dom (take i x) := by
  rcases (FMap.mem_set _ _ _ _).1 hx with h | h
  · exact (hR _).2 (Or.inl (hinv.2.1 x h i))
  · subst h
    have : 0 ≤ size x := by simp [size]
    refine (hR _).2 (Or.inr ⟨min (max i 0) (size x), by omega, min_le_right _ _, take_clamp i x⟩)

theorem db_query_extend (Q : FMap (List block) block) (P R : FMap (List block) state)
    (bs₀ : List block) (sa : block) (x : List block) (i : ℤ) (hne : take i x ≠ [])
    (hdom : R.dom (take i x)) (hinv : prefix_inv Q P)
    (hR : ∀ y, R.dom y ↔ P.dom y ∨ ∃ j, 0 ≤ j ∧ j ≤ size bs₀ ∧ y = take j bs₀) :
    ∃ l2, (Q.set bs₀ sa).dom (take i x ++ l2) := by
  rcases (hR _).1 hdom with hP | ⟨j, -, -, hj⟩
  · obtain ⟨l2, hl⟩ := hinv.2.2 x i hne hP
    exact ⟨l2, (FMap.mem_set _ _ _ _).2 (Or.inl hl)⟩
  · exact ⟨drop j bs₀, by rw [hj, cat_take_drop]; exact (FMap.mem_set _ _ _ _).2 (Or.inr rfl)⟩

/-! EC's `smt` facts in `DoubleBounding`'s second loop that `smt_close` does not find: the round
adds the prefix `take (i+1) p` to `Redo.prefixes`. -/

theorem db_loop_prefix_closed (R pref : FMap (List block) state) (p x : List block) (i i' : ℤ)
    (v : state) (hx : (R.set (take (i + 1) p) v).dom x) (hall : all_prefixes R) (hi : 0 ≤ i)
    (hR : ∀ y, R.dom y ↔ pref.dom y ∨ ∃ j, 0 ≤ j ∧ j ≤ i ∧ y = take j p) :
    (R.set (take (i + 1) p) v).dom (take i' x) := by
  rcases (FMap.mem_set _ _ _ _).1 hx with h | h
  · exact (FMap.mem_set _ _ _ _).2 (Or.inl (hall x h i'))
  · subst h
    rw [take_take]
    by_cases hm : min i' (i + 1) ≤ i
    · have : 0 ≤ size p := by simp [size]
      refine (FMap.mem_set _ _ _ _).2 (Or.inl ((hR _).2 (Or.inr
        ⟨min (max (min i' (i + 1)) 0) (size p), by omega, by omega, take_clamp _ p⟩)))
    · rw [show min i' (i + 1) = i + 1 by omega]
      exact (FMap.mem_set _ _ _ _).2 (Or.inr rfl)

theorem db_loop_next (R : FMap (List block) state) (p : List block) (i : ℤ) (v : state)
    (h : (R.set (take (i + 1) p) v).dom (take (i + 1 + 1) p)) (hall : all_prefixes R)
    (hi : 0 ≤ i) (hlt : i + 1 < size p) (hn : ¬ R.dom (take (i + 1) p)) : False := by
  rcases (FMap.mem_set _ _ _ _).1 h with h | h
  · have := hall _ h (i + 1)
    rw [take_take, min_eq_left (by omega)] at this
    exact hn this
  · have h2 := congrArg List.length h
    simp only [take, List.length_take] at h2
    simp only [size] at hlt
    omega

theorem db_loop_dom (R pref : FMap (List block) state) (p y : List block) (i : ℤ) (v : state)
    (hR : ∀ y, R.dom y ↔ pref.dom y ∨ ∃ j, 0 ≤ j ∧ j ≤ i ∧ y = take j p) (hi : 0 ≤ i) :
    (R.set (take (i + 1) p) v).dom y ↔ pref.dom y ∨ ∃ j, 0 ≤ j ∧ j ≤ i + 1 ∧ y = take j p := by
  rw [FMap.mem_set, hR]
  constructor
  · rintro ((h | ⟨j, h0, h1, rfl⟩) | rfl)
    · exact Or.inl h
    · exact Or.inr ⟨j, h0, by omega, rfl⟩
    · exact Or.inr ⟨i + 1, by omega, le_rfl, rfl⟩
  · rintro (h | ⟨j, h0, h1, rfl⟩)
    · exact Or.inl (Or.inl h)
    · by_cases hj : j ≤ i
      · exact Or.inl (Or.inr ⟨j, h0, hj, rfl⟩)
      · rw [show j = i + 1 by omega]
        exact Or.inr rfl

/-! EC's facts in `DoubleBounding`'s first loop: the prefixes of `bs` up to its longest queried
prefix are known (`prefix_exchange` moves the longest prefix from the queries to the prefixes). -/

theorem db_first_post_false (Q : FMap (List block) block) (R : FMap (List block) state)
    (bs : List block) (hinv : prefix_inv Q R) (hall : all_prefixes R)
    (hlt : «prefix» bs (get_max_prefix bs (elems (FMap.fdom Q))) < size bs)
    (hd : R.dom (take («prefix» bs (get_max_prefix bs (elems (FMap.fdom Q))) + 1) bs)) : False := by
  rw [prefix_exchange Q R bs hinv hall] at hlt hd
  exact prefix_lt_size bs _ hlt _ (lt_add_one _) ((mem_elems_fdom _ _).2 hd)

theorem db_first_dom (R : FMap (List block) state) (bs : List block) (i : ℤ) (s : state)
    (hall : all_prefixes R) (hi : R.get (take i bs) = some s) (y : List block) :
    R.dom y ↔ R.dom y ∨ ∃ j, 0 ≤ j ∧ j ≤ i ∧ y = take j bs := by
  refine ⟨Or.inl, ?_⟩
  rintro (h | ⟨j, -, hj, rfl⟩)
  · exact h
  · have := hall _ ((FMap.domE _ _).2 (by rw [hi]; simp)) j
    rwa [take_take, min_eq_left hj] at this

theorem db_first_step (Q : FMap (List block) block) (R : FMap (List block) state)
    (bs : List block) (i : ℤ) (hinv : prefix_inv Q R) (hall : all_prefixes R) (h0 : 0 ≤ i)
    (hg : (decide (i < size bs) && decide (R.dom (take (i + 1) bs))) = true) :
    i + 1 ≤ «prefix» bs (get_max_prefix bs (elems (FMap.fdom Q))) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  rw [prefix_exchange Q R bs hinv hall]
  exact all_take_in bs (i + 1) R ⟨by omega, by omega⟩ hall hg.2

theorem db_first_get (R : FMap (List block) state) (bs : List block) (i : ℤ)
    (hg : (decide (i < size bs) && decide (R.dom (take (i + 1) bs))) = true) :
    R.get (take (i + 1) bs) =
      some ((oget (R.get (take (i + 1) bs))).1, (oget (R.get (take (i + 1) bs))).2) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.1 ((FMap.domE _ _).1 hg.2)
  simp [hv, EC.oget_some]

theorem db_first_exit (Q : FMap (List block) block) (R : FMap (List block) state)
    (bs : List block) (i : ℤ) (h0 : 0 ≤ i)
    (hi : i ≤ «prefix» bs (get_max_prefix bs (elems (FMap.fdom Q))))
    (hj : ∀ j, 0 ≤ j → j ≤ «prefix» bs (get_max_prefix bs (elems (FMap.fdom Q))) →
      R.dom (take j bs))
    (hg : (decide (i < size bs) && decide (R.dom (take (i + 1) bs))) = false) :
    i = «prefix» bs (get_max_prefix bs (elems (FMap.fdom Q))) := by
  have hs := prefix_sizel bs (get_max_prefix bs (elems (FMap.fdom Q)))
  by_contra hne
  have hd := hj (i + 1) (by omega) (by omega)
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hg
  rcases hg with h | h
  · omega
  · exact h hd

theorem db_first_init (Q : FMap (List block) block) (R : FMap (List block) state)
    (bs : List block) (hinv : prefix_inv Q R) (hall : all_prefixes R)
    (h0 : R.get [] = some (b0, c0)) (j : ℤ) (_hj0 : 0 ≤ j)
    (hj : j ≤ «prefix» bs (get_max_prefix bs (elems (FMap.fdom Q)))) : R.dom (take j bs) := by
  rw [prefix_exchange Q R bs hinv hall] at hj
  exact take_get_max_prefix2 bs R j ⟨[], (FMap.domE _ _).2 (by rw [h0]; simp)⟩ hall hj

/-- EC's `smt(mem_set mem_empty)` on the initial maps: the keys of `{[] ↦ w}` are `[]`, so are
their prefixes. -/
theorem db_init_dom {β γ : Type} (v : β) (w : γ) (bs : List block) (i : ℤ)
    (h : (FMap.empty.set [] w).dom bs) : (FMap.empty.set [] v).dom (take i bs) := by
  rcases (FMap.mem_set _ _ _ _).1 h with h | rfl
  · exact absurd h (FMap.mem_empty _)
  · exact (FMap.mem_set _ _ _ _).2 (Or.inr (by simp [take]))

/-! EC's facts in `Real_Concrete`'s first step (the new query `bs`, `Redo.prefixes` from `P` to
`R`: `P`'s entries kept, the prefixes of `bs` added, nothing else), the `conseq` goals
`smt_close` does not find (EC's `progress` bullets: two by hand, three `smt`). -/

theorem rc_dom_of_P (P R : FMap (List block) state)
    (hPR : ∀ l, P.dom l → P.get l = R.get l) (l : List block) (h : P.dom l) : R.dom l := by
  rw [FMap.domE] at h ⊢; rwa [← hPR l ((FMap.domE _ _).2 h)]

theorem rc_take_in (R : FMap (List block) state) (bs : List block)
    (hRin : ∀ j, 0 ≤ j → j ≤ size bs → R.dom (take j bs)) (i : ℤ) : R.dom (take i bs) := by
  have : 0 ≤ size bs := by simp [size]
  rw [take_clamp]; exact hRin _ (by omega) (min_le_right _ _)

theorem rc_query_block (Q : FMap (List block) block) (P R : FMap (List block) state)
    (bs : List block) (sa : block) (sc : capacity) (x : List block)
    (hx : (Q.set bs sa).dom x) (hinv : prefix_inv Q P)
    (hPR : ∀ l, P.dom l → P.get l = R.get l)
    (hR : R.get (take (size bs) bs) = some (sa, sc)) :
    oget ((Q.set bs sa).get x) = (oget (R.get x)).1 :=
  db_query_block Q P R bs sa sc x hx hinv hPR
    (fun y hy => by simpa [take_size] using hinv.2.1 y hy (size y)) hR

theorem rc_query_prefixes (Q : FMap (List block) block) (P R : FMap (List block) state)
    (bs : List block) (sa : block) (x : List block) (i : ℤ)
    (hx : (Q.set bs sa).dom x) (hinv : prefix_inv Q P)
    (hPR : ∀ l, P.dom l → P.get l = R.get l)
    (hRin : ∀ j, 0 ≤ j → j ≤ size bs → R.dom (take j bs)) : R.dom (take i x) := by
  rcases (FMap.mem_set _ _ _ _).1 hx with h | h
  · exact rc_dom_of_P P R hPR _ (hinv.2.1 x h i)
  · subst h; exact rc_take_in R x hRin i

theorem rc_query_extend (Q : FMap (List block) block) (P R : FMap (List block) state)
    (bs : List block) (sa : block) (x : List block) (i : ℤ) (hne : take i x ≠ [])
    (hdom : R.dom (take i x)) (hinv : prefix_inv Q P)
    (hRout : ∀ l, R.dom l → P.dom l ∨ ∃ j, 0 ≤ j ∧ j ≤ size bs ∧ l = take j bs) :
    ∃ l2, (Q.set bs sa).dom (take i x ++ l2) := by
  rcases hRout _ hdom with hP | ⟨j, -, -, hj⟩
  · obtain ⟨l2, hl⟩ := hinv.2.2 x i hne hP
    exact ⟨l2, (FMap.mem_set _ _ _ _).2 (Or.inl hl)⟩
  · exact ⟨drop j bs, by rw [hj, cat_take_drop]; exact (FMap.mem_set _ _ _ _).2 (Or.inr rfl)⟩

theorem rc_nil (P R : FMap (List block) state) (hP0 : P.get [] = some (b0, c0))
    (hPR : ∀ l, P.dom l → P.get l = R.get l) : R.get [] = some (b0, c0) := by
  rw [← hPR [] ((FMap.domE _ _).2 (by rw [hP0]; simp))]; exact hP0

theorem rc_all_prefixes (P R : FMap (List block) state) (bs : List block) (l : List block)
    (i : ℤ) (hl : R.dom l) (hall : all_prefixes P)
    (hPR : ∀ l, P.dom l → P.get l = R.get l)
    (hRin : ∀ j, 0 ≤ j → j ≤ size bs → R.dom (take j bs))
    (hRout : ∀ l, R.dom l → P.dom l ∨ ∃ j, 0 ≤ j ∧ j ≤ size bs ∧ l = take j bs) :
    R.dom (take i l) := by
  rcases hRout l hl with hP | ⟨j, -, -, rfl⟩
  · exact rc_dom_of_P P R hPR _ (hall l hP i)
  · rw [take_take]; exact rc_take_in R bs hRin _

/-! EC's facts in `Real_Concrete`'s first step, second loop: a round past the longest queried
prefix adds `take (i+1) p`, which was nowhere yet (EC's `prefix_exchange`). -/

theorem rc_pref_notin (Q : FMap (List block) block) (P : FMap (List block) state)
    (p : List block) (i : ℤ) (hinv : prefix_inv Q P) (hallP : all_prefixes P)
    (hpre : «prefix» p (get_max_prefix p (elems (FMap.fdom Q))) ≤ i) (hi : i < size p) :
    ¬ P.dom (take (i + 1) p) := by
  intro hP
  rw [prefix_exchange Q P p hinv hallP] at hpre
  exact prefix_lt_size p _ (by omega) (i + 1) (by omega) ((mem_elems_fdom _ _).2 hP)

theorem rc_loop_notin (Q : FMap (List block) block) (P R : FMap (List block) state)
    (p : List block) (i : ℤ) (hinv : prefix_inv Q P) (hallP : all_prefixes P)
    (hpre : «prefix» p (get_max_prefix p (elems (FMap.fdom Q))) ≤ i) (hi : i < size p)
    (hRout : ∀ l, R.dom l → P.dom l ∨ ∃ j, 0 ≤ j ∧ j ≤ i ∧ l = take j p) :
    ¬ R.dom (take (i + 1) p) := by
  intro hd
  rcases hRout _ hd with hP | ⟨j, hj0, hji, hj⟩
  · exact rc_pref_notin Q P p i hinv hallP hpre hi hP
  · have h2 := congrArg List.length hj
    simp only [take, List.length_take] at h2
    simp only [size] at hi
    omega

theorem rc_loop_closed (Q : FMap (List block) block) (R : FMap (List block) state)
    (p x : List block) (i i' : ℤ) (v : state) (hx : (R.set (take (i + 1) p) v).dom x)
    (hall : all_prefixes R) (hpre : «prefix» p (get_max_prefix p (elems (FMap.fdom Q))) ≤ i)
    (hRin : ∀ j, 0 ≤ j → j ≤ i → R.dom (take j p)) :
    (R.set (take (i + 1) p) v).dom (take i' x) := by
  have h0 := prefix_ge0 p (get_max_prefix p (elems (FMap.fdom Q)))
  rcases (FMap.mem_set _ _ _ _).1 hx with h | h
  · exact (FMap.mem_set _ _ _ _).2 (Or.inl (hall x h i'))
  · subst h
    rw [take_take]
    by_cases hm : min i' (i + 1) ≤ i
    · have : 0 ≤ size p := by simp [size]
      refine (FMap.mem_set _ _ _ _).2 (Or.inl ?_)
      rw [take_clamp]
      exact hRin _ (by omega) (by omega)
    · rw [show min i' (i + 1) = i + 1 by omega]
      exact (FMap.mem_set _ _ _ _).2 (Or.inr rfl)

theorem rc_loop_pref (Q : FMap (List block) block) (P R : FMap (List block) state)
    (p l : List block) (i : ℤ) (v : state) (hinv : prefix_inv Q P) (hallP : all_prefixes P)
    (hpre : «prefix» p (get_max_prefix p (elems (FMap.fdom Q))) ≤ i) (hi : i < size p)
    (hl : P.dom l) (hPR : ∀ l, P.dom l → P.get l = R.get l) :
    P.get l = (R.set (take (i + 1) p) v).get l := by
  rw [FMap.get_setE, if_neg]
  · exact hPR l hl
  · rintro rfl; exact rc_pref_notin Q P p i hinv hallP hpre hi hl

theorem rc_loop_in (R : FMap (List block) state)
    (p : List block) (i j : ℤ) (v : state)
    (hRin : ∀ j, 0 ≤ j → j ≤ i → R.dom (take j p)) (hj0 : 0 ≤ j) (hj : j ≤ i + 1) :
    (R.set (take (i + 1) p) v).dom (take j p) := by
  by_cases h : j ≤ i
  · exact (FMap.mem_set _ _ _ _).2 (Or.inl (hRin j hj0 h))
  · rw [show j = i + 1 by omega]; exact (FMap.mem_set _ _ _ _).2 (Or.inr rfl)

theorem rc_loop_out (Q : FMap (List block) block) (P R : FMap (List block) state)
    (p l : List block) (i : ℤ) (v : state)
    (hpre : «prefix» p (get_max_prefix p (elems (FMap.fdom Q))) ≤ i)
    (hRout : ∀ l, R.dom l → P.dom l ∨ ∃ j, 0 ≤ j ∧ j ≤ i ∧ l = take j p)
    (hl : (R.set (take (i + 1) p) v).dom l) :
    P.dom l ∨ ∃ j, 0 ≤ j ∧ j ≤ i + 1 ∧ l = take j p := by
  have h0 := prefix_ge0 p (get_max_prefix p (elems (FMap.fdom Q)))
  rcases (FMap.mem_set _ _ _ _).1 hl with h | rfl
  · rcases hRout l h with h | ⟨j, h0, h1, rfl⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, h0, by omega, rfl⟩
  · exact Or.inr ⟨i + 1, by omega, le_rfl, rfl⟩

/-! EC's facts in `Real_Concrete`'s first step, first loop: it stops exactly at the longest
queried prefix (EC's `take_get_max_prefix`, `prefix_exchange`). -/

theorem rc_first_exit {Q : FMap (List block) block} {R : FMap (List block) state}
    {bs : List block} {i : ℤ} {s : state} (hinv : prefix_inv Q R) (hall : all_prefixes R)
    (hi : i ≤ «prefix» bs (get_max_prefix bs (elems (FMap.fdom Q))))
    (hR : R.get (take i bs) = some s)
    (hg : (decide (i < size bs) && decide (R.dom (take (i + 1) bs))) = false) :
    «prefix» bs (get_max_prefix bs (elems (FMap.fdom Q))) = i := by
  rw [prefix_exchange Q R bs hinv hall] at hi ⊢
  by_contra hne
  have hs := prefix_sizel bs (get_max_prefix bs (elems (FMap.fdom R)))
  have hd := take_get_max_prefix2 bs R (i + 1)
    ⟨_, (FMap.domE _ _).2 (by rw [hR]; simp)⟩ hall (by omega)
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not] at hg
  rcases hg with h | h
  · omega
  · exact h hd

theorem rc_first_in (Q : FMap (List block) block) (R : FMap (List block) state)
    (bs : List block) (i j : ℤ) (s : state) (hinv : prefix_inv Q R) (hall : all_prefixes R)
    (hi : «prefix» bs (get_max_prefix bs (elems (FMap.fdom Q))) = i)
    (hR : R.get (take i bs) = some s) (hj : j ≤ i) : R.dom (take j bs) := by
  subst hi
  rw [prefix_exchange Q R bs hinv hall] at hj
  exact take_get_max_prefix2 bs R j ⟨_, (FMap.domE _ _).2 (by rw [hR]; simp)⟩ hall hj

/-- A `PRPSec.SPRP_Oracles` is a `DPRIMITIVE` (its `f`, `fi`). -/
module_subtype (EC.PRP.StrongPRP.SPRP_Oracles state) <: DPRIMITIVE

section

declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo}

-- EC's `declare axiom D_ll`
variable (D_ll : ∀ (F <: DFUNCTIONALITY {-D}), ∀ (P <: DPRIMITIVE {-D}),
  islossless P.f → islossless P.fi → islossless F.f → islossless D(F, P).distinguish)

/-- `local module GReal' = Indif(FC(SqueezelessSponge(Perm)), PC(Perm), D)`. -/
noncomputable abbrev GReal' : procmod () → Bool :=
  Module.app Indif (Module.pair (Module.app FC (Module.app SqueezelessSponge
    ((Perm : PRIMITIVE) : DPRIMITIVE))) (Module.pair (Module.app PC (Perm : PRIMITIVE)) D))

end

-- EC's `local module (D' : PRPSec.Distinguisher) (P' : PRPSec.SPRP_Oracles)`, `D` a Lean
-- parameter (as `DRestr`)
set_option linter.gaudisCrypt.using false in
module D' (D : DISTINGUISHER) using (P' : Switching.PRPSec.SPRP_Oracles) {
  proc distinguish () : Bool {
    var b : Bool;
    _ <- call Redo.init ();
    b <- call DRestr(D, SqueezelessSponge(P'), P').distinguish ();
    return $b
  };
}

section

-- EC's `{-Perm, -C, -PF, -Redo}`, and the local clone's modules (declared after `D` in EC's
-- section, so fresh for it: EC's freshness, as the pilots' `SecureRO`)
declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo, -DBounder, -ARP, -PRPi.PRPi}

set_option maxHeartbeats 4000000 in
-- one declaration: EC's call over three oracles, with the loops of `SqueezelessSponge`
/-- EC's `local lemma DoubleBounding (P <: PRPSec.PRP {-D, -C, -DBounder, -Redo}) &m:
Pr[PRPSec.IND(P,D').main() @ &m: res] = Pr[PRPSec.IND(P,DBounder(D')).main() @ &m: res]`. -/
theorem DoubleBounding : ∀ (P <: Switching.PRPSec.PRP {-D, -C, -DBounder, -Redo}),
    ∀ m : VariableAssignment,
    Pr[ Switching.PRPSec.IND(P, D'(D)).main () @ &m : §res ] =
      Pr[ Switching.PRPSec.IND(P, DBounder(D'(D))).main () @ &m : §res ] := by
  intro P _ m
  byequiv; equiv_proc; stmt_inline*; stmt_wp
  equiv_call (_ : ={glob C, glob P, glob Redo} ∧ all_prefixes §Redo.prefixes{2} ∧
      FMap.get §Redo.prefixes{2} [] = some (b0, c0) ∧
      (∀ x, FMap.dom §C.queries{2} x → FMap.dom §Redo.prefixes{2} x) ∧
      prefix_inv §C.queries{2} §Redo.prefixes{2} ∧ §DBounder.FBounder.c{2} = §C.c{2})
  -- `P.f`
  · equiv_proc; stmt_sp; equiv_if
    · stmt_inline*
      stmt_rcondt{2} 3
      · hoare_auto
      sim; auto_close
    · equiv_skip; auto_close
    · auto_close
  -- `P.fi`
  · equiv_proc; stmt_sp; equiv_if
    · stmt_inline*
      stmt_rcondt{2} 3
      · hoare_auto
      sim; auto_close
    · equiv_skip; auto_close
    · auto_close
  -- `F.f`
  · equiv_proc; stmt_sp; equiv_if
    · stmt_inline*
      equiv_if
      · stmt_wp
        stmt_splitwhile{1} 5 : FMap.dom §Redo.prefixes (take (§i + 1) §p)
        stmt_splitwhile{2} 5 : FMap.dom §Redo.prefixes (take (§i + 1) §p)
        stmt_alias{1} 1 pref = §Redo.prefixes
        stmt_alias{2} 1 pref = §Redo.prefixes
        stmt_sp 1
        stmt_alias{1} 1 query = §C.queries
        stmt_alias{2} 1 query = §C.queries
        stmt_sp 1
        equiv_conseq (: _ ==> ={sa, Redo.prefixes, glob D, glob P, i, C.c} ∧ all_prefixes §Redo.prefixes{2} ∧
            (∀ x, FMap.dom §query{2} x → FMap.dom §Redo.prefixes{2} x) ∧ §i{1} = size §bs{1} ∧
            FMap.get §Redo.prefixes{1} (take §i{1} §bs{1}) = some (§sa{1}, §sc{1}) ∧
            (∀ y, FMap.dom §pref{1} y → FMap.get §pref{1} y = FMap.get §Redo.prefixes{1} y) ∧
            (∀ y, FMap.dom §Redo.prefixes{1} y ↔
              (FMap.dom §pref{1} y ∨ ∃ j, 0 ≤ j ∧ j ≤ §i{1} ∧ y = take j §bs{1})) ∧
            §DBounder.FBounder.c{2} = §C.c{2} - size §bs{1} + §i{1})
        · auto_progress
          -- EC's six `smt(domE mem_set get_setE take_size cat_take_drop)`
          · smt_close [FMap.domE, FMap.mem_set, FMap.get_setE, take_size, cat_take_drop]
          · smt_close [FMap.domE, FMap.mem_set, FMap.get_setE, take_size, cat_take_drop]
          · generalize_reads_all; subst_vars; apply db_query_block <;> assumption
          · generalize_reads_all; subst_vars; apply db_query_prefixes <;> assumption
          · generalize_reads_all; subst_vars; apply db_query_extend <;> assumption
        · equiv_while_raw (={sa, Redo.prefixes, glob D, glob P, i, C.c, p, sc} ∧ §p{1} = §bs{1} ∧
              all_prefixes §Redo.prefixes{2} ∧ FMap.get §Redo.prefixes{2} [] = some (b0, c0) ∧
              (∀ x, FMap.dom §query{2} x → FMap.dom §Redo.prefixes{2} x) ∧
              (§i{1} < size §p{1} → ¬ FMap.dom §Redo.prefixes{1} (take (§i{1} + 1) §p{1})) ∧
              0 ≤ «prefix» §bs{1} (get_max_prefix §bs{1} (elems (FMap.fdom §C.queries{1}))) ∧
              «prefix» §bs{1} (get_max_prefix §bs{1} (elems (FMap.fdom §C.queries{1}))) ≤ §i{1} ∧
              §i{1} ≤ size §bs{1} ∧ §C.c{1} ≤ max_size ∧
              FMap.get §Redo.prefixes{1} (take §i{1} §bs{1}) = some (§sa{1}, §sc{1}) ∧
              (∀ y, FMap.dom §pref{1} y → FMap.get §pref{1} y = FMap.get §Redo.prefixes{1} y) ∧
              (∀ y, FMap.dom §Redo.prefixes{1} y ↔
                (FMap.dom §pref{1} y ∨ ∃ j, 0 ≤ j ∧ j ≤ §i{1} ∧ y = take j §bs{1})) ∧
              §DBounder.FBounder.c{2} = §C.c{2} - size §bs{1} + §i{1})
          · equiv_if
            · stmt_wp; equiv_skip; smt_close [FMap.domE]
            · stmt_sp
              stmt_rcondt{2} 1
              · intros; apply hoare_skip_of_imp
                auto_prep; generalize_reads_all; subst_vars; omega
              sim
              auto_progress
              all_goals first
                | (smt_close [FMap.domE, FMap.mem_set, FMap.get_setE, take_take, take_size,
                    cat_take_drop, prefix_ge0, prefix_sizel])
                | (generalize_reads_all; try subst_vars
                   first
                    | (apply db_loop_prefix_closed <;> first | assumption | omega)
                    | (apply db_loop_next (h := by assumption) <;> first | assumption | omega)
                    | (apply db_loop_dom <;> first | assumption | omega))
            · auto_close
          · auto_close
          · auto_close
          · stmt_sp
            equiv_conseq (: _ ==> ={sa, Redo.prefixes, glob D, glob P, i, C.c, p, sc, bs} ∧
                §p{1} = §bs{1} ∧ §Redo.prefixes{2} = §pref{2} ∧
                (∀ x, FMap.dom §query{2} x → FMap.dom §Redo.prefixes{2} x) ∧ §C.c{1} ≤ max_size ∧
                §i{1} = «prefix» §bs{1} (get_max_prefix §bs{1} (elems (FMap.fdom §C.queries{1}))) ∧
                FMap.get §Redo.prefixes{1} (take §i{1} §bs{1}) = some (§sa{1}, §sc{1}) ∧
                §DBounder.FBounder.c{2} = §C.c{2} - size §bs{1} +
                  «prefix» §bs{1} (get_max_prefix §bs{1} (elems (FMap.fdom §C.queries{1}))))
            · auto_progress
              · smt_close [all_prefixes]
              · generalize_reads_all; subst_vars; apply db_first_post_false <;> assumption
              · generalize_reads_all; exact prefix_ge0 _ _
              · generalize_reads_all; subst_vars; exact prefix_sizel _ _
              · generalize_reads_all; subst_vars; apply db_first_dom <;> assumption
            stmt_alias{2} 1 k = §DBounder.FBounder.c
            stmt_sp
            equiv_conseq (: _ ==> ={sa, Redo.prefixes, glob D, glob P, i, C.c, p, sc, bs} ∧
                §p{1} = §bs{1} ∧ §Redo.prefixes{2} = §pref{2} ∧
                (∀ x, FMap.dom §query{2} x → FMap.dom §Redo.prefixes{2} x) ∧ §C.c{2} ≤ max_size ∧
                §i{1} = «prefix» §bs{1} (get_max_prefix §bs{1} (elems (FMap.fdom §C.queries{1}))) ∧
                FMap.get §Redo.prefixes{1} (take §i{1} §bs{1}) = some (§sa{1}, §sc{1}) ∧
                §DBounder.FBounder.c{2} = §k{2})
            · smt_close
            equiv_while_raw (={sa, Redo.prefixes, glob D, glob P, i, C.c, p, sc, bs, C.queries} ∧
                §p{1} = §bs{1} ∧ §Redo.prefixes{2} = §pref{2} ∧
                (∀ x, FMap.dom §query{2} x → FMap.dom §Redo.prefixes{2} x) ∧
                prefix_inv §C.queries{2} §Redo.prefixes{2} ∧ all_prefixes §Redo.prefixes{2} ∧
                §C.c{2} ≤ max_size ∧ 0 ≤ §i{1} ∧
                §i{1} ≤ «prefix» §bs{1} (get_max_prefix §bs{1} (elems (FMap.fdom §C.queries{1}))) ∧
                (∀ j, 0 ≤ j → j ≤ «prefix» §bs{1} (get_max_prefix §bs{1} (elems (FMap.fdom §C.queries{1}))) →
                  FMap.dom §Redo.prefixes{1} (take j §bs{2})) ∧
                FMap.get §Redo.prefixes{1} (take §i{1} §bs{1}) = some (§sa{1}, §sc{1}) ∧
                §DBounder.FBounder.c{2} = §k{2})
            · stmt_rcondt{1} 1
              · hoare_auto
              stmt_rcondt{2} 1
              · hoare_auto
              equiv_auto
              auto_progress
              · apply db_first_step <;> assumption
              · apply db_first_get; assumption
            · auto_close
            · auto_progress
              apply db_first_exit <;> assumption
            · equiv_skip
              auto_progress
              all_goals first
                | (generalize_reads_all; subst_vars; exact prefix_ge0 _ _)
                | (generalize_reads_all; subst_vars; apply db_first_init <;> assumption)
                | (generalize_reads_all; subst_vars
                   simp only [take, Int.toNat_zero, List.take_zero]; assumption)
      · equiv_skip; auto_close
      · auto_close
    · stmt_wp; equiv_skip; auto_close
    · auto_close
  stmt_wp
  equiv_call (_ : ={glob D, glob P})
  equiv_skip
  auto_progress
  all_goals first
    | smt_close [FMap.mem_set, FMap.mem_empty, FMap.get_setE]
    | (apply db_init_dom; assumption)

end

section

declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo}

set_option maxHeartbeats 4000000 in
-- one declaration: EC's call over three oracles, with the loops of `SqueezelessSponge`
/-- The first step of EC's `Real_Concrete` (its `have ->:`): `Pr[RealIndif(SqueezelessSponge,
PC(Perm), D).main() @ &m: res /\ C.c <= max_size] = Pr[GReal'.main() @ &m: res /\ C.c <=
max_size]`; a theorem of its own (EC's proof, step for step). -/
theorem Real_GReal' (m : VariableAssignment) :
    Pr[ RealIndif(SqueezelessSponge, PC(Perm), D).main () @ &m : §res ∧ §C.c ≤ max_size ] =
      Pr[ (GReal' D) () @ &m : §res ∧ §C.c ≤ max_size ] := by
  byequiv; equiv_proc; stmt_inline*
  equiv_call (_ : ={C.c, glob Perm, Redo.prefixes} ∧ prefix_inv §C.queries{2} §Redo.prefixes{1} ∧
      FMap.get §Redo.prefixes{1} [] = some (b0, c0) ∧ all_prefixes §Redo.prefixes{1})
  -- `P.f`
  · equiv_proc; stmt_inline*; stmt_sp; equiv_if
    · sim; auto_close
    · sim; auto_close
    · auto_close
  -- `P.fi`
  · equiv_proc; stmt_inline*; stmt_sp; equiv_if
    · sim; auto_close
    · sim; auto_close
    · auto_close
  -- `F.f`
  · equiv_proc; stmt_inline*; stmt_sp; equiv_if{2}
    · stmt_sp; stmt_wp
      stmt_splitwhile{1} 1 : FMap.dom §Redo.prefixes (take (§i + 1) §p)
      stmt_splitwhile{2} 1 : FMap.dom §Redo.prefixes (take (§i + 1) §p0)
      stmt_alias{1} 1 pref = §Redo.prefixes
      stmt_alias{2} 1 pref = §Redo.prefixes
      stmt_sp 1 1
      stmt_alias{2} 1 query = §C.queries
      stmt_sp 0 1
      equiv_conseq (: _ ==> §sa{1} = §sa0{2} ∧ §p{1} = §p0{2} ∧
          ={Perm.m, Perm.mi, Redo.prefixes, i} ∧
          §C.c{1} = §C.c{2} - size §p0{2} + §i{2} ∧ §i{2} = size §p0{2} ∧
          FMap.get §Redo.prefixes{2} (take §i{2} §p0{2}) = some (§sa0{2}, §sc{2}) ∧
          (∀ l, FMap.dom §pref{2} l → FMap.get §pref{2} l = FMap.get §Redo.prefixes{2} l) ∧
          (∀ j, 0 ≤ j → j ≤ §i{2} → FMap.dom §Redo.prefixes{2} (take j §p0{2})) ∧
          (∀ l, FMap.dom §Redo.prefixes{2} l →
            FMap.dom §pref{2} l ∨ ∃ j, 0 ≤ j ∧ j ≤ §i{2} ∧ l = take j §p0{2}))
      · auto_progress
        all_goals first
          | smt_close
          | (generalize_reads_all; subst_vars
             first
              | (apply rc_query_block <;> assumption)
              | (apply rc_query_prefixes <;> assumption)
              | (apply rc_query_extend <;> assumption)
              | (apply rc_nil <;> assumption)
              | (apply rc_all_prefixes <;> assumption))
      equiv_while_raw (§sa{1} = §sa0{2} ∧ ={sc, Perm.m, Perm.mi, Redo.prefixes, i} ∧ §p{1} = §p0{2} ∧
          §C.c{1} = §C.c{2} - size §p0{2} + §i{2} ∧
          all_prefixes §Redo.prefixes{2} ∧ all_prefixes §pref{2} ∧
          prefix_inv §C.queries{2} §pref{2} ∧
          «prefix» §p0{2} (get_max_prefix §p0{2} (elems (FMap.fdom §C.queries{2}))) ≤ §i{2} ∧
          §i{2} ≤ size §p0{2} ∧
          FMap.get §Redo.prefixes{2} (take §i{2} §p0{2}) = some (§sa0{2}, §sc{2}) ∧
          (∀ l, FMap.dom §pref{2} l → FMap.get §pref{2} l = FMap.get §Redo.prefixes{2} l) ∧
          (∀ j, 0 ≤ j → j ≤ §i{2} → FMap.dom §Redo.prefixes{2} (take j §p0{2})) ∧
          (∀ l, FMap.dom §Redo.prefixes{2} l →
            FMap.dom §pref{2} l ∨ ∃ j, 0 ≤ j ∧ j ≤ §i{2} ∧ l = take j §p0{2}))
      · stmt_rcondf{1} 1
        · intros; apply hoare_skip_of_imp
          auto_prep; generalize_reads_all; subst_vars
          apply rc_loop_notin <;> assumption
        stmt_rcondf{2} 1
        · intros; apply hoare_skip_of_imp
          auto_prep; generalize_reads_all; subst_vars
          apply rc_loop_notin <;> assumption
        sim
        auto_progress
        all_goals first
          | smt_close
          | (generalize_reads_all; try subst_vars
             first
              | (apply rc_loop_closed <;> assumption)
              | (apply rc_loop_pref <;> assumption)
              | (apply rc_loop_in <;> assumption)
              | (apply rc_loop_out <;> assumption))
      · auto_close
      · auto_close
      · equiv_conseq (: _ ==> §sa{1} = §sa0{2} ∧ ={sc, Perm.m, Perm.mi, Redo.prefixes, i} ∧
            §p{1} = §p0{2} ∧ §C.c{1} = §C.c{2} - size §p0{2} + §i{2} ∧
            §pref{2} = §Redo.prefixes{2} ∧ all_prefixes §pref{2} ∧
            prefix_inv §C.queries{2} §pref{2} ∧
            «prefix» §p0{2} (get_max_prefix §p0{2} (elems (FMap.fdom §C.queries{2}))) = §i{2} ∧
            FMap.get §Redo.prefixes{2} (take §i{2} §p0{2}) = some (§sa0{2}, §sc{2}))
        · auto_progress
          all_goals first
            | smt_close [all_prefixes]
            | (generalize_reads_all; subst_vars
               first
                | exact prefix_sizel _ _
                | (apply rc_first_in <;> first | assumption | rfl))
        equiv_while_raw (§sa{1} = §sa0{2} ∧ ={sc, Perm.m, Perm.mi, Redo.prefixes, i} ∧
            §p{1} = §p0{2} ∧
            §C.c{1} = §C.c{2} - size §p0{2} +
              «prefix» §p0{2} (get_max_prefix §p0{2} (elems (FMap.fdom §C.queries{2}))) ∧
            §pref{2} = §Redo.prefixes{2} ∧ all_prefixes §pref{2} ∧
            prefix_inv §C.queries{2} §pref{2} ∧ 0 ≤ §i{2} ∧
            §i{2} ≤ «prefix» §p0{2} (get_max_prefix §p0{2} (elems (FMap.fdom §C.queries{2}))) ∧
            FMap.get §Redo.prefixes{2} (take §i{2} §p0{2}) = some (§sa0{2}, §sc{2}))
        · stmt_rcondt{1} 1
          · hoare_auto
          stmt_rcondt{2} 1
          · hoare_auto
          equiv_auto
          auto_progress
          · apply db_first_step <;> assumption
          · apply db_first_get; assumption
        · auto_close
        · auto_progress
          all_goals
            have := rc_first_exit (by assumption) (by assumption) (by assumption) (by assumption)
              (by assumption)
            omega
        · equiv_skip
          auto_progress
          generalize_reads_all; exact prefix_ge0 _ _
    · stmt_wp
      equiv_conseq (: _ ==> §sa{1} = (oget (FMap.get §Redo.prefixes{1} (take §i{1} §p{1}))).1 ∧
          §i{1} = size §p{1} ∧ FMap.get §Redo.prefixes{1} [] = some (b0, c0) ∧
          ={Perm.m, Perm.mi, Redo.prefixes, C.c})
      · auto_progress
        all_goals first
          | smt_close [take_size]
          | smt_close [take_size, prefix_inv]
          | smt_close [all_prefixes]
      equiv_while{1} (={Perm.m, Perm.mi, Redo.prefixes, C.c} ∧ FMap.dom §C.queries{2} §p{1} ∧
          prefix_inv §C.queries{2} §Redo.prefixes{1} ∧ 0 ≤ §i{1} ∧ §i{1} ≤ size §p{1} ∧
          FMap.get §Redo.prefixes{1} [] = some (b0, c0) ∧
          (§sa{1}, §sc{1}) = oget (FMap.get §Redo.prefixes{1} (take §i{1} §p{1})) ∧
          all_prefixes §Redo.prefixes{1}) ((size §p{1} - §i{1}).toNat)
      · while_ll_phoare
        intro σ₂
        stmt_rcondt 1
        · hoare_auto; smt_close [prefix_inv]
        phoare_auto
      · intro σ₂ k
        stmt_rcondt 1
        · hoare_auto; smt_close [prefix_inv]
        hoare_auto
        smt_close
      · auto_progress
        all_goals smt_close
      · equiv_skip
        auto_progress
        all_goals smt_close [size, take]
  stmt_wp; equiv_skip
  auto_progress
  all_goals first
    | smt_close [FMap.mem_set, FMap.mem_empty, FMap.get_setE]
    | (apply db_init_dom; assumption)

end

/-! The `glob`s of the concrete modules, which EC reads off their code (`Module.GlobBound`:
instance search derives the restrictions against them).  Not EC lemmas. -/

set_option maxHeartbeats 2000000 in
@[fp_bound] theorem fvP_SqueezelessSponge :
    FVP.fvP SqueezelessSponge ≤ Redo.prefixes.footprint := by
  fp_module Redo.prefixes

-- at the module types the lemmas ask for (`Perm` is a `PRIMITIVE` by definition, `@` keeps the
-- type: an ascription would elaborate to `Perm` at its own type)
instance : @Module.GlobBound CONSTRUCTION _ SqueezelessSponge Redo.prefixes.footprint :=
  ⟨fvP_SqueezelessSponge, by fp_finite⟩

set_option maxHeartbeats 2000000 in
@[fp_bound] theorem fvP_Perm :
    FVP.fvP (Perm : PRIMITIVE) ≤ Perm.m.footprint ⊔ Perm.mi.footprint := by
  rw [← Footprint.lens_pair]
  fp_module (Lens.pair Perm.m Perm.mi)

instance : @Module.GlobBound PRIMITIVE _ Perm (Perm.m.footprint ⊔ Perm.mi.footprint) :=
  ⟨fvP_Perm, by fp_finite⟩

set_option maxHeartbeats 2000000 in
theorem fvP_PRPi :
    FVP.fvP (Switching.PRPi.PRPi : Switching.PRPSec.PRP) ≤
      Switching.PRPi.m.footprint ⊔ Switching.PRPi.mi.footprint := by
  rw [← Footprint.lens_pair]
  fp_module (Lens.pair Switching.PRPi.m Switching.PRPi.mi)

instance : @Module.GlobBound Switching.PRPSec.PRP _ Switching.PRPi.PRPi
    (Switching.PRPi.m.footprint ⊔ Switching.PRPi.mi.footprint) :=
  ⟨fvP_PRPi, by fp_finite⟩

set_option maxHeartbeats 2000000 in
theorem fvP_ARP :
    FVP.fvP (Switching.ARP : Switching.PRPSec.PRP) ≤
      Switching.ARP.coll.footprint ⊔ (Switching.ARP.m.footprint ⊔ Switching.ARP.mi.footprint) := by
  rw [← Footprint.lens_pair, ← Footprint.lens_pair]
  fp_module (Lens.pair Switching.ARP.coll (Lens.pair Switching.ARP.m Switching.ARP.mi))

instance : @Module.GlobBound Switching.PRPSec.PRP _ Switching.ARP
    (Switching.ARP.coll.footprint ⊔ (Switching.ARP.m.footprint ⊔ Switching.ARP.mi.footprint)) :=
  ⟨fvP_ARP, by fp_finite⟩

set_option maxHeartbeats 4000000 in
/-- `D'(D)` touches `D`'s variables, `C`'s and `Redo.prefixes`.  Not an EC lemma. -/
theorem fvP_D' (D : DISTINGUISHER) : FVP.fvP (D' D) ≤
    FVP.fvP D ⊔ (C.c.footprint ⊔ C.queries.footprint ⊔ Redo.prefixes.footprint) := by
  rw [← Footprint.lens_pair, ← Footprint.lens_pair]
  fp_module (Lens.pair (Lens.pair C.c C.queries) Redo.prefixes)

set_option synthInstance.checkSynthOrder false in
/-- EC's `glob D'`: `glob D` and the variables of `D'`'s code. -/
instance (D : DISTINGUISHER) {S : Footprint VariableAssignment} [h : Module.Declared D S] :
    Module.ECGlob (D' D)
      ((FVP.fvP D).glob ⊔ (C.c.footprint ⊔ C.queries.footprint ⊔ Redo.prefixes.footprint)) :=
  ⟨(h.finite.sup (by fp_finite)).mono (fvP_D' D),
    (fvP_D' D).trans (sup_le_sup_right (Footprint.le_glob _) _),
    ⟨_, h.finite.sup (by fp_finite), sup_le (Footprint.glob_mono le_sup_left)
      (Footprint.le_glob_of_le le_sup_right)⟩⟩

namespace Switching

/-- The clone's `lemma Conclusion (D <: Distinguisher {-PRPi, -ARP, -DBounder}) &m:
(forall (O <: SPRP_Oracles{-D}), islossless O.f => islossless O.fi =>
islossless D(O).distinguish) => `|Pr[IND(PRPi,DBounder(D)).main() @ &m: res] -
Pr[IND(ARP,DBounder(D)).main() @ &m: res]| <= (q^2 - q)%r / 2%r * mu uD (pred1 witness)`: the
library's (`Lib/EC/Strong_RP_RF.lean`) at the clone's variables.  EC's restrictions are on EC's
`glob D` (`Module.ECGlob`, a local module's `glob` from its code): `D` outside the clone's
variables, the oracles `O <: SPRP_Oracles{-D}` declared against it. -/
theorem Conclusion (D : PRPSec.Distinguisher) {R : Footprint VariableAssignment}
    [hR : Module.ECGlob D R] [hD : Footprint.Outside R (PRPi.m.footprint ⊔ PRPi.mi.footprint ⊔
      ARP.coll.footprint ⊔ ARP.m.footprint ⊔ ARP.mi.footprint ⊔ DBounder.FBounder.c.footprint)]
    (m : VariableAssignment) :
    (∀ (O : PRPSec.SPRP_Oracles) [Module.Declared O R], islossless O.f → islossless O.fi →
      islossless (Module.app D O)) →
    |Pr[ PRPSec.IND(PRPi.PRPi, DBounder(D)).main () @ &m : §res ] -
      Pr[ PRPSec.IND(ARP, DBounder(D)).main () @ &m : §res ]| ≤
      ((max_size ^ 2 - max_size : ℤ) : ℝ) / 2 * (dstate.1 {default}).toReal := by
  intro hll
  obtain ⟨GF, hGF, hRGF⟩ := hR.base
  exact Strong_RP_RF.Conclusion_of_region state dstate max_size uD_uf_fu PRPi.m PRPi.mi
    ARP.m ARP.mi ARP.coll DBounder.FBounder.c (by fp_finite) D hR.finite R GF hGF hRGF hR.le hD.le
    m (fun O hOf hO hf hfi => @hll O ⟨hOf, hO⟩ hf hfi)

end Switching

section

-- EC's section's `D`, with the local clone's modules fresh for it (as `DoubleBounding`'s)
declare module D <: DISTINGUISHER {-Perm, -C, -PF, -Redo, -DBounder, -ARP, -PRPi.PRPi}

-- EC's `declare axiom D_ll`
variable (D_ll : ∀ (F <: DFUNCTIONALITY {-D}), ∀ (P <: DPRIMITIVE {-D}),
  islossless P.f → islossless P.fi → islossless F.f → islossless D(F, P).distinguish)

set_option maxHeartbeats 4000000 in
-- EC's restriction checks by instance search (`{-PRPi, -ARP, -DBounder}` on `glob D'`: 18 pairs
-- of variables)
set_option synthInstance.maxSize 1024 in
include D_ll in
/-- EC's `lemma Real_Concrete &m : Pr[GReal(D).main()@ &m: res /\ C.c <= max_size] <=
Pr[CF(DRestr(D)).main()@ &m: res] + (max_size ^ 2 - max_size)%r / 2%r * mu dstate (pred1
witness)`. -/
theorem Real_Concrete (m : VariableAssignment) :
    Pr[ (Pilot.SLCommon.GReal D) () @ &m : §res ∧ §C.c ≤ max_size ] ≤
      Pr[ (CF (DRestr D)) () @ &m : §res ] +
        ((max_size ^ 2 - max_size : ℤ) : ℝ) / 2 * (dstate.1 {default}).toReal := by
  rw [Real_GReal' D m]
  have p_ll : islossless Perm.f :=
    EC.PRP.RP.f_ll dD_ll (dprod_fu BitWord.dunifin_fu BitWord.dunifin_fu)
  have pi_ll : islossless Perm.fi :=
    EC.PRP.RP.fi_ll dD_ll (dprod_fu BitWord.dunifin_fu BitWord.dunifin_fu)
  have f_ll : islossless SqueezelessSponge(Perm).f := by
    phoare_proc
    phoare_while True ((size §p - §i).toNat)
    · intro z; stmt_wp; stmt_if
      · phoare_auto; smt_close
      · stmt_wp; phoare_call p_ll; phoare_auto; smt_close
    · phoare_auto
  apply le_trans (Pr_restr Perm SqueezelessSponge D p_ll pi_ll f_ll D_ll m)
  have e1 : Pr[ Indif(SqueezelessSponge(Perm), Perm, DRestr(D)).main () @ &m : §res ] =
      Pr[ PRPSec.IND(PRPi.PRPi, DBounder(D'(D))).main () @ &m : §res ] := by
    rw [← DoubleBounding D PRPi.PRPi m]
    byequiv; equiv_proc; stmt_inline*; stmt_wp
    equiv_call (_ : ={glob D, glob C, glob Redo} ∧ §Perm.m{1} = §PRPi.m{2} ∧
      §Perm.mi{1} = §PRPi.mi{2})
    all_goals try (equiv_proc; stmt_inline*)
    all_goals sim (_ : §Perm.m{1} = §PRPi.m{2} ∧ §Perm.mi{1} = §PRPi.mi{2})
    all_goals auto_close
  simp only [e1]
  have e2 : Pr[ (CF (DRestr D)) () @ &m : §res ] =
      Pr[ PRPSec.IND(ARP, DBounder(D'(D))).main () @ &m : §res ] := by
    rw [← DoubleBounding D ARP m]
    byequiv; equiv_proc; stmt_inline*; stmt_wp
    equiv_call (_ : ={glob D, glob C, glob Redo} ∧ §PF.m{1} = §ARP.m{2} ∧
      §PF.mi{1} = §ARP.mi{2})
    all_goals try (equiv_proc; stmt_inline*)
    all_goals sim (_ : §PF.m{1} = §ARP.m{2} ∧ §PF.mi{1} = §ARP.mi{2})
  simp only [e2]
  have := Switching.Conclusion (D' D) m ?D'_ll
  -- EC's `smt()`
  · linarith [(abs_le.1 this).2]
  case D'_ll =>
    intro O _ O_f_ll O_fi_ll
    phoare_proc; phoare_inline*; stmt_sp; stmt_wp
    phoare_call (@D_ll _ ?_ _ ?_ ?_ ?_ ?_)
    · phoare_auto
    · phoare_proc; stmt_sp; stmt_if
      · phoare_auto; phoare_call O_f_ll; phoare_auto
      · phoare_auto
    · phoare_proc; stmt_sp; stmt_if
      · phoare_auto; phoare_call O_fi_ll; phoare_auto
      · phoare_auto
    · phoare_proc; phoare_inline*; stmt_sp; stmt_if
      · stmt_if
        · stmt_wp
          phoare_while True ((size §p - §i).toNat)
          · intro z; stmt_wp; stmt_if
            · phoare_auto; smt_close
            · stmt_wp; phoare_call O_f_ll; phoare_auto; smt_close
          · phoare_auto
        · phoare_auto
      · phoare_auto

end

end GaudisCrypt.SHA3.Pilot.ConcreteF
