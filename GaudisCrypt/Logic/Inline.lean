import GaudisCrypt.Syntax.ProgramSyntax
import GaudisCrypt.Language.Modules
import GaudisCrypt.Logic.Hoare

/-!
# Flattening calls whose callee is spelled out

`Flatten.flattenProcedureCalls` rewrites every call of a statement whose callee is written out (a
`proc` literal) into the callee's body, and proves the result denotationally equivalent to the
input (`StmtWithHoles.EquivInLens`) along a lens that renames the locals.
`Flatten.flattenProcedure` does the same to a procedure, with a proof that its
`procedureDenotation` is unchanged.
`Flatten.unfoldProcedure` and `Flatten.inlineProcedure` first evaluate a callee named through
modules, so that it can be flattened.  The design is §4 of `NEW_PROCEDURES.md`.

One call is flattened by renaming the locals: the caller's keep their names (`Flatten.trafo`,
renaming by `Flatten.escape`, the identity on every name not starting with `@`), the callee's
frame moves to names the caller cannot have (`Flatten.emb`, renaming `n` to `@.n` by
`Flatten.tag`), and the call becomes

```
(resetSetter (Flatten.prefixed "@.")) <- ();  -- the callee's frame back to its initial values
«@.z₁», …, «@.zₙ» <- (args);                  -- the arguments, in the callee's parameter slots
‹callee body, renamed›
x <- ‹callee return value, renamed›;
```

The two renamings have disjoint images, which is what makes the callee's frame disjoint from the
caller's without looking at either.  Readable names come last, in a pass of their own
(`Flatten.renameNames`): a permutation of names (`Flatten.rename ren`, `«@.w» ↦ w0`), which is
sound for any choice of names.

What a reset puts back is given by a set of names, which every later round and the cleanup
renaming map along with the rest.  The cleaning keeps such a set in a normal form,
`{"z", "w0"} ∪ Flatten.prefixed "@@." \ {"@@.z", "@@.w"}` say (section *Reset regions*, and
`Flatten.cleanNameSet?`, the only meta code that knows that form).
-/

namespace GaudisCrypt

/-! ## Lens helpers -/

/-- Compose a getter with a lens between its containers. -/
def Lens.chainGetter {a : Type u} {s : Type v} {t : Type w} (l : Lens s t) (g : Getter a s) :
    Getter a t where
  get τ := g.get (l.get τ)

/-- Compose a setter with a lens between its containers. -/
def Lens.chainSetter {a : Type u} {s : Type v} {t : Type w} (l : Lens s t) (x : Setter a s) :
    Setter a t where
  set v τ := l.set (x.set v (l.get τ)) τ
  set_set σ u v := by simp [l.set_get, x.set_set, l.set_set]

@[simp] theorem Lens.id_chain {a : Type u} {m : Type v} (y : Lens a m) :
    Lens.chain Lens.id y = y := rfl

@[simp] theorem Lens.chain_id {a : Type u} {m : Type v} (x : Lens a m) :
    Lens.chain x Lens.id = x := rfl

/-- Chaining is associative. -/
theorem Lens.chain_assoc {a : Type u} {b : Type v} {c : Type w} {d : Type w'} (x : Lens c d)
    (y : Lens b c) (z : Lens a b) : (x.chain y).chain z = x.chain (y.chain z) := rfl

/-! ## Names

In a flattening round the caller's names go through `escape`, the callee's through `tag`; the two
have disjoint images (`escape_ne_tag`), and `escape` is the identity on every name that does not
start with `@`.  The readable names come from a separate permutation, `swaps ren`. -/

namespace Flatten

/-- `escape` on character lists: a leading `@` is doubled. -/
def escapeChars : List Char → List Char
  | [] => []
  | c :: cs => if c = '@' then '@' :: '@' :: cs else c :: cs

/-- The caller's names: `@…` ↦ `@@…`, every other name unchanged. -/
def escape (n : String) : String := String.ofList (escapeChars n.toList)

/-- The callee's names: `n` ↦ `@.n`. -/
def tag (n : String) : String := String.ofList ('@' :: '.' :: n.toList)

theorem escapeChars_injective : Function.Injective escapeChars := by
  intro l₁ l₂ h
  cases l₁ with
  | nil => cases l₂ with
    | nil => rfl
    | cons d ds => simp only [escapeChars] at h; split at h <;> simp at h
  | cons c cs => cases l₂ with
    | nil => simp only [escapeChars] at h; split at h <;> simp at h
    | cons d ds =>
      simp only [escapeChars] at h
      split at h <;> split at h <;> simp only [List.cons.injEq] at h <;> grind

theorem escape_injective : Function.Injective escape := fun a b h =>
  String.toList_injective (escapeChars_injective (by
    simpa only [escape, String.toList_ofList] using congrArg String.toList h))

theorem tag_injective : Function.Injective tag := fun a b h => by
  have h' := congrArg String.toList h
  simp only [tag, String.toList_ofList, List.cons.injEq, true_and] at h'
  exact String.toList_injective h'

/-- No caller name is a callee name. -/
theorem escape_ne_tag (a b : String) : escape a ≠ tag b := by
  intro h
  have h' := congrArg String.toList h
  simp only [escape, tag, String.toList_ofList] at h'
  cases ha : a.toList with
  | nil => simp [ha, escapeChars] at h'
  | cons c cs => simp only [ha, escapeChars] at h'; split at h' <;> simp_all

/-- The cleanup renaming: for each `(a, f)`, the names `a` and `f` swap places. -/
def swaps : List (String × String) → Equiv.Perm String
  | [] => 1
  | (a, f) :: ren => Equiv.swap a f * swaps ren

/-- The name `n` after the cleanup renaming `ren`. -/
def renameName (ren : List (String × String)) (n : String) : String := swaps ren n

theorem renameName_injective (ren : List (String × String)) :
    Function.Injective (renameName ren) :=
  (swaps ren).injective

end Flatten

/-! ## Renaming the locals of a program state -/

open Classical in
/-- Writing through one `embed` is invisible through another whose image is disjoint. -/
theorem VariableAssignment.embed_get_embed_set {ι₁ ι₂ : String → String}
    (h₁ : ι₁.Injective) (h₂ : ι₂.Injective) (hd : ∀ a b, ι₁ a ≠ ι₂ b)
    (w m : VariableAssignment) :
    (embed ι₁ h₁).get ((embed ι₂ h₂).set w m) = (embed ι₁ h₁).get m := by
  funext v
  change (if (v.withName (ι₁ v.name)).name ∈ Set.range ι₂ then _ else _) = _
  rw [if_neg]
  · rfl
  · rintro ⟨b, hb⟩
    exact hd _ _ hb.symm

/-! ## Reset regions

The names a flattened call resets start out as all of the callee's (`Set.univ`, seen through
`emb`), and every later round and the cleanup renaming map them along with the rest.  The
cleaning keeps such a set in the normal form `nf p add rem`, that is
`{add…} ∪ prefixed p \ {rem…}`: the names that start with `p`, except those in `rem`, and those
in `add`.  The three name maps keep that form: `tag` and `escape` move the prefix (`@.`, `@@.`,
…), and each swap of the cleanup renaming moves at most one name out of the set and one into it.

This section and `cleanNameSet?` (which computes the normal form, with these lemmas as proofs)
are all there is to the form; another one replaces both. -/

namespace Flatten

/-- The names that start with `p`. -/
def prefixed (p : String) : Set String := {n | p.toList <+: n.toList}

/-- The names in `l`.  Never printed: the cleaning writes it as a set literal (`ofList_cons`,
`ofList_singleton`). -/
def ofList (l : List String) : Set String := {n | n ∈ l}

theorem ofList_singleton (a : String) : ofList [a] = {a} := by ext n; simp [ofList]

theorem ofList_cons (a b : String) (l : List String) :
    ofList (a :: b :: l) = insert a (ofList (b :: l)) := by
  ext n; simp [ofList]

/-- The normal form of a reset region: the names that start with `p` and are not in `rem`, and
those in `add`.  Never printed: the cleaning writes it out without its empty parts
(`nf_eq_pretty` and the rest). -/
def nf (p : String) (add rem : List String) : Set String := ofList add ∪ prefixed p \ ofList rem

/-- Membership in `nf p add rem`, as a computation. -/
def memB (p : String) (add rem : List String) (n : String) : Bool :=
  add.contains n || (p.toList.isPrefixOf n.toList && !rem.contains n)

theorem nf_eq_setOf (p : String) (add rem : List String) :
    nf p add rem = {n | n ∈ add ∨ (p.toList <+: n.toList ∧ n ∉ rem)} := by
  ext n; simp [nf, ofList, prefixed]

theorem nf_eq_setOf_memB (p : String) (add rem : List String) :
    nf p add rem = {n | memB p add rem n = true} := by
  ext n; simp [nf, ofList, prefixed, memB, List.isPrefixOf_iff_prefix]

/-! `nf p add rem` written out, given the set literals `A`, `R` of `add`, `rem`. -/

theorem nf_nil_nil (p : String) : nf p [] [] = prefixed p := by ext n; simp [nf, ofList]

theorem nf_nil_eq (p : String) (add : List String) (A : Set String) (hA : ofList add = A) :
    nf p add [] = A ∪ prefixed p := by
  subst hA; ext n; simp [nf, ofList]

theorem nf_nil_left_eq (p : String) (rem : List String) (R : Set String) (hR : ofList rem = R) :
    nf p [] rem = prefixed p \ R := by
  subst hR; ext n; simp [nf, ofList]

theorem nf_eq_pretty (p : String) (add rem : List String) (A R : Set String)
    (hA : ofList add = A) (hR : ofList rem = R) : nf p add rem = A ∪ prefixed p \ R := by
  subst hA hR; rfl

theorem univ_eq_nf : (Set.univ : Set String) = nf "" [] [] := by
  ext n; simp [nf, ofList, prefixed]

/-- The image of a normal form under an injective name map that maps the names with prefix `p`
onto those with prefix `p'`. -/
theorem image_nf {ι : String → String} (hι : ι.Injective) {p p' : String}
    (h₁ : ∀ n : String, p.toList <+: n.toList → p'.toList <+: (ι n).toList)
    (h₂ : ∀ m : String, p'.toList <+: m.toList → ∃ n, ι n = m ∧ p.toList <+: n.toList)
    (add rem : List String) :
    ι '' nf p add rem = nf p' (add.map ι) (rem.map ι) := by
  rw [nf_eq_setOf, nf_eq_setOf]
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq, List.mem_map]
  constructor
  · rintro ⟨n, hn, he⟩
    rcases hn with hn | ⟨hp, hr⟩
    · exact Or.inl ⟨n, hn, he⟩
    · refine Or.inr ⟨he ▸ h₁ n hp, ?_⟩
      rintro ⟨x, hx, hxe⟩
      exact hr (hι (hxe.trans he.symm) ▸ hx)
  · rintro (⟨n, hn, he⟩ | ⟨hp, hr⟩)
    · exact ⟨n, Or.inl hn, he⟩
    · obtain ⟨n, he, hn⟩ := h₂ _ hp
      exact ⟨n, Or.inr ⟨hn, fun h => hr ⟨n, h, he⟩⟩, he⟩

theorem image_tag_nf (p : String) (add rem : List String) :
    tag '' nf p add rem = nf (tag p) (add.map tag) (rem.map tag) := by
  refine image_nf tag_injective (fun n hn => ?_) (fun m hm => ?_) add rem
  · simpa [tag, String.toList_ofList] using hn
  · obtain ⟨t, ht⟩ := hm
    refine ⟨String.ofList (p.toList ++ t), ?_, ⟨t, by simp⟩⟩
    apply String.toList_injective
    simpa [tag, String.toList_ofList] using ht

/-- `escape` moves a nonempty prefix along (the empty one it would not: `escape` maps the names
starting with `@` to those starting with `@@`, not onto all). -/
theorem image_escape_nf (p : String) (hp : p ≠ "") (add rem : List String) :
    escape '' nf p add rem = nf (escape p) (add.map escape) (rem.map escape) := by
  obtain ⟨c, cs, hpc⟩ : ∃ c cs, p.toList = c :: cs := by
    cases h : p.toList with
    | nil => exact absurd (String.toList_injective (h.trans String.toList_empty.symm)) hp
    | cons c cs => exact ⟨c, cs, rfl⟩
  refine image_nf escape_injective (fun n hn => ?_) (fun m hm => ?_) add rem
  · obtain ⟨t, ht⟩ := hn
    refine ⟨t, ?_⟩
    simp only [escape, String.toList_ofList, hpc, ← ht]
    by_cases hc : c = '@' <;> simp [escapeChars, hc]
  · obtain ⟨t, ht⟩ := hm
    simp only [escape, String.toList_ofList, hpc] at ht
    by_cases hc : c = '@'
    · refine ⟨String.ofList ('@' :: cs ++ t), ?_, ⟨t, by simp [hpc, hc]⟩⟩
      apply String.toList_injective
      simp [escape, escapeChars, ← ht, hc]
    · refine ⟨m, ?_, ⟨t, ?_⟩⟩
      · apply String.toList_injective
        simp [escape, escapeChars, ← ht, hc]
      · simpa [escapeChars, hc, hpc] using ht

/-- `nf p add' rem'` is the image of `nf p add rem` under the swap of `a` and `f`: `a` and `f`
trade membership, and the lists agree on every other name. -/
def swapOK (p : String) (add rem add' rem' : List String) (a f : String) : Bool :=
  memB p add' rem' a == memB p add rem f && memB p add' rem' f == memB p add rem a &&
  (add ++ add').all (fun x => x == a || x == f || add.contains x == add'.contains x) &&
  (rem ++ rem').all (fun x => x == a || x == f || rem.contains x == rem'.contains x)

theorem contains_eq_of_all {l l' : List String} {a f : String}
    (h : (l ++ l').all (fun x => x == a || x == f || l.contains x == l'.contains x) = true)
    {m : String} (ha : m ≠ a) (hf : m ≠ f) : l.contains m = l'.contains m := by
  simp only [List.all_eq_true, List.mem_append, Bool.or_eq_true, beq_iff_eq] at h
  by_cases hm : m ∈ l ∨ m ∈ l'
  · rcases h m hm with (h | h) | h
    · exact absurd h ha
    · exact absurd h hf
    · exact h
  · simp only [not_or] at hm
    simp [hm.1, hm.2]

theorem memB_swap {p : String} {add rem add' rem' : List String} {a f : String}
    (h : swapOK p add rem add' rem' a f = true) (m : String) :
    memB p add' rem' m = memB p add rem (Equiv.swap a f m) := by
  simp only [swapOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨ha, hf⟩, hadd⟩, hrem⟩ := h
  by_cases hma : m = a
  · subst hma; rw [Equiv.swap_apply_left, ha]
  by_cases hmf : m = f
  · subst hmf; rw [Equiv.swap_apply_right, hf]
  rw [Equiv.swap_apply_of_ne_of_ne hma hmf]
  simp only [memB, contains_eq_of_all hadd hma hmf, contains_eq_of_all hrem hma hmf]

/-! The steps of `cleanNameSet?`: each takes the region in normal form and a check that the
meta code proves by evaluation (`rfl`). -/

theorem image_tag_eq (S : Set String) (p : String) (add rem : List String) (p' : String)
    (add' rem' : List String) (hS : S = nf p add rem)
    (h : (tag p == p' && add.map tag == add' && rem.map tag == rem') = true) :
    tag '' S = nf p' add' rem' := by
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
  rw [hS, image_tag_nf]

theorem image_escape_eq (S : Set String) (p : String) (add rem : List String) (p' : String)
    (add' rem' : List String) (hS : S = nf p add rem)
    (h : (p != "" && escape p == p' && add.map escape == add' && rem.map escape == rem') = true) :
    escape '' S = nf p' add' rem' := by
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at h
  obtain ⟨⟨⟨hp, rfl⟩, rfl⟩, rfl⟩ := h
  rw [hS, image_escape_nf p hp]

theorem image_renameName_nil (S : Set String) (p : String) (add rem : List String)
    (hS : S = nf p add rem) : renameName [] '' S = nf p add rem := by
  rw [← hS]
  exact Set.image_id S

theorem image_renameName_cons (S : Set String) (a f : String)
    (ren : List (String × String)) (p : String) (add rem add' rem' : List String)
    (hS : renameName ren '' S = nf p add rem)
    (h : swapOK p add rem add' rem' a f = true) :
    renameName ((a, f) :: ren) '' S = nf p add' rem' := by
  have : renameName ((a, f) :: ren) '' S = Equiv.swap a f '' (renameName ren '' S) := by
    rw [Set.image_image]; rfl
  rw [this, hS, nf_eq_setOf_memB, nf_eq_setOf_memB]
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn, he⟩
    rw [memB_swap h, ← he, Equiv.swap_apply_self]; exact hn
  · intro hw
    exact ⟨Equiv.swap a f w, by rw [← memB_swap h]; exact hw, Equiv.swap_apply_self _ _ _⟩

end Flatten

/-- The slot of a variable whose name is given as another term for the same string. -/
theorem varLens_rename {n n' : String} {T : Type} (i : Nonempty T) (k : Nat)
    (hk : k = VariableName.encode n) (k' : Nat) (hk' : k' = VariableName.encode n') (h : n = n') :
    (varLens (@VariableName.mk n T i k hk) : Lens T VariableAssignment)
      = varLens (@VariableName.mk n' T i k' hk') := by
  subst h hk hk'
  rfl

variable [ProgramSpec]

/-- A lens on the locals, as a lens on the program state that keeps the globals. -/
def ProgramState.mapLocal (m : Lens VariableAssignment VariableAssignment) :
    Lens ProgramState ProgramState where
  get t := ⟨t.globals, m.get t.locals⟩
  set v t := ⟨v.globals, m.set v.locals t.locals⟩
  set_get s x := by simp [m.set_get]
  set_set s x y := by simp [m.set_set]
  get_set s := by simp [m.get_set]

theorem ProgramState.mapLocal_chain_globalL (m : Lens VariableAssignment VariableAssignment) :
    (mapLocal m).chain globalL = globalL := by
  refine Lens.ext _ _ fun v s => ?_
  change (⟨v, m.set (m.get s.locals) s.locals⟩ : ProgramState) = ⟨v, s.locals⟩
  rw [m.get_set]

@[simp] theorem ProgramState.mapLocal_chain_intoLocal {A : Type u}
    (m : Lens VariableAssignment VariableAssignment) (L : Lens A VariableAssignment) :
    (mapLocal m).chain L.intoLocal = (m.chain L).intoLocal := rfl

@[simp] theorem ProgramState.mapLocal_chain_intoGlobal {A : Type u}
    (m : Lens VariableAssignment VariableAssignment) (g : Lens A State) :
    (mapLocal m).chain g.intoGlobal = g.intoGlobal := by
  refine Lens.ext _ _ fun v s => ?_
  change (⟨g.set v s.globals, m.set (m.get s.locals) s.locals⟩ : ProgramState)
    = ⟨g.set v s.globals, s.locals⟩
  rw [m.get_set]

/-- **Cleaning**: a local variable seen through a renaming of the locals is the renamed variable.
(The content type is spelled `T` rather than `(VariableName.mk n T …).type`: `simp` reduces the
latter in the term before it looks for lemmas, so a lemma indexed by it would never be found.) -/
theorem ProgramState.mapLocal_embed_chain_varLens (ι : String → String) (hι : ι.Injective)
    (n : String) (T : Type) (i : Nonempty T) (k : Nat) (hk : k = VariableName.encode n) :
    @Lens.chain T _ _ (mapLocal (VariableAssignment.embed ι hι))
      (@Lens.intoLocal _ T (varLens (@VariableName.mk n T i k hk)))
      = (varLens (@VariableName.mk (ι n) T i (VariableName.encode (ι n)) rfl)).intoLocal := by
  rw [mapLocal_chain_intoLocal, VariableAssignment.embed_chain_varLens]
  rfl

/-- A renaming of the locals leaves the entry state of a procedure alone when it keeps the names
of the parameters: the parameters are where they were, and every other slot is `init`, whatever
it is called. -/
theorem ProgramState.mapLocal_embed_get_entry (ι : String → String) (hι : ι.Injective)
    (names : List String) (tys : List Type) (hlen : names.length = tys.length)
    (hfix : ∀ n ∈ names, ι n = n) (args : typeListToTuple tys) (st : State) :
    (mapLocal (VariableAssignment.embed ι hι)).get
        ⟨st, VariableAssignment.setParams names tys hlen args VariableAssignment.init⟩
      = ⟨st, VariableAssignment.setParams names tys hlen args VariableAssignment.init⟩ := by
  change (⟨st, fun v => VariableAssignment.setParams names tys hlen args VariableAssignment.init
      (v.withName (ι v.name))⟩ : ProgramState) = _
  congr 1
  funext v
  by_cases hv : v.name ∈ names
  · exact VariableAssignment.apply_withName _ v (hfix _ hv)
  · have hv' : (v.withName (ι v.name)).name ∉ names := by
      intro hm
      apply hv
      have := hfix _ hm
      rw [VariableName.withName_name] at this hm
      rwa [← hι this]
    rw [VariableAssignment.setParams_apply_of_notMem _ _ _ _ _ _ hv',
      VariableAssignment.setParams_apply_of_notMem _ _ _ _ _ _ hv]
    rfl

open Classical in
/-- **Cleaning**: a reset seen through a renaming of the locals resets the renamed names. -/
theorem ProgramState.mapLocal_embed_chainSetter_resetSetter (ι : String → String)
    (hι : ι.Injective) (S : Set String) :
    (mapLocal (VariableAssignment.embed ι hι)).chainSetter (resetSetter S)
      = resetSetter (ι '' S) := by
  ext x σ
  change (⟨σ.globals, fun w => if w.name ∈ Set.range ι then
      (if Function.invFun ι w.name ∈ S then VariableAssignment.init _
        else σ.locals ((w.withName (Function.invFun ι w.name)).withName
          (ι (Function.invFun ι w.name)))) else σ.locals w⟩ : ProgramState)
    = ⟨σ.globals, fun w => if w.name ∈ ι '' S then VariableAssignment.init w else σ.locals w⟩
  congr 1
  funext w
  by_cases hw : w.name ∈ Set.range ι
  · have hinv : ι (Function.invFun ι w.name) = w.name := Function.invFun_eq hw
    have hmem : Function.invFun ι w.name ∈ S ↔ w.name ∈ ι '' S := by
      constructor
      · intro h
        exact ⟨_, h, hinv⟩
      · rintro ⟨n, hn, he⟩
        rwa [← he, Function.leftInverse_invFun hι n]
    rw [if_pos hw]
    by_cases hS : w.name ∈ ι '' S
    · -- `init` does not look at the name
      rw [if_pos (hmem.mpr hS), if_pos hS]
    · rw [if_neg (fun h => hS (hmem.mp h)), if_neg hS]
      exact σ.locals.apply_withName w hinv
  · have hS : w.name ∉ ι '' S := fun h => hw (Set.image_subset_range ι S h)
    rw [if_neg hw, if_neg hS]

/-- Resetting every variable. -/
theorem resetSetter_univ_set (x : Unit) (σ : ProgramState) :
    (resetSetter Set.univ).set x σ = ⟨σ.globals, VariableAssignment.init⟩ := by
  simp [resetSetter]

namespace Flatten

/-- The caller's side of a flattening round: its locals, renamed by `escape` (which keeps every
name that does not start with `@`). -/
noncomputable def trafo : Lens ProgramState ProgramState :=
  ProgramState.mapLocal (VariableAssignment.embed escape escape_injective)

/-- The callee's frame inside the caller's locals, renamed by `tag` (`n ↦ @.n`). -/
noncomputable def emb : Lens ProgramState ProgramState :=
  ProgramState.mapLocal (VariableAssignment.embed tag tag_injective)

/-- The cleanup renaming `ren`, on the locals: a permutation of the names, hence an
isomorphism. -/
noncomputable def rename (ren : List (String × String)) : Lens ProgramState ProgramState :=
  ProgramState.mapLocal (VariableAssignment.embed (renameName ren) (renameName_injective ren))

theorem trafo_chain_globalL : trafo.chain ProgramState.globalL = ProgramState.globalL :=
  ProgramState.mapLocal_chain_globalL _

theorem emb_chain_globalL : emb.chain ProgramState.globalL = ProgramState.globalL :=
  ProgramState.mapLocal_chain_globalL _

theorem rename_chain_globalL (ren : List (String × String)) :
    (rename ren).chain ProgramState.globalL = ProgramState.globalL :=
  ProgramState.mapLocal_chain_globalL _

/-- Writing the callee's frame is invisible to the caller, except for the globals. -/
theorem trafo_get_emb_set (v τ : ProgramState) :
    trafo.get (emb.set v τ) = ProgramState.globalL.set v.globals (trafo.get τ) := by
  change (⟨v.globals, (VariableAssignment.embed escape escape_injective).get
      ((VariableAssignment.embed tag tag_injective).set v.locals τ.locals)⟩ : ProgramState) = _
  rw [VariableAssignment.embed_get_embed_set _ _ escape_ne_tag]
  rfl

/-- The reset a flattened call starts with: every variable of the callee, seen through `emb`,
which is the callee's frame. -/
theorem emb_chainSetter_resetSetter_univ_set (τ : ProgramState) :
    (emb.chainSetter (resetSetter Set.univ)).set () τ
      = emb.set ⟨τ.globals, VariableAssignment.init⟩ τ := by
  change emb.set ((resetSetter Set.univ).set () (emb.get τ)) τ = _
  rw [resetSetter_univ_set]
  rfl

/-- **Cleaning**: a caller's local variable, seen through `trafo`, is the escaped variable. -/
@[simp] theorem trafo_chain_varLens (n : String) (T : Type) (i : Nonempty T) (k : Nat)
    (hk : k = VariableName.encode n) :
    @Lens.chain T _ _ trafo (@Lens.intoLocal _ T (varLens (@VariableName.mk n T i k hk)))
      = (varLens (@VariableName.mk (escape n) T i
          (VariableName.encode (escape n)) rfl)).intoLocal :=
  ProgramState.mapLocal_embed_chain_varLens _ _ n T i k hk

/-- **Cleaning**: a callee's local variable, seen through `emb`, is the tagged variable. -/
@[simp] theorem emb_chain_varLens (n : String) (T : Type) (i : Nonempty T) (k : Nat)
    (hk : k = VariableName.encode n) :
    @Lens.chain T _ _ emb (@Lens.intoLocal _ T (varLens (@VariableName.mk n T i k hk)))
      = (varLens (@VariableName.mk (tag n) T i (VariableName.encode (tag n)) rfl)).intoLocal :=
  ProgramState.mapLocal_embed_chain_varLens _ _ n T i k hk

/-- **Cleaning**: a local variable, seen through the cleanup renaming, is the renamed
variable. -/
@[simp] theorem rename_chain_varLens (ren : List (String × String)) (n : String) (T : Type)
    (i : Nonempty T) (k : Nat) (hk : k = VariableName.encode n) :
    @Lens.chain T _ _ (rename ren) (@Lens.intoLocal _ T (varLens (@VariableName.mk n T i k hk)))
      = (varLens (@VariableName.mk (renameName ren n) T i
          (VariableName.encode (renameName ren n)) rfl)).intoLocal :=
  ProgramState.mapLocal_embed_chain_varLens _ _ n T i k hk

/-- `emb_chain_varLens`, with the new name given: what the meta code instantiates, proving the
name by evaluation. -/
theorem emb_chain_varLens_eq (n : String) (T : Type) (i : Nonempty T) (k : Nat)
    (hk : k = VariableName.encode n) (f : String) (k' : Nat) (hk' : k' = VariableName.encode f)
    (h : tag n = f) :
    emb.chain (varLens (@VariableName.mk n T i k hk)).intoLocal
      = (varLens (@VariableName.mk f T i k' hk')).intoLocal := by
  rw [emb_chain_varLens]
  subst h hk'
  rfl

end Flatten

omit [ProgramSpec] in
/-- A lens composed with a pair is the pair of the composites — stated with the composites
given up to an equation (and any `Disjoint` instance for them), so that the cleaning pass can
rewrite the components and re-synthesize the instance (`Flatten.reduceChainPair`). -/
theorem Lens.chain_pair_eq {a b : Type u} {s : Type v} {t : Type w} (l : Lens s t)
    (x : Lens a s) (y : Lens b s) [Lens.Disjoint x y] (x' : Lens a t) (y' : Lens b t)
    [Lens.Disjoint x' y'] (hx : l.chain x = x') (hy : l.chain y = y') :
    l.chain (Lens.pair x y) = Lens.pair x' y' := by
  subst hx hy
  refine Lens.ext _ _ fun v σ => ?_
  change l.set (x.set v.1 (y.set v.2 (l.get σ))) σ
    = l.set (x.set v.1 (l.get (l.set (y.set v.2 (l.get σ)) σ))) (l.set (y.set v.2 (l.get σ)) σ)
  rw [l.set_get, l.set_set]

/-! ## Re-targeting a statement along a lens -/

/-- Re-target a statement along a lens between program states.  The `call'` case does not
recurse into the callee: its body and return value run in the callee's own frame, which the lens
does not touch. -/
def StmtWithHoles.applyLens {h : HoleSigs} (l : Lens ProgramState ProgramState) :
    StmtWithHoles h → StmtWithHoles h
  | .skip                   => .skip
  | .sample x e             => .sample (l.chainSetter x) (l.chainGetter e)
  | .call' x ns hl hn b r p => .call' (l.chainSetter x) ns hl hn b r (l.chainGetter p)
  | .hole n x p             => .hole n (l.chainSetter x) (l.chainGetter p)
  | .seq s₁ s₂              => .seq (s₁.applyLens l) (s₂.applyLens l)
  | .ifThenElse c t e       => .ifThenElse (l.chainGetter c) (t.applyLens l) (e.applyLens l)
  | .while c b              => .while (l.chainGetter c) (b.applyLens l)

/-- `applyLens` commutes with hole instantiation: it never touches a hole's index, and the
`hole ↦ call` step only re-tags the same setter and getter. -/
theorem StmtWithHoles.applyLens_instantiate {h : HoleSigs} (l : Lens ProgramState ProgramState)
    (inst : h.Instantiation) :
    ∀ s : StmtWithHoles h, (s.applyLens l).instantiate inst = (s.instantiate inst).applyLens l
  | .skip                    => rfl
  | .sample _ _              => rfl
  | .call' _ _ _ _ _ _ _     => rfl
  | .hole _ _ _              => rfl
  | .seq s₁ s₂               => by
      simp only [StmtWithHoles.applyLens, StmtWithHoles.instantiate,
        applyLens_instantiate l inst s₁, applyLens_instantiate l inst s₂]
  | .ifThenElse _ t e        => by
      simp only [StmtWithHoles.applyLens, StmtWithHoles.instantiate,
        applyLens_instantiate l inst t, applyLens_instantiate l inst e]
  | .while _ b               => by
      simp only [StmtWithHoles.applyLens, StmtWithHoles.instantiate,
        applyLens_instantiate l inst b]

/-! ## Denotational equivalence along a lens -/

/-- Push a state map through a denotation's result: `(u, τ) ↦ (u, f τ)`. -/
noncomputable def SubProbability.mapState {α : Type v} {s t : Type u} (f : t → s)
    (μ : SubProbability (α × t)) : SubProbability (α × s) :=
  (fun p => (p.1, f p.2)) <$> μ

/-- `b`, running on the wide state `t`, is denotationally equivalent to `a`, running on the
narrow state `s`, in the lens `l : Lens s t`: from any wide state, running `b` and projecting the
result with `l.get` gives the same subdistribution as running `a` from the projected state.

Nothing is assumed about the part of the wide state that `l` does not see — in particular the
frame of a flattened callee, which the flattened code resets before it reads it. -/
def ProgramDenotation.EquivInLens {s t : Type u} {α : Type v} (a : ProgramDenotation s α)
    (b : ProgramDenotation t α) (l : Lens s t) : Prop :=
  ∀ (sa : s) (sb : t), sa = l.get sb → (b sb).mapState l.get = a sa

/-- The statement-level relation.  `programDenotation` needs a hole-free statement and the
rewrites here leave hole indices untouched, so the instantiation is quantified — the same one on
both sides. -/
def StmtWithHoles.EquivInLens {hCtx : HoleSigs} (a b : StmtWithHoles hCtx)
    (l : Lens ProgramState ProgramState) : Prop :=
  ∀ inst : hCtx.Instantiation,
    (programDenotation (a.instantiate inst)).EquivInLens
      (programDenotation (b.instantiate inst)) l

/-- Denotational equivalence without renaming — what `flattenSeq` proves. -/
abbrev StmtWithHoles.Equiv {hCtx : HoleSigs} (a b : StmtWithHoles hCtx) : Prop :=
  a.EquivInLens b Lens.id

/-! ## `zoom` against the primitives -/

omit [ProgramSpec] in
/-- `ProgramDenotation.get` applied at a state — the `Getter` version of
`ProgramDenotation.get_apply` (which is stated for a `Lens`). -/
theorem ProgramDenotation.get_apply' {s : Type u} {a : Type v} (g : Getter a s) (st : s) :
    ProgramDenotation.get g st = pure (g.get st, st) := rfl

omit [ProgramSpec] in
/-- `ProgramDenotation.set` applied at a state — the `Setter` version of
`ProgramDenotation.set_apply` (which is stated for a `Lens`). -/
theorem ProgramDenotation.set_apply' {s : Type u} {a : Type v} (x : Setter a s) (v : a)
    (st : s) : ProgramDenotation.set x v st = pure ((), x.set v st) := rfl

omit [ProgramSpec] in
/-- Zooming twice is zooming along the chained lens. -/
theorem ProgramDenotation.zoom_chain {s : Type u₁} {t : Type u₂} {u : Type u₃} {a : Type v}
    (x : Lens t u) (y : Lens s t) (p : ProgramDenotation s a) :
    ProgramDenotation.zoom (x.chain y) p
      = ProgramDenotation.zoom x (ProgramDenotation.zoom y p) := by
  funext uv
  change (p (y.get (x.get uv))).hbind (fun as => pure (as.1, x.set (y.set as.2 (x.get uv)) uv))
       = ((p (y.get (x.get uv))).hbind fun as => pure (as.1, y.set as.2 (x.get uv))).hbind
            fun bs => pure (bs.1, x.set bs.2 uv)
  rw [SubProbability.hbind_assoc]
  congr 1; funext as
  rw [SubProbability.pure_hbind]

omit [ProgramSpec] in
/-- Reading through a zoomed lens is reading through the composed getter. -/
theorem ProgramDenotation.zoom_get {s t : Type u} {a : Type v} (l : Lens s t) (g : Getter a s) :
    ProgramDenotation.zoom l (ProgramDenotation.get g)
      = ProgramDenotation.get (l.chainGetter g) := by
  funext tv
  change (ProgramDenotation.get g (l.get tv)).hbind (fun as => pure (as.1, l.set as.2 tv))
    = ProgramDenotation.get (l.chainGetter g) tv
  rw [ProgramDenotation.get_apply', ProgramDenotation.get_apply', SubProbability.pure_hbind]
  simp only [l.get_set]
  rfl

omit [ProgramSpec] in
/-- Writing through a zoomed lens is writing through the composed setter. -/
theorem ProgramDenotation.zoom_set {s t : Type u} {a : Type v} (l : Lens s t) (x : Setter a s)
    (v : a) :
    ProgramDenotation.zoom l (ProgramDenotation.set x v)
      = ProgramDenotation.set (l.chainSetter x) v := by
  funext tv
  change (ProgramDenotation.set x v (l.get tv)).hbind (fun as => pure (as.1, l.set as.2 tv))
    = ProgramDenotation.set (l.chainSetter x) v tv
  rw [ProgramDenotation.set_apply', ProgramDenotation.set_apply', SubProbability.pure_hbind]
  rfl

omit [ProgramSpec] in
/-- A state-blind draw is unaffected by zooming. -/
theorem ProgramDenotation.zoom_lift {s t : Type u} {a : Type v} (l : Lens s t)
    (μ : SubProbability a) :
    ProgramDenotation.zoom l (μ.toProgramDenotation : ProgramDenotation s a)
      = (μ.toProgramDenotation : ProgramDenotation t a) := by
  funext tv
  change (μ.hbind fun v => pure (v, l.get tv)).hbind (fun as => pure (as.1, l.set as.2 tv))
    = μ.hbind fun v => pure (v, tv)
  rw [SubProbability.hbind_assoc]
  congr 1; funext v
  rw [SubProbability.pure_hbind]
  simp only [l.get_set]

omit [ProgramSpec] in
/-- Zooming the everywhere-diverging program diverges. -/
theorem ProgramDenotation.zoom_bot {s t : Type u} {a : Type v} (l : Lens s t) :
    ProgramDenotation.zoom l (⊥ : ProgramDenotation s a) = ⊥ := by
  funext tv
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_left _

omit [ProgramSpec] in
/-- `zoom` is ω-continuous in its program argument — what the loop case needs. -/
theorem ProgramDenotation.zoom_ωScottContinuous {s t : Type u} {a : Type v} (l : Lens s t) :
    OmegaCompletePartialOrder.ωScottContinuous
      (fun (m : ProgramDenotation s a) => ProgramDenotation.zoom l m) := by
  refine OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup ⟨?mono, ?sup⟩
  case mono =>
    intro m₁ m₂ h τ
    exact SubProbability.bind_mono (fun m : ProgramDenotation s a => m (l.get τ))
      (fun _ (p : a × s) => (pure (p.1, l.set p.2 τ) : SubProbability (a × t)))
      (fun _ _ hh => Pi.le_def.mp hh (l.get τ)) (fun _ _ _ => le_rfl) h
  case sup =>
    intro ch
    funext τ
    refine (SubProbability.bind_ωScottContinuous (fun m : ProgramDenotation s a => m (l.get τ))
      (fun _ (p : a × s) => (pure (p.1, l.set p.2 τ) : SubProbability (a × t))) ?_ ?_).map_ωSup ch
    · exact OmegaCompletePartialOrder.ωScottContinuous.const
    · exact OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup
        ⟨fun _ _ hh => Pi.le_def.mp hh (l.get τ), fun _ => rfl⟩

omit [ProgramSpec] in
/-- **`zoom` commutes with `while_loop`** (Kleene/ωSup argument): running the whole loop in the
sublens and writing back once is the same as writing back after every iteration. -/
theorem ProgramDenotation.zoom_while {s t : Type u} (l : Lens s t)
    (cond : ProgramDenotation s Bool) (body : ProgramDenotation s Unit) :
    ProgramDenotation.zoom l (while_loop cond body)
      = while_loop (ProgramDenotation.zoom l cond) (ProgramDenotation.zoom l body) := by
  let F := while_iteration cond body
  let G := while_iteration (ProgramDenotation.zoom l cond) (ProgramDenotation.zoom l body)
  have key : ∀ n : ℕ,
      ProgramDenotation.zoom l ((F^[n] (⊥ : Unit → ProgramDenotation s Unit)) ())
        = (G^[n] (⊥ : Unit → ProgramDenotation t Unit)) () := by
    intro n
    induction n with
    | zero => exact ProgramDenotation.zoom_bot l
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change ProgramDenotation.zoom l (cond >>= fun b =>
          if b = true then body >>= fun _ => (F^[n] ⊥) ()
          else (pure () : ProgramDenotation s Unit))
        = (ProgramDenotation.zoom l cond) >>= fun b =>
          if b = true then (ProgramDenotation.zoom l body) >>= fun _ => (G^[n] ⊥) ()
          else (pure () : ProgramDenotation t Unit)
      rw [ProgramDenotation.zoom_bind]
      congr 1; funext b
      by_cases h : b = true
      · simp only [h, if_true]
        rw [ProgramDenotation.zoom_bind]
        congr 1; funext _
        exact ih
      · simp only [h, Bool.false_eq_true, if_false]
        exact ProgramDenotation.zoom_pure l ()
  change ProgramDenotation.zoom l (F.lfp ()) = G.lfp ()
  let chainF : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation s Unit) :=
    ⟨fun n => F^[n] ⊥, Monotone.monotone_iterate_of_le_map F.monotone (OrderBot.bot_le _)⟩
  let chainG : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation t Unit) :=
    ⟨fun n => G^[n] ⊥, Monotone.monotone_iterate_of_le_map G.monotone (OrderBot.bot_le _)⟩
  have hF_at : F.lfp () = OmegaCompletePartialOrder.ωSup
      (chainF.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := rfl
  have hG_at : G.lfp () = OmegaCompletePartialOrder.ωSup
      (chainG.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := rfl
  rw [hF_at, hG_at, (ProgramDenotation.zoom_ωScottContinuous l).map_ωSup]
  congr 1
  ext n
  exact key n

/-! ## The transport theorem

`applyLens l s` runs `s` in the sublens `l` — which is exactly `zoom l`.  The only assumption is
that `l` leaves the globals alone, which is what a `call` needs (the callee runs on the globals,
and must see the same ones before and after re-targeting).

This holds for an *arbitrary* statement `s`, which is why the flattener may wrap whole
subprograms in `applyLens` without looking at them. -/

theorem programDenotation_applyLens (l : Lens ProgramState ProgramState)
    (hglob : l.chain ProgramState.globalL = ProgramState.globalL) :
    ∀ s : Stmt,
      programDenotation (s.applyLens l) = ProgramDenotation.zoom l (programDenotation s)
  | .skip => by
      simp only [StmtWithHoles.applyLens, programDenotation, ProgramDenotation.skip]
      exact (ProgramDenotation.zoom_pure l ()).symm
  | .sample x e => by
      simp only [StmtWithHoles.applyLens, programDenotation]
      rw [ProgramDenotation.zoom_bind, ProgramDenotation.zoom_get]
      congr 1; funext μ
      rw [ProgramDenotation.zoom_bind, ProgramDenotation.zoom_lift]
      congr 1; funext v
      rw [ProgramDenotation.zoom_set]
  | .call' x ns hl hn b r p => by
      simp only [StmtWithHoles.applyLens, programDenotation_call']
      rw [ProgramDenotation.zoom_bind, ProgramDenotation.zoom_get]
      congr 1; funext args
      rw [ProgramDenotation.zoom_bind, ← ProgramDenotation.zoom_chain, hglob]
      congr 1; funext ret
      rw [ProgramDenotation.zoom_set]
  | .seq s₁ s₂ => by
      simp only [StmtWithHoles.applyLens, programDenotation,
        programDenotation_applyLens l hglob s₁, programDenotation_applyLens l hglob s₂]
      rw [ProgramDenotation.zoom_bind]
  | .ifThenElse c s₁ s₂ => by
      simp only [StmtWithHoles.applyLens, programDenotation,
        programDenotation_applyLens l hglob s₁, programDenotation_applyLens l hglob s₂]
      rw [ProgramDenotation.zoom_bind, ProgramDenotation.zoom_get]
      congr 1; funext bv
      cases bv <;> simp
  | .while c s => by
      simp only [StmtWithHoles.applyLens, programDenotation,
        programDenotation_applyLens l hglob s]
      rw [ProgramDenotation.zoom_while, ProgramDenotation.zoom_get]
  termination_by s => s.depth
  decreasing_by all_goals simp only [StmtWithHoles.depth]; omega

omit [ProgramSpec] in
/-- Zooming is always a correct replacement: projecting the result of the zoomed program back
gives the original program's result. -/
theorem ProgramDenotation.equivInLens_zoom {s t : Type u} {α : Type v} (l : Lens s t)
    (p : ProgramDenotation s α) : p.EquivInLens (ProgramDenotation.zoom l p) l := by
  rintro sa sb rfl
  change ((ProgramDenotation.zoom l p sb) >>= fun q => pure (q.1, l.get q.2)) = p (l.get sb)
  change ((p (l.get sb) >>= fun as => pure (as.1, l.set as.2 sb))
            >>= fun q => pure (q.1, l.get q.2)) = p (l.get sb)
  have key : (fun as : α × s => (pure (as.1, l.set as.2 sb) : SubProbability (α × t))
                 >>= fun q => pure (q.1, l.get q.2))
           = (pure : α × s → SubProbability (α × s)) := by
    funext as
    rw [SubProbability.pure_bind]
    simp only [l.set_get]
  rw [SubProbability.bind_assoc, key]
  exact SubProbability.bind_pure _

/-- **`applyLens` is always the right replacement**: whatever the statement, re-targeting it
along a globals-preserving lens is denotationally equivalent in that lens. -/
theorem StmtWithHoles.equivInLens_applyLens {hCtx : HoleSigs} (l : Lens ProgramState ProgramState)
    (hglob : l.chain ProgramState.globalL = ProgramState.globalL)
    (s : StmtWithHoles hCtx) : s.EquivInLens (s.applyLens l) l := by
  intro inst
  rw [StmtWithHoles.applyLens_instantiate, programDenotation_applyLens l hglob]
  exact ProgramDenotation.equivInLens_zoom l _

/-! ## `EquivInLens` is a congruence

What the flattener needs along the path down to the call it is rewriting. -/

omit [ProgramSpec] in
/-- `mapState` spelled out as a `bind`, for rewriting. -/
theorem SubProbability.mapState_eq {α : Type v} {s t : Type u} (f : t → s)
    (μ : SubProbability (α × t)) : μ.mapState f = μ >>= fun q => pure (q.1, f q.2) := rfl

omit [ProgramSpec] in
/-- `pure` is equivalent to itself. -/
theorem ProgramDenotation.EquivInLens.pure {s t : Type u} {α : Type v} {l : Lens s t} (a : α) :
    (Pure.pure a : ProgramDenotation s α).EquivInLens (Pure.pure a) l := by
  rintro sa sb rfl
  change ((Pure.pure (a, sb) : SubProbability (α × t))
      >>= fun q => (Pure.pure (q.1, l.get q.2) : SubProbability (α × s))) = _
  rw [SubProbability.pure_bind]
  rfl

omit [ProgramSpec] in
/-- Diverging is equivalent to diverging. -/
theorem ProgramDenotation.EquivInLens.bot {s t : Type u} {α : Type v} {l : Lens s t} :
    (⊥ : ProgramDenotation s α).EquivInLens ⊥ l := by
  rintro sa sb rfl
  apply Subtype.ext
  exact MeasureTheory.Measure.bind_zero_left _

omit [ProgramSpec] in
/-- Reading through the composed getter is equivalent to reading through the original one. -/
theorem ProgramDenotation.EquivInLens.get {s t : Type u} {α : Type v} (l : Lens s t)
    (g : Getter α s) :
    (ProgramDenotation.get g).EquivInLens (ProgramDenotation.get (l.chainGetter g)) l := by
  rintro sa sb rfl
  change (ProgramDenotation.get (l.chainGetter g) sb
      >>= fun q => (Pure.pure (q.1, l.get q.2) : SubProbability (α × s)))
    = ProgramDenotation.get g (l.get sb)
  rw [ProgramDenotation.get_apply', ProgramDenotation.get_apply', SubProbability.pure_bind]
  rfl

omit [ProgramSpec] in
/-- Writing through the composed setter is equivalent to writing through the original one. -/
theorem ProgramDenotation.EquivInLens.set {s t : Type u} {α : Type v} (l : Lens s t)
    (x : Setter α s) (v : α) :
    (ProgramDenotation.set x v).EquivInLens (ProgramDenotation.set (l.chainSetter x) v) l := by
  rintro sa sb rfl
  change (ProgramDenotation.set (l.chainSetter x) v sb
      >>= fun q => (Pure.pure (q.1, l.get q.2) : SubProbability (Unit × s)))
    = ProgramDenotation.set x v (l.get sb)
  rw [ProgramDenotation.set_apply', ProgramDenotation.set_apply', SubProbability.pure_bind]
  simp only [Lens.chainSetter, l.set_get]

omit [ProgramSpec] in
/-- A state-blind draw is equivalent to itself. -/
theorem ProgramDenotation.EquivInLens.lift {s t : Type u} {α : Type v} (l : Lens s t)
    (μ : SubProbability α) :
    (μ.toProgramDenotation : ProgramDenotation s α).EquivInLens
      (μ.toProgramDenotation : ProgramDenotation t α) l := by
  rintro sa sb rfl
  change SubProbability.hbind (μ.hbind fun v => (Pure.pure (v, sb) : SubProbability (α × t)))
      (fun q => (Pure.pure (q.1, l.get q.2) : SubProbability (α × s)))
    = μ.hbind fun v => Pure.pure (v, l.get sb)
  rw [SubProbability.hbind_assoc]
  congr 1; funext v
  rw [SubProbability.pure_hbind]

omit [ProgramSpec] in
/-- **Bind congruence** — the `seq` case, and the heart of the path congruences.  Note the
continuation hypothesis is over *wide* states, which is exactly what `EquivInLens` provides. -/
theorem ProgramDenotation.EquivInLens.bind {s t : Type u} {α β : Type v} {l : Lens s t}
    {p : ProgramDenotation s α} {q : ProgramDenotation t α}
    {p' : α → ProgramDenotation s β} {q' : α → ProgramDenotation t β}
    (h : p.EquivInLens q l) (h' : ∀ a, (p' a).EquivInLens (q' a) l) :
    (p >>= p').EquivInLens (q >>= q') l := by
  rintro sa sb rfl
  have hfun : (fun r : α × t =>
        (q' r.1 r.2 >>= fun z => (Pure.pure (z.1, l.get z.2) : SubProbability (β × s))))
      = (fun r : α × t => p' r.1 (l.get r.2)) := funext fun r => h' r.1 _ r.2 rfl
  change ((q sb >>= fun r => q' r.1 r.2)
      >>= fun z => (Pure.pure (z.1, l.get z.2) : SubProbability (β × s)))
    = p (l.get sb) >>= fun r => p' r.1 r.2
  rw [SubProbability.bind_assoc, hfun, ← h _ sb rfl]
  change _ = ((q sb >>= fun z => (Pure.pure (z.1, l.get z.2) : SubProbability (α × s)))
      >>= fun r => p' r.1 r.2)
  rw [SubProbability.bind_assoc]
  congr 1; funext r
  rw [SubProbability.pure_bind]

omit [ProgramSpec] in
/-- Projecting twice is projecting along the composite. -/
theorem SubProbability.mapState_mapState {α : Type v} {s t u : Type w} (f : u → t) (g : t → s)
    (μ : SubProbability (α × u)) :
    (μ.mapState f).mapState g = μ.mapState (fun x => g (f x)) := by
  change ((μ >>= fun q => Pure.pure (q.1, f q.2)) >>= fun q => Pure.pure (q.1, g q.2))
    = μ >>= fun q => Pure.pure (q.1, g (f q.2))
  rw [SubProbability.bind_assoc]
  congr 1; funext q
  rw [SubProbability.pure_bind]

omit [ProgramSpec] in
/-- Equivalences compose: through `l`, then through `m`, is through `m.chain l`. -/
theorem ProgramDenotation.EquivInLens.trans {s t u : Type w} {α : Type v} {l : Lens s t}
    {m : Lens t u} {p : ProgramDenotation s α} {q : ProgramDenotation t α}
    {r : ProgramDenotation u α}
    (h : p.EquivInLens q l) (h' : q.EquivInLens r m) : p.EquivInLens r (m.chain l) := by
  rintro sa su rfl
  change ((r su).mapState (fun x => l.get (m.get x))) = p (l.get (m.get su))
  rw [← SubProbability.mapState_mapState, h' _ su rfl, h _ (m.get su) rfl]

omit [ProgramSpec] in
/-- `mapState` is ω-continuous — what the loop congruence needs. -/
theorem SubProbability.mapState_ωScottContinuous {α : Type v} {s t : Type u} (f : t → s) :
    OmegaCompletePartialOrder.ωScottContinuous
      (fun μ : SubProbability (α × t) => μ.mapState f) := by
  refine OmegaCompletePartialOrder.ωScottContinuous.of_monotone_map_ωSup ⟨?mono, ?sup⟩
  case mono =>
    intro μ₁ μ₂ h
    exact SubProbability.bind_mono (fun μ : SubProbability (α × t) => μ)
      (fun _ q => (Pure.pure (q.1, f q.2) : SubProbability (α × s)))
      (fun _ _ hh => hh) (fun _ _ _ => le_rfl) h
  case sup =>
    intro ch
    exact (SubProbability.bind_ωScottContinuous (fun μ : SubProbability (α × t) => μ)
      (fun _ q => (Pure.pure (q.1, f q.2) : SubProbability (α × s)))
      OmegaCompletePartialOrder.ωScottContinuous.const
      OmegaCompletePartialOrder.ωScottContinuous.id).map_ωSup ch

omit [ProgramSpec] in
/-- Equivalence passes to ω-suprema of chains — the limit step of the loop congruence. -/
theorem ProgramDenotation.EquivInLens.ωSup {s t : Type u} {α : Type v} {l : Lens s t}
    (chP : OmegaCompletePartialOrder.Chain (ProgramDenotation s α))
    (chQ : OmegaCompletePartialOrder.Chain (ProgramDenotation t α))
    (h : ∀ n, (chP n).EquivInLens (chQ n) l) :
    (OmegaCompletePartialOrder.ωSup chP).EquivInLens (OmegaCompletePartialOrder.ωSup chQ) l := by
  rintro sa sb rfl
  have hQ : (OmegaCompletePartialOrder.ωSup chQ) sb = OmegaCompletePartialOrder.ωSup
      (chQ.map ⟨fun m => m sb, fun _ _ hh => Pi.le_def.mp hh sb⟩) := rfl
  have hP : (OmegaCompletePartialOrder.ωSup chP) (l.get sb) = OmegaCompletePartialOrder.ωSup
      (chP.map ⟨fun m => m (l.get sb), fun _ _ hh => Pi.le_def.mp hh (l.get sb)⟩) := rfl
  rw [hQ, hP, (SubProbability.mapState_ωScottContinuous (α := α) l.get).map_ωSup]
  congr 1
  ext n
  exact h n _ sb rfl

omit [ProgramSpec] in
/-- **Loop congruence** (Kleene/ωSup argument again): equivalent conditions and equivalent bodies
give equivalent loops. -/
theorem ProgramDenotation.EquivInLens.while_loop {s t : Type u} {l : Lens s t}
    {cond : ProgramDenotation s Bool} {cond' : ProgramDenotation t Bool}
    {body : ProgramDenotation s Unit} {body' : ProgramDenotation t Unit}
    (hc : cond.EquivInLens cond' l) (hb : body.EquivInLens body' l) :
    (while_loop cond body).EquivInLens (while_loop cond' body') l := by
  let F := while_iteration cond body
  let G := while_iteration cond' body'
  have key : ∀ n : ℕ, ((F^[n] (⊥ : Unit → ProgramDenotation s Unit)) ()).EquivInLens
      ((G^[n] (⊥ : Unit → ProgramDenotation t Unit)) ()) l := by
    intro n
    induction n with
    | zero => exact ProgramDenotation.EquivInLens.bot
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      change (cond >>= fun b => if b = true then body >>= fun _ => (F^[n] ⊥) ()
                else (Pure.pure () : ProgramDenotation s Unit)).EquivInLens
             (cond' >>= fun b => if b = true then body' >>= fun _ => (G^[n] ⊥) ()
                else (Pure.pure () : ProgramDenotation t Unit)) l
      refine ProgramDenotation.EquivInLens.bind hc fun b => ?_
      by_cases h : b = true
      · simp only [h, if_true]
        exact ProgramDenotation.EquivInLens.bind hb fun _ => ih
      · simp only [h, Bool.false_eq_true, if_false]
        exact ProgramDenotation.EquivInLens.pure ()
  let chainF : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation s Unit) :=
    ⟨fun n => F^[n] ⊥, Monotone.monotone_iterate_of_le_map F.monotone (OrderBot.bot_le _)⟩
  let chainG : OmegaCompletePartialOrder.Chain (Unit → ProgramDenotation t Unit) :=
    ⟨fun n => G^[n] ⊥, Monotone.monotone_iterate_of_le_map G.monotone (OrderBot.bot_le _)⟩
  have hF_at : F.lfp () = OmegaCompletePartialOrder.ωSup
      (chainF.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := rfl
  have hG_at : G.lfp () = OmegaCompletePartialOrder.ωSup
      (chainG.map ⟨fun fp => fp (), fun _ _ h => h ()⟩) := rfl
  change (F.lfp ()).EquivInLens (G.lfp ()) l
  rw [hF_at, hG_at]
  exact ProgramDenotation.EquivInLens.ωSup _ _ key

omit [ProgramSpec] in
/-- Every program is equivalent to itself, in the identity lens. -/
theorem ProgramDenotation.EquivInLens.refl {s : Type u} {α : Type v} (p : ProgramDenotation s α) :
    p.EquivInLens p Lens.id := by
  rintro sa sb rfl
  exact SubProbability.bind_pure _

/-! ### The same, at statement level -/

/-- Sequencing. -/
theorem StmtWithHoles.EquivInLens.seq {hCtx : HoleSigs} {l : Lens ProgramState ProgramState}
    {a b a' b' : StmtWithHoles hCtx} (ha : a.EquivInLens a' l) (hb : b.EquivInLens b' l) :
    (a.seq b).EquivInLens (a'.seq b') l := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  exact ProgramDenotation.EquivInLens.bind (ha inst) fun _ => hb inst

/-- Branching; the condition is re-targeted by composing it with the lens. -/
theorem StmtWithHoles.EquivInLens.ifThenElse {hCtx : HoleSigs}
    {l : Lens ProgramState ProgramState} (c : Getter Bool ProgramState)
    {a b a' b' : StmtWithHoles hCtx} (ha : a.EquivInLens a' l) (hb : b.EquivInLens b' l) :
    (StmtWithHoles.ifThenElse c a b).EquivInLens
      (StmtWithHoles.ifThenElse (l.chainGetter c) a' b') l := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  refine ProgramDenotation.EquivInLens.bind (ProgramDenotation.EquivInLens.get l c) fun bv => ?_
  cases bv
  · simpa using hb inst
  · simpa using ha inst

/-- Looping; the condition is re-targeted by composing it with the lens. -/
theorem StmtWithHoles.EquivInLens.while {hCtx : HoleSigs} {l : Lens ProgramState ProgramState}
    (c : Getter Bool ProgramState) {b b' : StmtWithHoles hCtx} (hb : b.EquivInLens b' l) :
    (StmtWithHoles.while c b).EquivInLens (StmtWithHoles.while (l.chainGetter c) b') l := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  exact ProgramDenotation.EquivInLens.while_loop (ProgramDenotation.EquivInLens.get l c) (hb inst)

/-- Statement equivalences compose — how the flattener's passes are stitched together. -/
theorem StmtWithHoles.EquivInLens.trans {hCtx : HoleSigs} {l m : Lens ProgramState ProgramState}
    {a b c : StmtWithHoles hCtx} (h : a.EquivInLens b l) (h' : b.EquivInLens c m) :
    a.EquivInLens c (m.chain l) :=
  fun inst => (h inst).trans (h' inst)

/-- Reflexivity of the renaming-free relation. -/
theorem StmtWithHoles.Equiv.refl {hCtx : HoleSigs} (a : StmtWithHoles hCtx) : a.Equiv a :=
  fun _ => ProgramDenotation.EquivInLens.refl _

/-- Sequencing is associative, denotationally. -/
theorem StmtWithHoles.Equiv.seq_assoc {hCtx : HoleSigs} (a b c : StmtWithHoles hCtx) :
    ((a.seq b).seq c).Equiv (a.seq (b.seq c)) := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation]
  rw [ProgramDenotation.bind_assoc]
  exact ProgramDenotation.EquivInLens.refl _

/-! ## Deterministic statements -/

/-- An assignment, run at a state: a deterministic write. -/
theorem programDenotation_assign_apply {a : Type} (y : Setter a ProgramState)
    (e : Getter a ProgramState) (τ : ProgramState) :
    programDenotation (StmtWithHoles.assign (h := .empty) y e) τ
      = Pure.pure ((), y.set (e.get τ) τ) := by
  simp only [StmtWithHoles.assign, programDenotation]
  rw [ProgramDenotation.bind_apply, ProgramDenotation.get_apply', SubProbability.pure_bind,
    ProgramDenotation.bind_apply]
  change ((Pure.pure (e.get τ) : SubProbability a).hbind fun v => Pure.pure (v, τ))
      >>= (fun p => ProgramDenotation.set y p.1 p.2) = _
  rw [SubProbability.pure_hbind, SubProbability.pure_bind, ProgramDenotation.set_apply']

/-- An assignment is a read followed by a write. -/
theorem programDenotation_assign {a : Type} (y : Setter a ProgramState)
    (e : Getter a ProgramState) :
    programDenotation (StmtWithHoles.assign (h := .empty) y e)
      = ProgramDenotation.get e >>= fun v => ProgramDenotation.set y v := by
  funext τ
  rw [programDenotation_assign_apply, ProgramDenotation.bind_apply,
    ProgramDenotation.get_apply', SubProbability.pure_bind, ProgramDenotation.set_apply']

/-- `skip` is the identity state map. -/
theorem programDenotation_skip_apply (τ : ProgramState) :
    programDenotation (StmtWithHoles.skip (h := .empty)) τ = Pure.pure ((), τ) := by
  simp only [programDenotation, ProgramDenotation.skip]
  rfl

/-- Sequencing is `bind`. -/
theorem programDenotation_seq (a b : Stmt) :
    programDenotation (a.seq b) = programDenotation a >>= fun _ => programDenotation b := by
  simp only [programDenotation]

/-- Two deterministic statements in sequence: their state maps compose. -/
theorem programDenotation_seq_apply_det {a b : Stmt} {fa fb : ProgramState → ProgramState}
    (ha : ∀ τ, programDenotation a τ = Pure.pure ((), fa τ))
    (hb : ∀ τ, programDenotation b τ = Pure.pure ((), fb τ)) :
    ∀ τ, programDenotation (a.seq b) τ = Pure.pure ((), fb (fa τ)) := by
  intro τ
  rw [programDenotation_seq, ProgramDenotation.bind_apply, ha, SubProbability.pure_bind, hb]

/-! ## Placing a hole-free statement into a hole context

A flattened callee body is hole-free, but the statement it is spliced into need not be. -/

/-- Re-type a hole-free statement in any hole context.  (`hole` cannot occur: `HoleIndex .empty`
is uninhabited.) -/
def StmtWithHoles.weaken {h : HoleSigs} : Stmt → StmtWithHoles h
  | .skip                   => .skip
  | .sample x e             => .sample x e
  | .call' x ns hl hn b r p => .call' x ns hl hn b r p
  | .seq s₁ s₂              => .seq (weaken s₁) (weaken s₂)
  | .ifThenElse c t e       => .ifThenElse c (weaken t) (weaken e)
  | .while c b              => .while c (weaken b)
  termination_by s => s.depth
  decreasing_by all_goals simp only [StmtWithHoles.depth]; omega

/-- Weakening is undone by instantiation: a hole-free statement has nothing to fill in. -/
theorem StmtWithHoles.weaken_instantiate {h : HoleSigs} (inst : h.Instantiation) :
    ∀ s : Stmt, (StmtWithHoles.weaken (h := h) s).instantiate inst = s
  | .skip                   => by simp only [StmtWithHoles.weaken, StmtWithHoles.instantiate]
  | .sample _ _             => by simp only [StmtWithHoles.weaken, StmtWithHoles.instantiate]
  | .call' _ _ _ _ _ _ _    => by simp only [StmtWithHoles.weaken, StmtWithHoles.instantiate]
  | .seq s₁ s₂              => by
      simp only [StmtWithHoles.weaken, StmtWithHoles.instantiate,
        weaken_instantiate inst s₁, weaken_instantiate inst s₂]
  | .ifThenElse _ t e       => by
      simp only [StmtWithHoles.weaken, StmtWithHoles.instantiate,
        weaken_instantiate inst t, weaken_instantiate inst e]
  | .while _ b              => by
      simp only [StmtWithHoles.weaken, StmtWithHoles.instantiate, weaken_instantiate inst b]
  termination_by s => s.depth
  decreasing_by all_goals simp only [StmtWithHoles.depth]; omega

/-! ## Flattening one call

The one step with real content.  Everything else above is congruence and transport. -/

/-- A `call` statement, run at a state: run the callee's body on fresh locals holding the
arguments, then store its return value. -/
theorem programDenotation_call'_apply {sig : ProcedureSignature}
    (x : Setter sig.ret ProgramState) (names : List String)
    (hlen : names.length = sig.params.length) (hnodup : names.Nodup) (b : Stmt)
    (r : Getter sig.ret ProgramState) (args : Getter sig.ParamType ProgramState)
    (s : ProgramState) :
    programDenotation (StmtWithHoles.call' (h := .empty) x names hlen hnodup b r args) s
      = programDenotation b ⟨s.globals, VariableAssignment.setParams names sig.params hlen
            (args.get s) VariableAssignment.init⟩
          >>= fun z => Pure.pure ((), x.set (r.get z.2)
                (ProgramState.globalL.set z.2.globals s)) := by
  rw [programDenotation_call', ProgramDenotation.bind_apply, ProgramDenotation.get_apply',
    SubProbability.pure_bind, ProgramDenotation.bind_apply]
  change (((programDenotation b ⟨s.globals, VariableAssignment.setParams names sig.params hlen
        (args.get s) VariableAssignment.init⟩).hbind
        fun p => Pure.pure (r.get p.2, p.2.globals)).hbind
      fun w => Pure.pure (w.1, ProgramState.globalL.set w.2 s))
      >>= (fun q => ProgramDenotation.set x q.1 q.2) = _
  rw [SubProbability.hbind_assoc, SubProbability.hbind_bind]
  congr 1; funext z
  rw [SubProbability.pure_hbind, SubProbability.pure_bind, ProgramDenotation.set_apply']

/-- The expansion of a call, run at a state: after the prelude `f`, the callee's body runs in
`emb`, and its return value is stored through the caller's setter. -/
theorem flattenedCall_apply {sig : ProcedureSignature} (trafo emb : Lens ProgramState ProgramState)
    (heg : emb.chain ProgramState.globalL = ProgramState.globalL)
    (x : Setter sig.ret ProgramState) (b : Stmt) (r : Getter sig.ret ProgramState)
    (f : ProgramState → ProgramState) (τ : ProgramState) :
    ((fun σ => Pure.pure ((), f σ)) >>= fun _ =>
        programDenotation (b.applyLens emb) >>= fun _ =>
          ProgramDenotation.get (emb.chainGetter r) >>= fun v =>
            ProgramDenotation.set (trafo.chainSetter x) v) τ
      = programDenotation b (emb.get (f τ)) >>= fun w =>
          Pure.pure ((), trafo.set (x.set (r.get w.2) (trafo.get (emb.set w.2 (f τ))))
            (emb.set w.2 (f τ))) := by
  rw [ProgramDenotation.bind_apply, SubProbability.pure_bind, ProgramDenotation.bind_apply,
    programDenotation_applyLens emb heg b]
  change ((programDenotation b (emb.get (f τ))).hbind fun w => Pure.pure (w.1, emb.set w.2 (f τ)))
      >>= _ = _
  rw [SubProbability.hbind_bind]
  congr 1; funext w
  rw [SubProbability.pure_bind, ProgramDenotation.bind_apply, ProgramDenotation.get_apply',
    SubProbability.pure_bind, ProgramDenotation.set_apply']
  simp only [Lens.chainGetter, Lens.chainSetter, emb.set_get]

/-- **Flattening a call is sound.**  A `call` is denotationally equivalent, along `trafo`, to

* a *prelude* `f` that puts the callee's entry locals into the callee's frame of the wide state
  (`hpre_get`) without disturbing anything visible through `trafo` (`hpre_vis`);
* the callee's body, re-targeted with `applyLens emb`;
* a store of the callee's return value through the caller's setter.

The two lenses must preserve the globals (`htg`, `heg`), and writing the callee's frame must be
invisible through `trafo` except for the globals (`hdisj`). -/
theorem equivInLens_flattenCall {sig : ProcedureSignature}
    (trafo emb : Lens ProgramState ProgramState)
    (htg : trafo.chain ProgramState.globalL = ProgramState.globalL)
    (heg : emb.chain ProgramState.globalL = ProgramState.globalL)
    (hdisj : ∀ v τ, trafo.get (emb.set v τ)
      = ProgramState.globalL.set v.globals (trafo.get τ))
    (x : Setter sig.ret ProgramState) (names : List String)
    (hlen : names.length = sig.params.length) (hnodup : names.Nodup)
    (args : Getter sig.ParamType ProgramState) (b : Stmt) (r : Getter sig.ret ProgramState)
    (f : ProgramState → ProgramState)
    (hpre_get : ∀ τ, emb.get (f τ) = ⟨τ.globals, VariableAssignment.setParams names sig.params
      hlen (args.get (trafo.get τ)) VariableAssignment.init⟩)
    (hpre_vis : ∀ τ, trafo.get (f τ) = trafo.get τ) :
    (programDenotation (StmtWithHoles.call' (h := .empty) x names hlen hnodup b r args)).EquivInLens
      ((fun σ => Pure.pure ((), f σ)) >>= fun _ =>
        programDenotation (b.applyLens emb) >>= fun _ =>
          ProgramDenotation.get (emb.chainGetter r) >>= fun v =>
            ProgramDenotation.set (trafo.chainSetter x) v) trafo := by
  rintro sa τ rfl
  have hglob : (trafo.get τ).globals = τ.globals :=
    congrArg (fun L : Lens State ProgramState => L.get τ) htg
  rw [programDenotation_call'_apply, SubProbability.mapState_eq,
    flattenedCall_apply trafo emb heg x b r f τ, SubProbability.bind_assoc, hpre_get, hglob]
  congr 1; funext w
  rw [SubProbability.pure_bind, trafo.set_get, hdisj, hpre_vis]

/-- The statement-level form, for any prelude `pre` that is the deterministic state map `f`. -/
theorem StmtWithHoles.equivInLens_flattenCall {hCtx : HoleSigs} {sig : ProcedureSignature}
    (trafo emb : Lens ProgramState ProgramState)
    (htg : trafo.chain ProgramState.globalL = ProgramState.globalL)
    (heg : emb.chain ProgramState.globalL = ProgramState.globalL)
    (hdisj : ∀ v τ, trafo.get (emb.set v τ)
      = ProgramState.globalL.set v.globals (trafo.get τ))
    (x : Setter sig.ret ProgramState) (names : List String)
    (hlen : names.length = sig.params.length) (hnodup : names.Nodup)
    (args : Getter sig.ParamType ProgramState) (b : Stmt) (r : Getter sig.ret ProgramState)
    (pre : StmtWithHoles hCtx) (f : ProgramState → ProgramState)
    (hpre : ∀ inst τ, programDenotation (pre.instantiate inst) τ = Pure.pure ((), f τ))
    (hpre_get : ∀ τ, emb.get (f τ) = ⟨τ.globals, VariableAssignment.setParams names sig.params
      hlen (args.get (trafo.get τ)) VariableAssignment.init⟩)
    (hpre_vis : ∀ τ, trafo.get (f τ) = trafo.get τ) :
    (StmtWithHoles.call' (h := hCtx) x names hlen hnodup b r args).EquivInLens
      (pre.seq ((StmtWithHoles.weaken (b.applyLens emb)).seq
        (StmtWithHoles.assign (trafo.chainSetter x) (emb.chainGetter r)))) trafo := by
  intro inst
  have hpre' : programDenotation (pre.instantiate inst) = fun σ => Pure.pure ((), f σ) :=
    funext (hpre inst)
  simp only [StmtWithHoles.instantiate, StmtWithHoles.weaken_instantiate, StmtWithHoles.assign]
  rw [programDenotation_seq, programDenotation_seq, ← StmtWithHoles.assign,
    programDenotation_assign, hpre']
  exact _root_.GaudisCrypt.equivInLens_flattenCall
    trafo emb htg heg hdisj x names hlen hnodup args b r f hpre_get hpre_vis

namespace Flatten

/-- `P` writes an argument tuple into the parameter slots `names` of the callee's frame `emb`:
the wide-state form of `VariableAssignment.setParams`.  The meta code builds `P` as the tuple
of the parameters' renamed variables, which is how it prints. -/
def IsParamWriter (emb : Lens ProgramState ProgramState) (names : List String) (tys : List Type)
    (hlen : names.length = tys.length) (P : Setter (typeListToTuple tys) ProgramState) : Prop :=
  ∀ a σ, P.set a σ = emb.set (ProgramState.localL.set
    (VariableAssignment.setParams names tys hlen a (emb.get σ).locals) (emb.get σ)) σ

/-- No parameters: nothing to write. -/
theorem isParamWriter_nil (emb : Lens ProgramState ProgramState)
    (hlen : ([] : List String).length = ([] : List Type).length) :
    IsParamWriter emb [] [] hlen Setter.throwaway := fun _ σ => by
  change σ = emb.set (ProgramState.localL.set (emb.get σ).locals (emb.get σ)) σ
  rw [show ProgramState.localL.set (emb.get σ).locals (emb.get σ) = emb.get σ from
    ProgramState.localL.get_set _, emb.get_set]

/-- One parameter: its variable, seen through `emb`. -/
theorem isParamWriter_single (emb : Lens ProgramState ProgramState) (n : String) (T : Type)
    (i : Nonempty T) (k : Nat) (hk : k = VariableName.encode n)
    (hlen : [n].length = [T].length) (L : Lens T ProgramState)
    (hL : emb.chain (varLens (@VariableName.mk n T i k hk)).intoLocal = L) :
    IsParamWriter emb [n] [T] hlen L.toSetter := by
  subst hL hk
  intro a σ
  rfl

/-- Two or more parameters: the first one's variable, paired with the rest. -/
theorem isParamWriter_cons (emb : Lens ProgramState ProgramState) (n n' : String)
    (ns : List String) (T T' : Type) (Ts : List Type) (i : Nonempty T) (k : Nat)
    (hk : k = VariableName.encode n) (hlen : (n :: n' :: ns).length = (T :: T' :: Ts).length)
    (hlen' : (n' :: ns).length = (T' :: Ts).length)
    (L₁ : Lens T ProgramState) (L₂ : Lens (typeListToTuple (T' :: Ts)) ProgramState)
    (hL₁ : emb.chain (varLens (@VariableName.mk n T i k hk)).intoLocal = L₁)
    [hd : Lens.Disjoint L₁ L₂] (hrest : IsParamWriter emb (n' :: ns) (T' :: Ts) hlen' L₂.toSetter) :
    IsParamWriter emb (n :: n' :: ns) (T :: T' :: Ts) hlen (Lens.pair L₁ L₂).toSetter := by
  rintro ⟨a, as⟩ σ
  change L₁.set a (L₂.set as σ) = _
  rw [hd.commute, hrest as]
  subst hL₁ hk
  have hc : ∀ (M : Lens T ProgramState) τ,
      (emb.chain M).set a τ = emb.set (M.set a (emb.get τ)) τ := fun _ _ => rfl
  rw [hc, emb.set_get, emb.set_set]
  rfl

/-- **Flattening a call**, as the meta code instantiates it: the call is equivalent, along
`trafo`, to resetting the callee's frame, writing the arguments with `P`, the callee's body in
`emb`, and the store of its return value.  Every side condition of the general
`StmtWithHoles.equivInLens_flattenCall` is discharged here, once.

`P`'s content type is spelled `typeListToTuple sig.params`, not `sig.ParamType`: the two are
equal by definition, but only the former reduces at the transparency `simp` matches at, and the
cleaning lemmas have to see the parameters' types inside `P` when a later round renames them. -/
theorem equivInLens_call {hCtx : HoleSigs} {sig : ProcedureSignature}
    (x : Setter sig.ret ProgramState) (names : List String)
    (hlen : names.length = sig.params.length) (hnodup : names.Nodup) (b : Stmt)
    (r : Getter sig.ret ProgramState) (args : Getter sig.ParamType ProgramState)
    (P : Setter (typeListToTuple sig.params) ProgramState)
    (hP : IsParamWriter emb names sig.params hlen P) :
    (StmtWithHoles.call' (h := hCtx) x names hlen hnodup b r args).EquivInLens
      -- the binder is named: an anonymous one is `x✝`, which the printer takes for an `x`
      ((StmtWithHoles.assign (emb.chainSetter (resetSetter Set.univ)) ⟨fun _st => ()⟩).seq
        ((StmtWithHoles.assign (a := typeListToTuple sig.params) P (trafo.chainGetter args)).seq
          ((StmtWithHoles.weaken (b.applyLens emb)).seq
            (StmtWithHoles.assign (trafo.chainSetter x) (emb.chainGetter r)))))
      trafo := by
  -- the frame after the reset, and after the arguments are written
  let σ₁ : ProgramState → ProgramState := fun τ =>
    (emb.chainSetter (resetSetter Set.univ)).set () τ
  let f : ProgramState → ProgramState := fun τ => P.set (args.get (trafo.get (σ₁ τ))) (σ₁ τ)
  have hvis₁ : ∀ τ, trafo.get (σ₁ τ) = trafo.get τ := fun τ => by
    simp only [σ₁, emb_chainSetter_resetSetter_univ_set, trafo_get_emb_set]
    rfl
  have hemb₁ : ∀ τ, emb.get (σ₁ τ) = ⟨τ.globals, VariableAssignment.init⟩ := fun τ => by
    simp only [σ₁, emb_chainSetter_resetSetter_univ_set, emb.set_get]
  have hpre := StmtWithHoles.equivInLens_flattenCall (hCtx := hCtx) trafo emb
    trafo_chain_globalL emb_chain_globalL trafo_get_emb_set x names hlen hnodup
    args b r ((StmtWithHoles.assign (emb.chainSetter (resetSetter Set.univ)) ⟨fun _st => ()⟩).seq
      (StmtWithHoles.assign P (trafo.chainGetter args))) f
    (fun _ τ => programDenotation_seq_apply_det (programDenotation_assign_apply _ _)
      (programDenotation_assign_apply _ _) τ)
  have h := StmtWithHoles.EquivInLens.trans (hpre (fun τ => ?_) (fun τ => ?_))
    (StmtWithHoles.Equiv.seq_assoc _ _ _)
  · rwa [Lens.id_chain] at h
  · simp only [f, hvis₁]
    rw [hP, emb.set_get, hemb₁]
    rfl
  · simp only [f, hvis₁]
    rw [hP, trafo_get_emb_set, hvis₁]
    change ProgramState.globalL.set (emb.get (σ₁ τ)).globals _ = _
    rw [hemb₁]
    rfl

end Flatten

/-! ## What `flattenSeq` rewrites with

(And `StmtWithHoles.Equiv.seq_assoc`, above.) -/

/-- A leading `skip` can be dropped. -/
theorem StmtWithHoles.Equiv.skip_seq {hCtx : HoleSigs} (a : StmtWithHoles hCtx) :
    ((StmtWithHoles.skip).seq a).Equiv a := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation, ProgramDenotation.skip]
  rw [ProgramDenotation.pure_bind]
  exact ProgramDenotation.EquivInLens.refl _

/-- A trailing `skip` can be dropped. -/
theorem StmtWithHoles.Equiv.seq_skip {hCtx : HoleSigs} (a : StmtWithHoles hCtx) :
    (a.seq (StmtWithHoles.skip)).Equiv a := by
  intro inst
  simp only [StmtWithHoles.instantiate, programDenotation, ProgramDenotation.skip]
  rw [ProgramDenotation.bind_pure]
  exact ProgramDenotation.EquivInLens.refl _

/-- An assignment to `_` does nothing. -/
theorem programDenotation_assign_throwaway {a : Type} (e : Getter a ProgramState) :
    programDenotation (StmtWithHoles.assign (h := .empty) Setter.throwaway e)
      = ProgramDenotation.skip := by
  funext τ
  rw [programDenotation_assign_apply]
  rfl

/-- A leading assignment to `_` can be dropped (a call with no parameters writes its argument
`()` to `_`). -/
theorem StmtWithHoles.Equiv.throwaway_seq {hCtx : HoleSigs} {α : Type} (e : Getter α ProgramState)
    (a : StmtWithHoles hCtx) :
    ((StmtWithHoles.assign Setter.throwaway e).seq a).Equiv a := by
  intro inst
  change (programDenotation ((StmtWithHoles.assign (h := .empty) Setter.throwaway e).seq
    (a.instantiate inst))).EquivInLens _ _
  rw [programDenotation_seq, programDenotation_assign_throwaway, ProgramDenotation.skip,
    ProgramDenotation.pure_bind]
  exact ProgramDenotation.EquivInLens.refl _

/-- A trailing assignment to `_` can be dropped (a call whose result is discarded stores it to
`_`). -/
theorem StmtWithHoles.Equiv.seq_throwaway {hCtx : HoleSigs} {α : Type}
    (a : StmtWithHoles hCtx) (e : Getter α ProgramState) :
    (a.seq (StmtWithHoles.assign Setter.throwaway e)).Equiv a := by
  intro inst
  change (programDenotation ((a.instantiate inst).seq
    (StmtWithHoles.assign (h := .empty) Setter.throwaway e))).EquivInLens _ _
  rw [programDenotation_seq, programDenotation_assign_throwaway, ProgramDenotation.skip,
    ProgramDenotation.bind_pure]
  exact ProgramDenotation.EquivInLens.refl _

/-- Branching, at the identity lens. -/
theorem StmtWithHoles.Equiv.ifThenElse {hCtx : HoleSigs} (c : Getter Bool ProgramState)
    {a b a' b' : StmtWithHoles hCtx} (ha : a.Equiv a') (hb : b.Equiv b') :
    (StmtWithHoles.ifThenElse c a b).Equiv (StmtWithHoles.ifThenElse c a' b') :=
  StmtWithHoles.EquivInLens.ifThenElse c ha hb

/-- Looping, at the identity lens. -/
theorem StmtWithHoles.Equiv.while {hCtx : HoleSigs} (c : Getter Bool ProgramState)
    {b b' : StmtWithHoles hCtx} (hb : b.Equiv b') :
    (StmtWithHoles.while c b).Equiv (StmtWithHoles.while c b') :=
  StmtWithHoles.EquivInLens.while c hb

/-- Transitivity, at the identity lens (`Lens.id.chain Lens.id` is `Lens.id`). -/
theorem StmtWithHoles.Equiv.trans {hCtx : HoleSigs} {a b c : StmtWithHoles hCtx}
    (h : a.Equiv b) (h' : b.Equiv c) : a.Equiv c :=
  StmtWithHoles.EquivInLens.trans h h'

/-! ## The procedure level

What turns the statement-level result into a fact about `procedureDenotation`, and therefore
into something usable where the procedure is called. -/

namespace Flatten

/-- `l` leaves the entry state of a procedure with parameters `names : tys` alone: the arguments
in their slots, `init` everywhere else. -/
def FixesEntry (names : List String) (tys : List Type) (hlen : names.length = tys.length)
    (l : Lens ProgramState ProgramState) : Prop :=
  ∀ (st : State) (args : typeListToTuple tys),
    l.get ⟨st, VariableAssignment.setParams names tys hlen args VariableAssignment.init⟩
      = ⟨st, VariableAssignment.setParams names tys hlen args VariableAssignment.init⟩

theorem fixesEntry_trafo (names : List String) (tys : List Type)
    (hlen : names.length = tys.length) (hfix : ∀ n ∈ names, escape n = n) :
    FixesEntry names tys hlen trafo :=
  fun st args => ProgramState.mapLocal_embed_get_entry _ _ names tys hlen hfix args st

theorem fixesEntry_rename (ren : List (String × String)) (names : List String)
    (tys : List Type) (hlen : names.length = tys.length)
    (hfix : ∀ n ∈ names, renameName ren n = n) :
    FixesEntry names tys hlen (rename ren) :=
  fun st args => ProgramState.mapLocal_embed_get_entry _ _ names tys hlen hfix args st

/-- Two renamings that keep the globals compose to one that keeps them. -/
theorem chain_chain_globalL {l m : Lens ProgramState ProgramState}
    (hl : l.chain ProgramState.globalL = ProgramState.globalL)
    (hm : m.chain ProgramState.globalL = ProgramState.globalL) :
    (m.chain l).chain ProgramState.globalL = ProgramState.globalL := by
  rw [Lens.chain_assoc, hl, hm]

theorem FixesEntry.chain {names : List String} {tys : List Type}
    {hlen : names.length = tys.length} {l m : Lens ProgramState ProgramState}
    (hl : FixesEntry names tys hlen l) (hm : FixesEntry names tys hlen m) :
    FixesEntry names tys hlen (m.chain l) := fun st args => by
  change l.get (m.get _) = _
  rw [hm, hl]

/-- **The procedure-level statement**: flattening the body of a procedure does not change what it
computes, given that the renaming leaves the entry state and the globals alone. -/
theorem procedureDenotation_congr {sig : ProcedureSignature} (names : List String)
    (hlen : names.length = sig.params.length) (hnodup : names.Nodup)
    (l : Lens ProgramState ProgramState) (b b' : Stmt) (r : Getter sig.ret ProgramState)
    (hb : b.EquivInLens b' l) (hinit : FixesEntry names sig.params hlen l)
    (hglobL : l.chain ProgramState.globalL = ProgramState.globalL) :
    procedureDenotation (⟨names, hlen, hnodup, b', l.chainGetter r⟩ : Procedure sig)
      = procedureDenotation (⟨names, hlen, hnodup, b, r⟩ : Procedure sig) := by
  have hglob : ∀ τ, (l.get τ).globals = τ.globals := fun τ =>
    congrArg (fun L : Lens State ProgramState => L.get τ) hglobL
  funext argv st
  let τ : ProgramState :=
    ⟨st, VariableAssignment.setParams names sig.params hlen argv VariableAssignment.init⟩
  have h := hb ⟨⟩ (l.get τ) τ rfl
  rw [StmtWithHoles.instantiate_empty, StmtWithHoles.instantiate_empty, hinit] at h
  change (programDenotation b' τ).hbind (fun p => Pure.pure (r.get (l.get p.2), p.2.globals))
    = (programDenotation b τ).hbind (fun p => Pure.pure (r.get p.2, p.2.globals))
  rw [← h, SubProbability.mapState_eq, SubProbability.bind_hbind]
  congr 1; funext p
  rw [SubProbability.pure_hbind, hglob]

end Flatten

/-! ## The lemmas `cleanStmt` rewrites with

The closed set.  `Flatten.cleanLemmas` lists exactly these names and nothing else; the cleaning
pass runs `simp only` with that list, the name evaluation of `Flatten.reduceNames` and
`VariableName.reduceEncode`, no default simp set and `zeta := false`, so statement `let`s survive.

Three groups: through the statement wrappers (`applyLens`, `weaken`), into l-values, and into
expressions.  Everything that does not match keeps its wrapper — that costs prettiness, never
correctness. -/

section Clean

/-! ### Through the statement wrappers -/

@[simp] theorem StmtWithHoles.applyLens_skip {h : HoleSigs} (l : Lens ProgramState ProgramState) :
    (StmtWithHoles.skip (h := h)).applyLens l = StmtWithHoles.skip := rfl

@[simp] theorem StmtWithHoles.applyLens_sample {h : HoleSigs} {A : Type}
    (l : Lens ProgramState ProgramState) (x : Setter A ProgramState)
    (e : Getter (SubProbability A) ProgramState) :
    (StmtWithHoles.sample (h := h) x e).applyLens l
      = StmtWithHoles.sample (l.chainSetter x) (l.chainGetter e) := rfl

@[simp] theorem StmtWithHoles.applyLens_assign {h : HoleSigs} {A : Type}
    (l : Lens ProgramState ProgramState) (x : Setter A ProgramState) (e : Getter A ProgramState) :
    (StmtWithHoles.assign (h := h) x e).applyLens l
      = StmtWithHoles.assign (l.chainSetter x) (l.chainGetter e) := rfl


@[simp] theorem StmtWithHoles.applyLens_call' {h : HoleSigs} {sig : ProcedureSignature}
    (l : Lens ProgramState ProgramState) (x : Setter sig.ret ProgramState) (ns : List String)
    (hl : ns.length = sig.params.length) (hn : ns.Nodup) (b : Stmt)
    (r : Getter sig.ret ProgramState) (p : Getter sig.ParamType ProgramState) :
    (StmtWithHoles.call' (h := h) x ns hl hn b r p).applyLens l
      = StmtWithHoles.call' (l.chainSetter x) ns hl hn b r (l.chainGetter p) := rfl

@[simp] theorem StmtWithHoles.applyLens_call {h : HoleSigs} {sig : ProcedureSignature}
    (l : Lens ProgramState ProgramState) (x : Setter sig.ret ProgramState) (p : Procedure sig)
    (args : Getter sig.ParamType ProgramState) :
    (StmtWithHoles.call (h := h) x p args).applyLens l
      = StmtWithHoles.call (l.chainSetter x) p (l.chainGetter args) := rfl

@[simp] theorem StmtWithHoles.applyLens_hole {h : HoleSigs} {sig : ProcedureSignature}
    (l : Lens ProgramState ProgramState) (n : HoleIndex h sig) (x : Setter sig.ret ProgramState)
    (p : Getter sig.ParamType ProgramState) :
    (StmtWithHoles.hole n x p).applyLens l
      = StmtWithHoles.hole n (l.chainSetter x) (l.chainGetter p) := rfl

@[simp] theorem StmtWithHoles.applyLens_seq {h : HoleSigs} (l : Lens ProgramState ProgramState)
    (s₁ s₂ : StmtWithHoles h) : (s₁.seq s₂).applyLens l = (s₁.applyLens l).seq (s₂.applyLens l) :=
  rfl

@[simp] theorem StmtWithHoles.applyLens_ifThenElse {h : HoleSigs}
    (l : Lens ProgramState ProgramState) (c : Getter Bool ProgramState) (t e : StmtWithHoles h) :
    (StmtWithHoles.ifThenElse c t e).applyLens l
      = StmtWithHoles.ifThenElse (l.chainGetter c) (t.applyLens l) (e.applyLens l) := rfl

@[simp] theorem StmtWithHoles.applyLens_while {h : HoleSigs} (l : Lens ProgramState ProgramState)
    (c : Getter Bool ProgramState) (b : StmtWithHoles h) :
    (StmtWithHoles.while c b).applyLens l
      = StmtWithHoles.while (l.chainGetter c) (b.applyLens l) := rfl

/-- Two nested re-targetings collapse into one — what a second flattening round leaves behind. -/
@[simp] theorem StmtWithHoles.applyLens_applyLens {h : HoleSigs}
    (l m : Lens ProgramState ProgramState) :
    ∀ s : StmtWithHoles h, (s.applyLens l).applyLens m = s.applyLens (m.chain l)
  | .skip                   => rfl
  | .sample _ _             => rfl
  | .call' _ _ _ _ _ _ _    => rfl
  | .hole _ _ _             => rfl
  | .seq s₁ s₂              => by
      simp only [StmtWithHoles.applyLens, applyLens_applyLens l m s₁, applyLens_applyLens l m s₂]
  | .ifThenElse _ t e       => by
      simp only [StmtWithHoles.applyLens, applyLens_applyLens l m t, applyLens_applyLens l m e]
      rfl
  | .while _ b              => by
      simp only [StmtWithHoles.applyLens, applyLens_applyLens l m b]
      rfl

@[simp] theorem StmtWithHoles.weaken_skip {h : HoleSigs} :
    StmtWithHoles.weaken (h := h) StmtWithHoles.skip = StmtWithHoles.skip := by
  simp only [StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_sample {h : HoleSigs} {A : Type} (x : Setter A ProgramState)
    (e : Getter (SubProbability A) ProgramState) :
    StmtWithHoles.weaken (h := h) (StmtWithHoles.sample x e) = StmtWithHoles.sample x e := by
  simp only [StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_assign {h : HoleSigs} {A : Type} (x : Setter A ProgramState)
    (e : Getter A ProgramState) :
    StmtWithHoles.weaken (h := h) (StmtWithHoles.assign x e) = StmtWithHoles.assign x e := by
  simp only [StmtWithHoles.assign, StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_call' {h : HoleSigs} {sig : ProcedureSignature}
    (x : Setter sig.ret ProgramState) (ns : List String) (hl : ns.length = sig.params.length)
    (hn : ns.Nodup) (b : Stmt) (r : Getter sig.ret ProgramState)
    (p : Getter sig.ParamType ProgramState) :
    StmtWithHoles.weaken (h := h) (StmtWithHoles.call' x ns hl hn b r p)
      = StmtWithHoles.call' x ns hl hn b r p := by
  simp only [StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_call {h : HoleSigs} {sig : ProcedureSignature}
    (x : Setter sig.ret ProgramState) (p : Procedure sig)
    (args : Getter sig.ParamType ProgramState) :
    StmtWithHoles.weaken (h := h) (StmtWithHoles.call x p args) = StmtWithHoles.call x p args := by
  simp only [StmtWithHoles.call, StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_seq {h : HoleSigs} (s₁ s₂ : Stmt) :
    StmtWithHoles.weaken (h := h) (s₁.seq s₂)
      = (StmtWithHoles.weaken s₁).seq (StmtWithHoles.weaken s₂) := by
  simp only [StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_ifThenElse {h : HoleSigs} (c : Getter Bool ProgramState)
    (t e : Stmt) :
    StmtWithHoles.weaken (h := h) (StmtWithHoles.ifThenElse c t e)
      = StmtWithHoles.ifThenElse c (StmtWithHoles.weaken t) (StmtWithHoles.weaken e) := by
  simp only [StmtWithHoles.weaken]

@[simp] theorem StmtWithHoles.weaken_while {h : HoleSigs} (c : Getter Bool ProgramState)
    (b : Stmt) :
    StmtWithHoles.weaken (h := h) (StmtWithHoles.while c b)
      = StmtWithHoles.while c (StmtWithHoles.weaken b) := by
  simp only [StmtWithHoles.weaken]

/-- Weakening and re-targeting commute, so the two wrappers can be pushed inwards together. -/
@[simp] theorem StmtWithHoles.weaken_applyLens {h : HoleSigs} (l : Lens ProgramState ProgramState) :
    ∀ s : Stmt, StmtWithHoles.weaken (h := h) (s.applyLens l)
      = (StmtWithHoles.weaken (h := h) s).applyLens l
  | .skip                   => by simp only [StmtWithHoles.applyLens, StmtWithHoles.weaken]
  | .sample _ _             => by simp only [StmtWithHoles.applyLens, StmtWithHoles.weaken]
  | .call' _ _ _ _ _ _ _    => by simp only [StmtWithHoles.applyLens, StmtWithHoles.weaken]
  | .seq s₁ s₂              => by
      simp only [StmtWithHoles.applyLens, StmtWithHoles.weaken,
        weaken_applyLens l s₁, weaken_applyLens l s₂]
  | .ifThenElse _ t e       => by
      simp only [StmtWithHoles.applyLens, StmtWithHoles.weaken,
        weaken_applyLens l t, weaken_applyLens l e]
  | .while _ b              => by
      simp only [StmtWithHoles.applyLens, StmtWithHoles.weaken, weaken_applyLens l b]
  termination_by s => s.depth
  decreasing_by all_goals simp only [StmtWithHoles.depth]; omega

/-! ### Into l-values -/

/-- A variable used as an l-value travels along the lens. -/
@[simp] theorem Lens.chainSetter_liftLens {A : Type} (l : Lens ProgramState ProgramState)
    (x : Lens A ProgramState) : l.chainSetter (liftLens x) = liftLens (l.chain x) := rfl

/-- A *global* l-value is unaffected by a renaming of the locals. -/
@[simp] theorem Lens.chainSetter_liftLens_global {A : Type}
    (m : Lens VariableAssignment VariableAssignment) (g : Lens A State) :
    (ProgramState.mapLocal m).chainSetter (liftLens g) = liftLens g := by
  ext v τ
  change (⟨g.set v τ.globals, m.set (m.get τ.locals) τ.locals⟩ : ProgramState)
    = ⟨g.set v τ.globals, τ.locals⟩
  rw [m.get_set]

omit [ProgramSpec] in
/-- A discarded result stays discarded, so a void call does not acquire an l-value. -/
@[simp] theorem Lens.chainSetter_throwaway {A : Type} {s t : Type u} (l : Lens s t) :
    l.chainSetter (Setter.throwaway (a := A)) = Setter.throwaway := by
  ext v τ; exact l.get_set τ

omit [ProgramSpec] in
/-- A lens used as an l-value composes as a lens. -/
@[simp] theorem Lens.chainSetter_toSetter {a : Type u} {s : Type v} {t : Type w} (l : Lens s t)
    (x : Lens a s) : l.chainSetter (Lens.toSetter x) = Lens.toSetter (l.chain x) := rfl

omit [ProgramSpec] in
@[simp] theorem Lens.chainSetter_chainSetter {a : Type u} {s t u' : Type v} (m : Lens t u')
    (l : Lens s t) (x : Setter a s) : m.chainSetter (l.chainSetter x) = (m.chain l).chainSetter x :=
  rfl

omit [ProgramSpec] in
@[simp] theorem Lens.chainGetter_chainGetter {a : Type u} {s t u' : Type v} (m : Lens t u')
    (l : Lens s t) (g : Getter a s) : m.chainGetter (l.chainGetter g) = (m.chain l).chainGetter g :=
  rfl

omit [ProgramSpec] in
/-- A lens read as an expression composes as a lens. -/
@[simp] theorem Lens.chainGetter_toGetter {a : Type u} {s : Type v} {t : Type w} (l : Lens s t)
    (x : Lens a s) : l.chainGetter (Lens.toGetter x) = Lens.toGetter (l.chain x) := rfl

/-! ### Into expressions

A `GaudiExpr` getter is `Getter.mk (fun st => body)` with every variable read spelled
`eval x` at the current state `⟨st⟩`.  Composing it with a lens beta-reduces to the same body at
`l.get st`, and these lemmas move the lens from the *state* to the *variable* — after which the
variable lemmas rename it, and the read prints as `§x` again. -/

@[simp] theorem eval_chain_lens {A : Type} (l : Lens ProgramState ProgramState) (τ : ProgramState)
    (x : Lens A ProgramState) :
    (eval (cs := ⟨l.get τ⟩) x : A) = eval (cs := ⟨τ⟩) (l.chain x) := rfl

@[simp] theorem eval_chain_getter {A : Type} (l : Lens ProgramState ProgramState)
    (τ : ProgramState) (x : Getter A ProgramState) :
    (eval (cs := ⟨l.get τ⟩) x : A) = eval (cs := ⟨τ⟩) (l.chainGetter x) := rfl

@[simp] theorem eval_mapLocal_global_lens {A : Type}
    (m : Lens VariableAssignment VariableAssignment) (τ : ProgramState) (g : Lens A State) :
    (eval (cs := ⟨(ProgramState.mapLocal m).get τ⟩) g : A) = eval (cs := ⟨τ⟩) g := rfl

@[simp] theorem eval_mapLocal_global_getter {A : Type}
    (m : Lens VariableAssignment VariableAssignment) (τ : ProgramState) (g : Getter A State) :
    (eval (cs := ⟨(ProgramState.mapLocal m).get τ⟩) g : A) = eval (cs := ⟨τ⟩) g := rfl

/-! ### The three renamings, unfolded where the lemmas above need `mapLocal`

`trafo`, `emb` and `rename ren` are definitions (so that they print by name), and `simp` does not
see the `mapLocal` inside; each gets the global-variable lemmas restated. -/

namespace Flatten

@[simp] theorem trafo_chainSetter_liftLens_global {A : Type} (g : Lens A State) :
    trafo.chainSetter (liftLens g) = liftLens g := Lens.chainSetter_liftLens_global _ g

@[simp] theorem emb_chainSetter_liftLens_global {A : Type} (g : Lens A State) :
    emb.chainSetter (liftLens g) = liftLens g := Lens.chainSetter_liftLens_global _ g

@[simp] theorem rename_chainSetter_liftLens_global {A : Type} (ren : List (String × String))
    (g : Lens A State) : (rename ren).chainSetter (liftLens g) = liftLens g :=
  Lens.chainSetter_liftLens_global _ g

@[simp] theorem trafo_chain_intoGlobal {A : Type} (g : Lens A State) :
    trafo.chain g.intoGlobal = g.intoGlobal := ProgramState.mapLocal_chain_intoGlobal _ g

@[simp] theorem emb_chain_intoGlobal {A : Type} (g : Lens A State) :
    emb.chain g.intoGlobal = g.intoGlobal := ProgramState.mapLocal_chain_intoGlobal _ g

@[simp] theorem rename_chain_intoGlobal {A : Type} (ren : List (String × String))
    (g : Lens A State) : (rename ren).chain g.intoGlobal = g.intoGlobal :=
  ProgramState.mapLocal_chain_intoGlobal _ g

@[simp] theorem eval_trafo_global_lens {A : Type} (τ : ProgramState) (g : Lens A State) :
    (eval (cs := ⟨trafo.get τ⟩) g : A) = eval (cs := ⟨τ⟩) g := rfl

@[simp] theorem eval_emb_global_lens {A : Type} (τ : ProgramState) (g : Lens A State) :
    (eval (cs := ⟨emb.get τ⟩) g : A) = eval (cs := ⟨τ⟩) g := rfl

@[simp] theorem eval_rename_global_lens {A : Type} (ren : List (String × String))
    (τ : ProgramState) (g : Lens A State) :
    (eval (cs := ⟨(rename ren).get τ⟩) g : A) = eval (cs := ⟨τ⟩) g := rfl

@[simp] theorem eval_trafo_global_getter {A : Type} (τ : ProgramState) (g : Getter A State) :
    (eval (cs := ⟨trafo.get τ⟩) g : A) = eval (cs := ⟨τ⟩) g := rfl

@[simp] theorem eval_emb_global_getter {A : Type} (τ : ProgramState) (g : Getter A State) :
    (eval (cs := ⟨emb.get τ⟩) g : A) = eval (cs := ⟨τ⟩) g := rfl

@[simp] theorem eval_rename_global_getter {A : Type} (ren : List (String × String))
    (τ : ProgramState) (g : Getter A State) :
    (eval (cs := ⟨(rename ren).get τ⟩) g : A) = eval (cs := ⟨τ⟩) g := rfl

/-! ### Resets

A renaming around a reset resets the renamed region; `cleanNameSet?` then puts the region back in
normal form. -/

@[simp] theorem trafo_chainSetter_resetSetter (S : Set String) :
    trafo.chainSetter (resetSetter S) = resetSetter (escape '' S) :=
  ProgramState.mapLocal_embed_chainSetter_resetSetter _ _ S

@[simp] theorem emb_chainSetter_resetSetter (S : Set String) :
    emb.chainSetter (resetSetter S) = resetSetter (tag '' S) :=
  ProgramState.mapLocal_embed_chainSetter_resetSetter _ _ S

@[simp] theorem rename_chainSetter_resetSetter (ren : List (String × String)) (S : Set String) :
    (rename ren).chainSetter (resetSetter S) = resetSetter (renameName ren '' S) :=
  ProgramState.mapLocal_embed_chainSetter_resetSetter _ _ S

end Flatten

end Clean

/-! # The meta code

The passes, of which only the first can fail:

* `flattenCall n` — flatten call site `n`, leaving deliberately ugly terms behind: everything off
  the path to the call is wrapped in `applyLens trafo` without being looked at;
* `cleanStmt` — push those wrappers inwards with the closed lemma set of `Clean`;
* `flattenSeq` — re-associate `seq` to the right and drop `skip` and `_ <- e`;
* `flattenCallCleaned n` — the three in a row, proofs composed.  The callee's variables now have
  made-up names (`«@.w»`);
* `renameNames` — the cleanup: give the made-up names readable ones (`w`, or `w0` on a clash),
  by one renaming of the whole statement;
* `flattenProcedureCalls` — repeat `flattenCallCleaned` until no call can be flattened, then
  `renameNames`.

`flattenProcedure` does it to a procedure, and *Inlining* (`unfoldProcedure`, `inlineProcedure`)
evaluates a callee that is named through modules first. -/

namespace Flatten

open Lean Meta

/-- `Lean.Expr`, under a name that `GaudisCrypt.Expr` (the program-expression abbreviation) does
not shadow. -/
abbrev Expr := Lean.Expr

/-! ## Evaluating renamed names -/

/-- A literal `List (String × String)`, read back. -/
partial def renOfExpr? (e : Expr) : Option (List (String × String)) :=
  match e.getAppFnArgs with
  | (``List.nil, _) => some []
  | (``List.cons, #[_, hd, tl]) => do
      let (``Prod.mk, #[_, _, .lit (.strVal a), .lit (.strVal f)]) := hd.getAppFnArgs | none
      return (a, f) :: (← renOfExpr? tl)
  | _ => none

/-- `escape n`, `tag n` or `renameName ren n`, with `ren` and `n` literals, evaluated. -/
def evalName? (e : Expr) : Option String :=
  match e.getAppFn.constName?, e.getAppArgs with
  | some ``escape, #[.lit (.strVal n)] => some (escape n)
  | some ``tag, #[.lit (.strVal n)] => some (tag n)
  | some ``renameName, #[ren, .lit (.strVal n)] => (renOfExpr? ren).map (renameName · n)
  | _, _ => none

/-- `varLens ⟨escape "x", T, …⟩` (or `tag`, `renameName ren`) ↦ `varLens ⟨"y", T, …⟩`, the name
evaluated and the key with it, by `varLens_rename`.

A proof, not a definitional step: the two are equal by definition too, but checking that means
evaluating `VariableName.encode` of a *computed* string, which decodes it character by character
in the unifier (tens of seconds for a short name).  With the proof, the name is compared once,
and the key is the literal's. -/
simproc_decl reduceVarName (varLens _) := fun e => do
  unless e.isAppOfArity ``varLens 1 do return .continue
  let v := e.appArg!
  unless v.isAppOfArity ``VariableName.mk 5 do return .continue
  let some n' := evalName? (v.getArg! 0) | return .continue
  let a := v.getAppArgs
  let new ← VariableName.mkTerm n' a[1]! (ne? := some a[2]!)
  let b := new.getAppArgs
  let h ← mkExpectedTypeHint (← mkEqRefl (mkStrLit n')) (← mkEq a[0]! (mkStrLit n'))
  let proof ← mkAppOptM ``varLens_rename
    #[some a[0]!, some (mkStrLit n'), some a[1]!, some a[2]!, some a[3]!, some a[4]!, some b[3]!,
      some b[4]!, some h]
  return .done { expr := mkApp (mkConst ``varLens) new, proof? := some proof }

/-! ## Reset regions in normal form

Everything the meta code knows about the normal form of a reset region (section *Reset regions*
above) is in this section; `cleanNameSet?` is its entry point. -/

/-- `nf p add rem`, as a term. -/
def nfExpr (p : String) (add rem : List String) : Expr :=
  mkAppN (mkConst ``nf) #[mkStrLit p, toExpr add, toExpr rem]

/-- A nonempty `ofList l` as a set literal `{a, b, …}`, with a proof of `ofList l = ‹it›`. -/
partial def ofListToLit (l : List String) : MetaM (Expr × Expr) := do
  let setString := mkApp (mkConst ``Set [.zero]) (mkConst ``String)
  let (e, proof) ← match l with
    | [] => throwError "ofListToLit: empty list"
    | [a] => pure (← mkAppOptM ``Singleton.singleton
          #[some (mkConst ``String), some setString, none, some (mkStrLit a)],
        mkApp (mkConst ``ofList_singleton) (mkStrLit a))
    | a :: b :: l' => do
        let (e', h') ← ofListToLit (b :: l')
        let ins ← mkAppOptM ``Insert.insert
          #[some (mkConst ``String), some setString, none, some (mkStrLit a)]
        let h₁ := mkAppN (mkConst ``ofList_cons) #[mkStrLit a, mkStrLit b, toExpr l']
        pure (mkApp ins e', ← mkEqTrans h₁ (← mkCongrArg ins h'))
  return (e, ← mkExpectedTypeHint proof (← mkEq (mkApp (mkConst ``ofList) (toExpr l)) e))

/-- A set literal `{a, b, …}` of strings, read back. -/
partial def litToList? (e : Expr) : Option (List String) :=
  match e.getAppFnArgs with
  | (``Singleton.singleton, #[_, _, _, .lit (.strVal a)]) => some [a]
  | (``Insert.insert, #[_, _, _, .lit (.strVal a), rest]) => return a :: (← litToList? rest)
  | _ => none

/-- `nf p add rem`, written out without its empty parts, with a proof of `nf p add rem = ‹it›`. -/
def nfToPretty (p : String) (add rem : List String) : MetaM (Expr × Expr) := do
  let pre := mkApp (mkConst ``prefixed) (mkStrLit p)
  let (e, proof) ← match add, rem with
    | [], [] => pure (pre, mkApp (mkConst ``nf_nil_nil) (mkStrLit p))
    | _, [] => do
        let (A, hA) ← ofListToLit add
        pure (← mkAppM ``Union.union #[A, pre],
          mkAppN (mkConst ``nf_nil_eq) #[mkStrLit p, toExpr add, A, hA])
    | [], _ => do
        let (R, hR) ← ofListToLit rem
        pure (← mkAppM ``SDiff.sdiff #[pre, R],
          mkAppN (mkConst ``nf_nil_left_eq) #[mkStrLit p, toExpr rem, R, hR])
    | _, _ => do
        let (A, hA) ← ofListToLit add
        let (R, hR) ← ofListToLit rem
        pure (← mkAppM ``Union.union #[A, ← mkAppM ``SDiff.sdiff #[pre, R]],
          mkAppN (mkConst ``nf_eq_pretty) #[mkStrLit p, toExpr add, toExpr rem, A, R, hA, hR])
  return (e, ← mkExpectedTypeHint proof (← mkEq (nfExpr p add rem) e))

/-- A reset region as `nfToPretty` writes it (or `Set.univ`), read back as `nf p add rem`, with
a proof of `S = nf p add rem`. -/
def nfOfExpr? (S : Expr) : MetaM (Option (String × List String × List String × Expr)) := do
  if S.isAppOfArity ``Set.univ 1 then return some ("", [], [], mkConst ``univ_eq_nf)
  let pre? (e : Expr) : Option String := match e.getAppFnArgs with
    | (``prefixed, #[.lit (.strVal p)]) => some p
    | _ => none
  let diff? (e : Expr) : Option (String × List String) := match e.getAppFnArgs with
    | (``SDiff.sdiff, #[_, _, a, b]) => do return (← pre? a, ← litToList? b)
    | _ => none
  let some (p, add, rem) := (match S.getAppFnArgs with
      | (``prefixed, _) => (pre? S).map fun p => (p, [], [])
      | (``SDiff.sdiff, _) => (diff? S).map fun (p, rem) => (p, [], rem)
      | (``Union.union, #[_, _, a, b]) => do
          let add ← litToList? a
          match pre? b, diff? b with
          | some p, _ => some (p, add, [])
          | none, some (p, rem) => some (p, add, rem)
          | none, none => none
      | _ => none) | return none
  let (_, h) ← nfToPretty p add rem
  return some (p, add, rem, ← mkExpectedTypeHint (← mkEqSymm h) (← mkEq S (nfExpr p add rem)))

/-- The image of `nf p add rem` under the swap of `a` and `f`, in normal form: a name leaving
the set goes out of `add` and, if it has the prefix, into `rem`; a name entering it goes out of
`rem` if it has the prefix, and into `add` otherwise.  New names go to the front, so that after a
whole renaming (whose last pair is swapped first) `add` and `rem` are in the order of the
renaming. -/
def swapNF (p : String) (add rem : List String) (a f : String) : List String × List String :=
  let ma := memB p add rem a
  let mf := memB p add rem f
  if ma == mf then (add, rem) else
  let (out, into) := if ma then (a, f) else (f, a)
  let hasPrefix (n : String) := p.toList.isPrefixOf n.toList
  let add := add.filter (· != out)
  let rem := if hasPrefix out && !rem.contains out then out :: rem else rem
  if hasPrefix into then (add, rem.filter (· != into)) else (into :: add, rem)

/-- Apply the lemma `lem` (partially applied) to a proof, by evaluation, of its next hypothesis,
a `Bool` check `… = true`. -/
def applyCheck (lem : Expr) : MetaM Expr := do
  let .forallE _ dom _ _ ← whnfR (← inferType lem) | throwError "applyCheck: not a check"
  return mkApp lem (← mkExpectedTypeHint (← mkEqRefl (toExpr true)) dom)

/-- `renameName ren '' S` in normal form, given `S` in normal form: the swaps of `ren`
one at a time, the last pair first (`image_renameName_nil`/`_cons`). -/
partial def renameNF (S : Expr) (p : String) (add rem : List String) (hS : Expr) (renE : Expr) :
    MetaM (Option (List String × List String × Expr)) := do
  match renE.getAppFnArgs with
  | (``List.nil, _) =>
      return some (add, rem, mkAppN (mkConst ``image_renameName_nil)
        #[S, mkStrLit p, toExpr add, toExpr rem, hS])
  | (``List.cons, #[_, hd, tl]) =>
      let (``Prod.mk, #[_, _, .lit (.strVal a), .lit (.strVal f)]) := hd.getAppFnArgs
        | return none
      let some (add₁, rem₁, h₁) ← renameNF S p add rem hS tl | return none
      let (add₂, rem₂) := swapNF p add₁ rem₁ a f
      unless swapOK p add₁ rem₁ add₂ rem₂ a f do return none
      let lem := mkAppN (mkConst ``image_renameName_cons)
        #[S, mkStrLit a, mkStrLit f, tl, mkStrLit p, toExpr add₁, toExpr rem₁, toExpr add₂,
          toExpr rem₂, h₁]
      return some (add₂, rem₂, ← applyCheck lem)
  | _ => return none

/-- **The set cleaning**: `ι '' S`, for `S` in normal form (or `Set.univ`) and `ι` one of `tag`,
`escape`, `renameName ren` (with `ren` a literal), in normal form again, written out
(`nfToPretty`).  `none` when the term is not of that shape. -/
def cleanNameSet? (e : Expr) : MetaM (Option Simp.Result) := do
  unless e.isAppOfArity ``Set.image 4 do return none
  let (ι, S) := (e.getArg! 2, e.getArg! 3)
  let some (p, add, rem, hS) ← nfOfExpr? S | return none
  let args (p' : String) (add' rem' : List String) : Array Expr :=
    #[S, mkStrLit p, toExpr add, toExpr rem, mkStrLit p', toExpr add', toExpr rem', hS]
  let some (p', add', rem', h) ← (match ι.getAppFnArgs with
      | (``tag, #[]) => do
          let (p', add', rem') := (tag p, add.map tag, rem.map tag)
          let h ← applyCheck (mkAppN (mkConst ``image_tag_eq) (args p' add' rem'))
          return some (p', add', rem', h)
      | (``escape, #[]) => do
          if p.isEmpty then return none
          let (p', add', rem') := (escape p, add.map escape, rem.map escape)
          let h ← applyCheck (mkAppN (mkConst ``image_escape_eq) (args p' add' rem'))
          return some (p', add', rem', h)
      | (``renameName, #[renE]) => do
          let some (add', rem', h) ← renameNF S p add rem hS renE | return none
          return some (p, add', rem', h)
      | _ => return none) | return none
  let (pretty, hp) ← nfToPretty p' add' rem'
  let proof ← mkExpectedTypeHint (← mkEqTrans h hp) (← mkEq e pretty)
  return some { expr := pretty, proof? := some proof }

/-- See `cleanNameSet?`. -/
simproc_decl reduceNameSet (Set.image _ _) := fun e => do
  let some r ← cleanNameSet? e | return .continue
  return .done r

/-- `l.chain (Lens.pair x y)` ↦ `Lens.pair x' y'`, where `x'`, `y'` are `l.chain x`, `l.chain y`
cleaned (renamed, typically) and the `Disjoint` instance is synthesized for them anew.  Not a
plain lemma: the instance argument of `Lens.pair` depends on the components, so `simp` cannot
rewrite them in place. -/
simproc_decl reduceChainPair (Lens.chain _ (Lens.pair _ _)) := fun e => do
  unless e.isAppOfArity ``Lens.chain 5 do return .continue
  let l := e.getArg! 3
  let p := e.getArg! 4
  unless p.isAppOfArity ``Lens.pair 6 do return .continue
  let (x, y) := (p.getArg! 3, p.getArg! 4)
  let rx ← Simp.simp (← mkAppM ``Lens.chain #[l, x])
  let ry ← Simp.simp (← mkAppM ``Lens.chain #[l, y])
  let .some _ ← trySynthInstance (← mkAppM ``Lens.Disjoint #[rx.expr, ry.expr])
    | return .continue
  let proof ← mkAppOptM ``Lens.chain_pair_eq
    #[none, none, none, none, some l, some x, some y, some (p.getArg! 5), some rx.expr,
      some ry.expr, none, some (← rx.getProof), some (← ry.getProof)]
  let pair ← mkAppOptM ``Lens.pair #[none, none, none, some rx.expr, some ry.expr, none]
  return .done { expr := pair, proof? := some proof }

/-! ## Statements -/

/-- What one flattening step produces: the rewritten statement, the renaming lens, and a proof
of `‹input›.EquivInLens stmt trafo`. -/
structure FlattenStep where
  /-- The rewritten statement. -/
  stmt : Expr
  /-- The renaming lens: the caller's locals, renamed. -/
  trafo : Expr
  /-- A proof of `‹input›.EquivInLens stmt trafo`. -/
  proof : Expr
  /-- The `ProgramSpec` instance the statement is over. -/
  inst : Expr
  /-- The hole context. -/
  hCtx : Expr

/-- Expose the statement hiding behind projections and definitions (`someProc.body`), *without*
zeta-reducing the `let`s of the statement — those are the user's own binders. -/
def unfoldStmt (e : Expr) : MetaM Expr :=
  withConfig (fun c => { c with zeta := false, zetaDelta := false }) (whnf e)

/-- The elements of a literal `List` expression.  Reducible transparency only: a callee named by
a definition stays stuck here, which is what makes "literal callees only" bite. -/
partial def listLitElems (e : Expr) : MetaM (List Expr) := do
  match (← whnfR e).getAppFnArgs with
  | (``List.nil, _)             => return []
  | (``List.cons, #[_, hd, tl]) => return hd :: (← listLitElems tl)
  | _ => throwError "expected a literal list, got{indentExpr e}"

/-- The strings of a literal `List String`. -/
def stringListLit (e : Expr) : MetaM (List String) := do
  (← listLitElems e).mapM fun s => do
    match ← whnfR s with
    | .lit (.strVal n) => return n
    | _ => throwError "expected a string literal, got{indentExpr s}"

/-- Is this application a **call site** — one of the two call forms, or a hole?

A hole is a call whose callee is not known yet, so it is one of the things a user counts when
numbering the call sites of a statement, even though neither flattening nor inlining can do
anything with it.  Numbering it along with the rest is what keeps the call-site numbers of a
statement independent of which sites happen to be flattenable. -/
def isCallSite (e : Expr) : Bool :=
  e.isAppOf ``StmtWithHoles.call' || e.isAppOf ``StmtWithHoles.call || e.isAppOf ``Stmt.call
    || e.isAppOf ``StmtWithHoles.hole

/-- How many call sites the statement contains, in the pre-order they are numbered by.  A callee's
own body is *not* searched: its calls belong to a later round. -/
partial def countCallSites (e₀ : Expr) : MetaM Nat := do
  let e ← unfoldStmt e₀
  if isCallSite e then return 1
  match e with
  | .letE _ _ _ body _ => countCallSites body
  | _ =>
    let args := e.getAppArgs
    match e.getAppFn.constName? with
    | some ``StmtWithHoles.seq =>
        return (← countCallSites args[2]!) + (← countCallSites args[3]!)
    | some ``StmtWithHoles.ifThenElse =>
        return (← countCallSites args[3]!) + (← countCallSites args[4]!)
    | some ``StmtWithHoles.while => countCallSites args[3]!
    | _ => return 0

/-- The pieces of a call: its signature, result l-value, the callee's parameter names (with their
two proofs), body and return value, and the argument expression. -/
structure CallData where
  /-- The callee's signature. -/
  sig : Expr
  /-- Where the result is stored. -/
  lvalue : Expr
  /-- The callee's parameter names. -/
  names : Expr
  /-- `names.length = sig.params.length`. -/
  hlen : Expr
  /-- `names.Nodup`. -/
  hnodup : Expr
  /-- The callee's body. -/
  body : Expr
  /-- The callee's return value. -/
  retVal : Expr
  /-- The argument expression. -/
  args : Expr

/-- A field of a structure literal, read off: `(ProcedureWithHoles.mk … b …).body` ↦ `b`.
Anything else is returned unchanged; nothing is unfolded but the projection. -/
def reduceField (e : Expr) : MetaM Expr := do
  let some n := e.getAppFn.constName? | return e
  unless (← getProjectionFnInfo? n).isSome do return e
  let some e' ← unfoldDefinition? e | return e
  -- `proj := .yes`: a structure named by a constant is not unfolded (`whnfCore`'s default
  -- would), so a callee named by a definition stays unflattenable
  let e'' ← withConfig (fun c => { c with proj := .yes }) (whnfCore e')
  return if e''.isProj then e else e''

/-- Read a call's pieces off the application.  Both call forms are accepted; a `call` needs a
callee that is a procedure written out. -/
def callData? (e : Expr) : MetaM (Option CallData) := do
  let args := e.getAppArgs
  match e.getAppFn.constName? with
  | some ``StmtWithHoles.call' =>
      -- `[inst] {h sig} x names hlen hnodup body ret args`; a `call` unfolds to `call'` with
      -- the callee's fields as projections
      unless args.size == 10 do return none
      let field (i : Nat) : MetaM Expr := reduceField args[i]!
      return some { sig := args[2]!, lvalue := args[3]!, names := ← field 4, hlen := args[5]!,
                    hnodup := args[6]!, body := ← field 7, retVal := ← field 8, args := args[9]! }
  | some ``StmtWithHoles.call =>
      -- `{h} [inst] {sig} x proc params`
      unless args.size == 6 do return none
      let p ← whnf args[4]!
      let pa := p.getAppArgs
      unless p.isAppOfArity ``ProcedureWithHoles.mk 8 do return none
      return some { sig := args[2]!, lvalue := args[3]!, names := pa[3]!, hlen := pa[4]!,
                    hnodup := pa[5]!, body := pa[6]!, retVal := pa[7]!, args := args[5]! }
  | _ => return none

/-- Annotate whatever goes wrong inside `k` with the step that was being built. -/
def inStep {α : Type} (what : String) (k : MetaM α) : MetaM α :=
  try k catch e => throwError "while building {what}: {e.toMessageData}"

/-! ## Names in use

The cleanup renaming gives the made-up names the names of the frame that are free.  Which names
are taken is read off the term, the literal variable names it mentions; a frame a statement reads
opaquely (through a getter that is not a variable) is not seen, but the renaming is sound
regardless, only the printed names could then be confusing. -/

/-- Every literal variable name of the frame `e` runs in (as `VariableName.mk "x" …` or
`localVarLens "x" …`), and every `let` binder name, in first-occurrence order.  The callees of
calls run in frames of their own and are skipped. -/
partial def namesIn (e : Expr) (acc : Array String := #[]) : Array String :=
  let push (acc : Array String) (n : String) := if acc.contains n then acc else acc.push n
  if e.isAppOfArity ``VariableName.mk 5 then
    match e.getArg! 0 with | .lit (.strVal n) => push acc n | _ => acc
  else if e.isAppOfArity ``localVarLens 6 then
    match e.getArg! 1 with | .lit (.strVal n) => push acc n | _ => acc
  -- a call: only its result l-value and its arguments are in this frame
  else if e.isAppOfArity ``StmtWithHoles.call' 10 then
    namesIn (e.getArg! 9) (namesIn (e.getArg! 3) acc)
  else if e.isAppOfArity ``StmtWithHoles.call 6 then
    namesIn (e.getArg! 5) (namesIn (e.getArg! 3) acc)
  else if e.isAppOfArity ``Stmt.call 5 then
    namesIn (e.getArg! 4) (namesIn (e.getArg! 2) acc)
  else match e with
  | .app f a => namesIn a (namesIn f acc)
  | .lam _ t b _ | .forallE _ t b _ => namesIn b (namesIn t acc)
  | .letE n t v b _ => namesIn b (namesIn v (namesIn t (push acc (n.eraseMacroScopes.toString))))
  | .mdata _ b | .proj _ _ b => namesIn b acc
  | _ => acc

/-- `base`, or `base0`, `base1`, … — the first one not in `used`. -/
def freshName (used : Array String) (base : String) : String :=
  if !used.contains base then base else Id.run do
    let mut i := 0
    while used.contains (base ++ toString i) do i := i + 1
    return base ++ toString i

/-- A name the flattening rounds made up: `@.w` for a callee's `w`, `@@.w` once a later round
has escaped it, and so on.  (Or a name a user wrote with a leading `@`, which the cleanup renames
just as well.) -/
def isMadeUp (n : String) : Bool := n.startsWith "@"

/-- The readable name a made-up name stands for: without its leading `@`s and `.`s. -/
def baseName (n : String) : String :=
  let b := String.ofList (n.toList.dropWhile fun c => c == '@' || c == '.')
  if b.isEmpty then "v" else b

/-! ## Flattening one call -/

/-- The parameters' new variables as one l-value — `Setter.throwaway` for none, the variable for
one, the `Lens.pair` tuple for more — with the proof that it writes the callee's parameter slots
(`IsParamWriter`). -/
partial def mkParamWriter (inst emb : Expr) : List String → List Expr → MetaM (Expr × Expr)
  | [], [] => do
      let w ← mkAppOptM ``Setter.throwaway #[some (mkConst ``Unit), some (mkApp (mkConst
        ``ProgramState) inst)]
      return (w, ← mkAppOptM ``isParamWriter_nil #[some inst, some emb, some (← lenProof [] [])])
  | z :: zs, T :: Ts => do
      let (L₁, slotArgs, hL₁) ← slot z T
      let hlen ← lenProof (z :: zs) (T :: Ts)
      match zs, Ts with
      | [], [] =>
          let pf ← mkAppOptM ``isParamWriter_single
            #[some inst, some emb, some (mkStrLit z), some T, some slotArgs[0]!, some slotArgs[1]!,
              some slotArgs[2]!, some hlen, some L₁, some hL₁]
          return (← mkAppM ``Lens.toSetter #[L₁], pf)
      | z' :: zs', T' :: Ts' =>
          let (rest, hrest) ← lensOf (z' :: zs') (T' :: Ts')
          let pair ← mkAppOptM ``Lens.pair #[none, none, none, some L₁, some rest, none]
          let pf ← mkAppOptM ``isParamWriter_cons
            #[some inst, some emb, some (mkStrLit z), some (mkStrLit z'),
              some (← mkListLit (mkConst ``String) (zs'.map mkStrLit)), some T, some T',
              some (← mkListLit (mkSort Level.one) Ts'), some slotArgs[0]!, some slotArgs[1]!,
              some slotArgs[2]!, some hlen, some (← lenProof (z' :: zs') (T' :: Ts')), some L₁,
              some rest, some hL₁, none, some hrest]
          return (← mkAppM ``Lens.toSetter #[pair], pf)
      | _, _ => throwError "the callee's parameter names and types do not match up"
  | _, _ => throwError "the callee's parameter names and types do not match up"
where
  /-- `names.length = tys.length`, for literal lists of the same length. -/
  lenProof (ns : List String) (ts : List Expr) : MetaM Expr := do
    let lhs ← mkAppM ``List.length #[← mkListLit (mkConst ``String) (ns.map mkStrLit)]
    let rhs ← mkAppOptM ``List.length
      #[some (mkSort Level.one), some (← mkListLit (mkSort Level.one) ts)]
    mkExpectedTypeHint (← mkEqRefl (mkNatLit ns.length)) (← mkEq lhs rhs)
  /-- Parameter `z : T` after renaming, `(varLens ⟨@.z, T⟩).intoLocal`, together with the
  instance, key and key proof of the callee's own `⟨z, T⟩` and the proof that `emb` takes the one
  to the other. -/
  slot (z : String) (T : Expr) : MetaM (Expr × Array Expr × Expr) := do
    let f := tag z
    let old ← inStep s!"the parameter `{z}`" <| VariableName.mkTerm z T
    let new ← VariableName.mkTerm f T
    let o := old.getAppArgs
    let n := new.getAppArgs
    let L ← mkAppOptM ``Lens.intoLocal #[some inst, some T, some (mkApp (mkConst ``varLens) new)]
    let hname ← mkExpectedTypeHint (← mkEqRefl (mkStrLit f))
      (← mkEq (mkApp (mkConst ``tag) (mkStrLit z)) (mkStrLit f))
    let h ← mkAppOptM ``emb_chain_varLens_eq
      #[some inst, some (mkStrLit z), some T, some o[2]!, some o[3]!, some o[4]!,
        some (mkStrLit f), some n[3]!, some n[4]!, some hname]
    return (L, #[o[2]!, o[3]!, o[4]!], h)
  /-- Two or more parameters as a lens (for the `Lens.pair` of the next level up). -/
  lensOf (zs : List String) (Ts : List Expr) : MetaM (Expr × Expr) := do
    let (P, pf) ← mkParamWriter inst emb zs Ts
    -- `P` is `L.toSetter`; the pair wants `L`
    unless P.isAppOfArity ``Lens.toSetter 3 do
      throwError "unexpected parameter writer{indentExpr P}"
    return (P.appArg!, pf)

/-- The replacement for one call, with its proof. -/
structure CallPlan where
  /-- `trafo`. -/
  trafo : Expr
  /-- `trafo.chain globalL = globalL`. -/
  htg : Expr
  /-- The statement replacing the call. -/
  stmt : Expr
  /-- `(call …).EquivInLens stmt trafo`. -/
  proof : Expr

/-- Build the expansion and its correctness proof for one call site. -/
def planCall (inst hCtx : Expr) (cd : CallData) : MetaM CallPlan := do
  let sigW ← whnf cd.sig
  unless sigW.isAppOfArity ``ProcedureSignature.mk 2 do
    throwError "callee's signature is not literal:{indentExpr cd.sig}"
  let paramTys ← listLitElems sigW.getAppArgs[0]!
  let names ← try stringListLit cd.names catch _ =>
    throwError "the call is not flattenable: its callee is not spelled out at the call site\
      {indentExpr cd.names}"
  let trafo ← mkAppOptM ``trafo #[some inst]
  let emb ← mkAppOptM ``emb #[some inst]
  let (P, hP) ← inStep "the parameter writer" <| mkParamWriter inst emb names paramTys
  let proof ← inStep "the call's expansion" <| mkAppOptM ``equivInLens_call
    #[some inst, some hCtx, some sigW, some cd.lvalue, some cd.names, some cd.hlen,
      some cd.hnodup, some cd.body, some cd.retVal, some cd.args, some P, some hP]
  -- the expansion is the right-hand side of the lemma
  let ty ← instantiateMVars (← inferType proof)
  unless ty.isAppOfArity ``StmtWithHoles.EquivInLens 5 do
    throwError "unexpected type of the call's expansion:{indentExpr ty}"
  let stmt := ty.getArg! 3
  let htg ← mkAppOptM ``trafo_chain_globalL #[some inst]
  return { trafo, htg, stmt, proof }

/-- What the traversal returns: the rewritten statement, its proof, and the plan the call site
produced (the lenses are only known once the call has been reached). -/
structure PathResult where
  /-- The rewritten statement. -/
  stmt : Expr
  /-- Its correctness proof. -/
  proof : Expr
  /-- The plan built at the call site. -/
  plan : CallPlan

/-- Rebuild the statement along the path to call `idx`, planning the call where it is found —
inside whatever `let` binders enclose it, since the call may mention them.  Everything off the
path is re-targeted wholesale with `applyLens`, without being inspected. -/
partial def rebuildPath (inst hCtx : Expr) (idx : Nat) (stmt₀ : Expr) : MetaM PathResult := do
  let stmt ← unfoldStmt stmt₀
  if stmt.isAppOf ``StmtWithHoles.hole then
    throwError "this call site is a hole: it has no callee to flatten"
  if isCallSite stmt then
    let some cd ← callData? stmt
      | throwError "the call is not flattenable: its callee is not spelled out"
    let plan ← planCall inst hCtx cd
    return { stmt := plan.stmt, proof := plan.proof, plan }
  match stmt with
  | .letE n ty val body _ =>
      withLetDecl n ty val fun fv => do
        let res ← rebuildPath inst hCtx idx (body.instantiate1 fv)
        return { res with stmt := ← mkLetFVars #[fv] res.stmt (usedLetOnly := false),
                          proof := ← mkLetFVars #[fv] res.proof (usedLetOnly := false) }
  | _ =>
    let args := stmt.getAppArgs
    -- a subprogram that does not contain the call, re-targeted and justified in one step
    let off (plan : CallPlan) (s : Expr) : MetaM (Expr × Expr) := do
      return (← mkAppM ``StmtWithHoles.applyLens #[plan.trafo, s],
              ← mkAppM ``StmtWithHoles.equivInLens_applyLens #[plan.trafo, plan.htg, s])
    match stmt.getAppFn.constName? with
    | some ``StmtWithHoles.seq =>
        let a := args[2]!
        let b := args[3]!
        let na ← countCallSites a
        let (res, a', pa, b', pb) ←
          if idx < na then do
            let res ← rebuildPath inst hCtx idx a
            let (b', pb) ← off res.plan b
            pure (res, res.stmt, res.proof, b', pb)
          else do
            let res ← rebuildPath inst hCtx (idx - na) b
            let (a', pa) ← off res.plan a
            pure (res, a', pa, res.stmt, res.proof)
        return { res with
          stmt := ← mkAppM ``StmtWithHoles.seq #[a', b'],
          proof := ← mkAppM ``StmtWithHoles.EquivInLens.seq #[pa, pb] }
    | some ``StmtWithHoles.ifThenElse =>
        let c := args[2]!
        let t := args[3]!
        let e := args[4]!
        let nt ← countCallSites t
        let (res, t', pt, e', pe) ←
          if idx < nt then do
            let res ← rebuildPath inst hCtx idx t
            let (e', pe) ← off res.plan e
            pure (res, res.stmt, res.proof, e', pe)
          else do
            let res ← rebuildPath inst hCtx (idx - nt) e
            let (t', pt) ← off res.plan t
            pure (res, t', pt, res.stmt, res.proof)
        return { res with
          stmt := ← mkAppM ``StmtWithHoles.ifThenElse
            #[← mkAppM ``Lens.chainGetter #[res.plan.trafo, c], t', e'],
          proof := ← mkAppM ``StmtWithHoles.EquivInLens.ifThenElse #[c, pt, pe] }
    | some ``StmtWithHoles.while =>
        let c := args[2]!
        let b := args[3]!
        let res ← rebuildPath inst hCtx idx b
        return { res with
          stmt := ← mkAppM ``StmtWithHoles.while
            #[← mkAppM ``Lens.chainGetter #[res.plan.trafo, c], res.stmt],
          proof := ← mkAppM ``StmtWithHoles.EquivInLens.while #[c, res.proof] }
    | _ => throwError "no call here:{indentExpr stmt}"

/-- The statement's type, split: its `ProgramSpec` instance and its hole context. -/
def stmtType (stmt : Expr) : MetaM (Expr × Expr) := do
  let ty ← whnf (← inferType stmt)
  unless ty.isAppOfArity ``StmtWithHoles 2 do
    throwError "not a `StmtWithHoles`:{indentExpr ty}"
  return (ty.getAppArgs[0]!, ty.getAppArgs[1]!)

/-- `a.EquivInLens b l`. -/
def mkEquivInLens (inst hCtx a b l : Expr) : MetaM Expr :=
  mkAppOptM ``StmtWithHoles.EquivInLens #[some inst, some hCtx, some a, some b, some l]

/-- Flatten call site `n` (pre-order), leaving the result deliberately uncleaned. -/
def flattenCall (n : Nat) (stmt : Expr) : MetaM FlattenStep := do
  let (inst, hCtx) ← stmtType stmt
  let total ← countCallSites stmt
  if n ≥ total then
    throwError "there is no call site number {n}: the statement has {total}"
  let res ← rebuildPath inst hCtx n stmt
  let proof ← mkExpectedTypeHint res.proof
    (← mkEquivInLens inst hCtx stmt res.stmt res.plan.trafo)
  return { stmt := res.stmt, trafo := res.plan.trafo, proof, inst, hCtx }

/-! ## Cleaning

`simp only` with `cleanLemmas`, the name evaluation of `cleanSimprocs` and **nothing else**: no
default simp set, and `zeta := false` / `zetaDelta := false`, so the user's `let`s survive.  The
only declaration unfolded is `Lens.chainGetter`, which has to go away for the `eval` lemmas to
see the state they are composed with. -/

/-- The closed lemma list of the cleaning pass.  Nothing outside this list ever rewrites the
statement. -/
def cleanLemmas : List Name :=
  -- through the statement wrappers
  [``StmtWithHoles.applyLens_skip, ``StmtWithHoles.applyLens_sample,
   ``StmtWithHoles.applyLens_assign,
   ``StmtWithHoles.applyLens_call', ``StmtWithHoles.applyLens_call,
   ``StmtWithHoles.applyLens_hole,
   ``StmtWithHoles.applyLens_seq, ``StmtWithHoles.applyLens_ifThenElse,
   ``StmtWithHoles.applyLens_while, ``StmtWithHoles.applyLens_applyLens,
   ``StmtWithHoles.weaken_skip, ``StmtWithHoles.weaken_sample, ``StmtWithHoles.weaken_assign,
   ``StmtWithHoles.weaken_call', ``StmtWithHoles.weaken_call,
   ``StmtWithHoles.weaken_seq,
   ``StmtWithHoles.weaken_ifThenElse, ``StmtWithHoles.weaken_while,
   ``StmtWithHoles.weaken_applyLens,
  -- into l-values
   ``Lens.chainSetter_liftLens, ``Lens.chainSetter_throwaway, ``Lens.chainSetter_toSetter,
   ``trafo_chainSetter_resetSetter, ``emb_chainSetter_resetSetter,
   ``rename_chainSetter_resetSetter,
   ``Lens.chainSetter_chainSetter, ``Lens.chainGetter_chainGetter, ``Lens.chainGetter_toGetter,
   ``trafo_chainSetter_liftLens_global, ``emb_chainSetter_liftLens_global,
   ``rename_chainSetter_liftLens_global,
  -- the variables: lens algebra, the renamings, globals untouched
   ``Lens.id_chain, ``Lens.chain_id, ``Lens.chain_assoc,
   ``trafo_chain_varLens, ``emb_chain_varLens, ``rename_chain_varLens,
   ``trafo_chain_intoGlobal, ``emb_chain_intoGlobal, ``rename_chain_intoGlobal,
  -- into expressions
   ``eval_chain_lens, ``eval_chain_getter,
   ``eval_trafo_global_lens, ``eval_emb_global_lens, ``eval_rename_global_lens,
   ``eval_trafo_global_getter, ``eval_emb_global_getter, ``eval_rename_global_getter]

/-- The lemmas of the cleaning pass that have to apply before `Lens.chainGetter` is unfolded. -/
def cleanPreLemmas : List Name := [``Lens.chainGetter_toGetter, ``Lens.chainGetter_chainGetter]

/-- The definitions the cleaning pass unfolds: `Lens.chainGetter`, and `typeListToTuple`, which
the content type of the parameter writer is spelled with (`Flatten.equivInLens_call`) — a
variable renamed in a later round would otherwise take that spelling for its type. -/
def cleanUnfold : List Name := [``Lens.chainGetter, ``typeListToTuple]

/-- The simprocs of the cleaning pass: evaluating the new names, renaming inside a tuple, and
the reset regions. -/
def cleanSimprocs : List Name := [``reduceVarName, ``reduceChainPair, ``reduceNameSet]

/-- The simp context and simprocs of the cleaning pass, and nothing else. -/
def cleanContext : MetaM (Simp.Context × Simp.SimprocsArray) := do
  let mut thms : SimpTheorems := {}
  -- every lemma is used as a rewrite *with its proof*, even those proved by `rfl`: `simp` would
  -- apply an `rfl` lemma as a definitional step and leave no trace, and checking the result then
  -- makes the unifier re-derive the step, which it may do by unfolding the renaming lenses and
  -- evaluating names (`(x.chain y).chain z =?= x.chain (y.chain z)` first tries `x.chain y =?= x`)
  for n in cleanLemmas do
    for thm in ← mkSimpTheoremFromConst n do
      thms := thms.addSimpTheorem { thm with rfl := false }
  -- `chainGetter` is unfolded on the way down, so the lemmas about a `chainGetter` have to fire
  -- before that: as pre-lemmas (a lens read as a getter, `L.toGetter`, has no `eval` in it for the
  -- expression lemmas to find)
  for n in cleanPreLemmas do
    for thm in ← mkSimpTheoremFromConst n (post := false) do
      thms := thms.addSimpTheorem { thm with rfl := false }
  for n in cleanUnfold do thms ← thms.addDeclToUnfold n
  let mut procs : Simprocs := {}
  for n in cleanSimprocs do procs ← procs.add n (post := true)
  -- every way `simp` could touch a `let` is switched off: `zeta`/`zetaDelta` (substituting),
  -- `zetaUnused` (dropping a binder the statement does not mention), `zetaHave` and `letToHave`
  let ctx ← Simp.mkContext
    (config := { zeta := false, zetaDelta := false, zetaUnused := false, zetaHave := false,
                 letToHave := false, decide := false, arith := false, failIfUnchanged := false })
    (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  return (ctx, #[procs])

/-- Push `applyLens` / `weaken` / `chain*` inwards as far as the terms allow, and evaluate the new
variable names.  Never fails; whatever does not match keeps its wrapper, which costs prettiness,
never correctness.

The `let`s around the statement (a procedure's holes, the user's binders) are kept, and the
statement under them is cleaned: `simp` with `zeta := false` would not go under them. -/
partial def cleanStmt (stmt : Expr) : MetaM Simp.Result := do
  match stmt with
  | .letE n ty val body _ =>
      withLetDecl n ty val fun fv => do
        let r ← cleanStmt (body.instantiate1 fv)
        let expr ← mkLetFVars #[fv] r.expr (usedLetOnly := false)
        match r.proof? with
        | none => return { expr }
        | some h =>
            -- `let x := v; (a = b)` and `(let x := v; a) = (let x := v; b)` differ by zeta
            let h ← mkLetFVars #[fv] h (usedLetOnly := false)
            return { expr, proof? := some (← mkExpectedTypeHint h (← mkEq stmt expr)) }
  | _ =>
    let (ctx, procs) ← cleanContext
    let (r, _) ← simp stmt ctx procs
    return r

/-! ## `flattenSeq` -/

/-- The statement heads a traversal stops at.  `call` is one: `whnf` would step through it to the
`call'` it is defined as, which spreads the callee over several arguments and no longer prints as
a call. -/
def stmtHeads : Array Name :=
  #[``StmtWithHoles.skip, ``StmtWithHoles.sample, ``StmtWithHoles.call', ``StmtWithHoles.call,
    ``Stmt.call, ``StmtWithHoles.hole, ``StmtWithHoles.seq, ``StmtWithHoles.ifThenElse,
    ``StmtWithHoles.while, ``StmtWithHoles.assign,
    ``StmtWithHoles.applyLens, ``StmtWithHoles.weaken]

/-- Head reduction that keeps `let`s: beta, iota and projections only. -/
def whnfNoZeta (e : Expr) : MetaM Expr :=
  withConfig (fun c => { c with zeta := false, zetaDelta := false }) (whnfCore e)

/-- Expose a statement position: reduce until a statement head (or a `let`) is visible, without
zeta-reducing and without stepping through `assign` or `call`. -/
partial def openStmt (e : Expr) : MetaM Expr := do
  let e' ← whnfNoZeta e
  if e'.isLet then return e'
  if let some n := e'.getAppFn.constName? then
    if stmtHeads.contains n then return e'
  match ← unfoldDefinition? e' with
  | some e'' => openStmt e''
  | none => return e'

/-- Is this `skip`? -/
def isSkip (e : Expr) : Bool := e.isAppOf ``StmtWithHoles.skip

/-- Is this `_ <- e`, an assignment with no effect? -/
def isThrowawayAssign (e : Expr) : Bool :=
  e.isAppOfArity ``StmtWithHoles.assign 5 && (e.getArg! 3).isAppOf ``Setter.throwaway

/-- `a.Equiv a`. -/
def mkEquivRefl (s : Expr) : MetaM Expr := mkAppM ``StmtWithHoles.Equiv.refl #[s]

/-- Concatenate two already right-nested sequences, dropping `skip`s and `_ <- e`s: returns the
result together with a proof of `(a.seq b).Equiv result`. -/
partial def concatSeq (a b : Expr) : MetaM (Expr × Expr) := do
  if isSkip a then return (b, ← mkAppM ``StmtWithHoles.Equiv.skip_seq #[b])
  if isSkip b then return (a, ← mkAppM ``StmtWithHoles.Equiv.seq_skip #[a])
  if isThrowawayAssign a then
    return (b, ← mkAppM ``StmtWithHoles.Equiv.throwaway_seq #[a.getArg! 4, b])
  if isThrowawayAssign b then
    return (a, ← mkAppM ``StmtWithHoles.Equiv.seq_throwaway #[a, b.getArg! 4])
  if a.isAppOfArity ``StmtWithHoles.seq 4 then
    let x := a.getAppArgs[2]!
    let y := a.getAppArgs[3]!
    let (r, p) ← concatSeq y b
    let p₁ ← mkAppM ``StmtWithHoles.Equiv.seq_assoc #[x, y, b]
    let p₂ ← mkAppM ``StmtWithHoles.EquivInLens.seq #[← mkEquivRefl x, p]
    let (r', p₃) ← if isSkip r then pure (x, ← mkAppM ``StmtWithHoles.Equiv.seq_skip #[x])
      else do let s ← mkAppM ``StmtWithHoles.seq #[x, r]; pure (s, ← mkEquivRefl s)
    return (r', ← mkAppM ``StmtWithHoles.Equiv.trans
      #[← mkAppM ``StmtWithHoles.Equiv.trans #[p₁, p₂], p₃])
  let s ← mkAppM ``StmtWithHoles.seq #[a, b]
  return (s, ← mkEquivRefl s)

/-- Re-associate `seq` to the right and drop `skip`s and `_ <- e`s, returning the result and a
proof of `‹input›.Equiv result`.  Never fails; `if`s are not otherwise touched. -/
partial def flattenSeq (s₀ : Expr) : MetaM (Expr × Expr) := do
  let s ← openStmt s₀
  match s with
  | .letE n ty val body _ =>
      withLetDecl n ty val fun fv => do
        let (r, p) ← flattenSeq (body.instantiate1 fv)
        return (← mkLetFVars #[fv] r (usedLetOnly := false),
                ← mkLetFVars #[fv] p (usedLetOnly := false))
  | _ =>
    let args := s.getAppArgs
    match s.getAppFn.constName? with
    | some ``StmtWithHoles.seq =>
        let (a, pa) ← flattenSeq args[2]!
        let (b, pb) ← flattenSeq args[3]!
        let (r, p) ← concatSeq a b
        let pseq ← mkAppM ``StmtWithHoles.EquivInLens.seq #[pa, pb]
        return (r, ← mkAppM ``StmtWithHoles.Equiv.trans #[pseq, p])
    | some ``StmtWithHoles.ifThenElse =>
        let (t, pt) ← flattenSeq args[3]!
        let (e, pe) ← flattenSeq args[4]!
        return (← mkAppM ``StmtWithHoles.ifThenElse #[args[2]!, t, e],
                ← mkAppM ``StmtWithHoles.Equiv.ifThenElse #[args[2]!, pt, pe])
    | some ``StmtWithHoles.while =>
        let (b, pb) ← flattenSeq args[3]!
        return (← mkAppM ``StmtWithHoles.while #[args[2]!, b],
                ← mkAppM ``StmtWithHoles.Equiv.while #[args[2]!, pb])
    | _ => return (s, ← mkEquivRefl s)

/-! ## Composition and the fixed point -/

/-- Clean `step.stmt`, and carry `step.proof` (about `input`) along: the cleaned statement, and
the proof of `input.EquivInLens ‹cleaned› step.trafo`. -/
def transportClean (input : Expr) (step : FlattenStep) : MetaM (Expr × Expr) := do
  let r ← inStep "the cleaning pass" <| cleanStmt step.stmt
  let some h := r.proof? | return (r.expr, step.proof)
  let motive ← withLocalDeclD `s (mkApp2 (mkConst ``StmtWithHoles) step.inst step.hCtx)
    fun s => do mkLambdaFVars #[s] (← mkEquivInLens step.inst step.hCtx input s step.trafo)
  return (r.expr, ← mkEqNDRec motive step.proof h)

/-- `flattenCall`, then `cleanStmt`, then `flattenSeq`, with the proofs composed.  The only step
that can fail is the first. -/
def flattenCallCleaned (n : Nat) (stmt : Expr) : MetaM FlattenStep := do
  let step ← flattenCall n stmt
  let proofC ← transportClean stmt step
  let (final, pSeq) ← inStep "the sequence pass" <| flattenSeq proofC.1
  let proofF ← mkAppM ``StmtWithHoles.EquivInLens.trans #[proofC.2, pSeq]
  -- the composite lens is `Lens.id.chain trafo`, which *is* `trafo`
  let proofF ← mkExpectedTypeHint proofF
    (← mkEquivInLens step.inst step.hCtx stmt final step.trafo)
  return { step with stmt := final, proof := proofF }

/-- The result of the whole pass. -/
structure FlatteningResult extends FlattenStep where
  /-- How many calls were flattened; nonzero, or we threw. -/
  count : Nat

/-- Run `step` on the first call site it succeeds on, or report why there is none. -/
def stepSomeCall (step : Nat → Expr → MetaM FlattenStep) (stmt : Expr) :
    MetaM (Option FlattenStep × MessageData) := do
  let total ← countCallSites stmt
  let mut why : MessageData := m!"the statement contains no call"
  for i in [0:total] do
    try
      return (some (← step i stmt), m!"")
    catch e =>
      why := e.toMessageData
  return (none, why)

/-- Run `step` on call sites until it succeeds on none, composing the proofs and the lenses.
Throws if it succeeds on nothing at all, or after `fuel` rounds. -/
def stepAllCalls (step : Nat → Expr → MetaM FlattenStep) (stmt : Expr) (fuel : Nat := 256) :
    MetaM FlatteningResult := do
  let (first?, why) ← stepSomeCall step stmt
  let some first := first?
    | throwError "nothing to flatten: {why}"
  let mut acc := first
  let mut count := 1
  repeat
    if count ≥ fuel then throwError "gave up after {fuel} rounds"
    let (next?, _) ← stepSomeCall step acc.stmt
    let some next := next? | break
    let proof ← mkAppM ``StmtWithHoles.EquivInLens.trans #[acc.proof, next.proof]
    let trafo ← mkAppM ``Lens.chain #[next.trafo, acc.trafo]
    acc := { next with proof, trafo }
    count := count + 1
  return { acc with count }

/-! ## The cleanup renaming -/

/-- Give the made-up names of `stmt` (`isMadeUp`) readable ones: `baseName`, or with `0`, `1`,
… appended on a clash with a name the statement uses or one in `avoid`.  One renaming of the whole
statement, `applyLens (rename ren)`, cleaned; sound for any choice of names, since `rename ren` is
a permutation of the names.  `none` if there is nothing to rename. -/
partial def renameNames (stmt : Expr) (avoid : Array String := #[]) :
    MetaM (Option FlattenStep) := do
  let (inst, hCtx) ← stmtType stmt
  let names := namesIn (← unfoldStmt stmt)
  let madeUp := names.filter isMadeUp
  if madeUp.isEmpty then return none
  let mut used := names.filter (!isMadeUp ·) ++ avoid
  let mut ren := #[]
  for a in madeUp do
    let f := freshName used (baseName a)
    used := used.push f
    ren := ren.push (a, f)
  let renE := toExpr ren.toList
  let l ← mkAppOptM ``rename #[some inst, some renE]
  let (s, p) ← applyLensUnderLets l (← mkAppOptM ``rename_chain_globalL #[some inst, some renE])
    stmt
  let p ← mkExpectedTypeHint p (← mkEquivInLens inst hCtx stmt s l)
  let (s', p') ← transportClean stmt { stmt := s, trafo := l, proof := p, inst, hCtx }
  return some { stmt := s', trafo := l, proof := p', inst, hCtx }
where
  /-- `applyLens l` under the `let`s a statement starts with (a procedure's holes, the user's
  binders), with its proof `equivInLens_applyLens`: cleaning does not go under an `applyLens`
  into a `let`. -/
  applyLensUnderLets (l htg stmt : Expr) : MetaM (Expr × Expr) := do
    match stmt with
    | .letE n ty v b _ =>
        withLetDecl n ty v fun fv => do
          let (s, p) ← applyLensUnderLets l htg (b.instantiate1 fv)
          return (← mkLetFVars #[fv] s (usedLetOnly := false),
                  ← mkLetFVars #[fv] p (usedLetOnly := false))
    | _ => return (← mkAppM ``StmtWithHoles.applyLens #[l, stmt],
                   ← mkAppM ``StmtWithHoles.equivInLens_applyLens #[l, htg, stmt])

/-- `step`, followed by the cleanup renaming (`renameNames`), proofs and lenses composed. -/
def withRenaming (avoid : Array String) (step : FlattenStep) : MetaM FlattenStep := do
  let some r ← renameNames step.stmt avoid | return step
  return { r with
    proof := ← mkAppM ``StmtWithHoles.EquivInLens.trans #[step.proof, r.proof]
    trafo := ← mkAppM ``Lens.chain #[r.trafo, step.trafo] }

/-- Flatten calls until none is left, then give the made-up names readable ones (avoiding
`avoid` too).  Throws if there was nothing to flatten at all; each round removes one `call`
node, so the loop terminates. -/
def flattenProcedureCalls (stmt : Expr) (avoid : Array String := #[]) :
    MetaM FlatteningResult := do
  let res ← stepAllCalls flattenCallCleaned stmt
  return { (← withRenaming avoid res.toFlattenStep) with count := res.count }

/-! ## The procedure wrapper

Run a pass on the body, give the made-up names readable ones (never the parameters' names), then
re-target `return_val` along the composite lens, and prove with `procedureDenotation_congr` that
the procedure computes the same: every renaming involved keeps the parameters' names, so the
procedure's entry state is unchanged. -/

/-- `∀ n ∈ names, f n = n`, by `decide`. -/
def fixesNamesProof (names f : Expr) : MetaM Expr := do
  let fixTy ← withLocalDeclD `n (mkConst ``String) fun n => do
    let mem ← mkAppM ``Membership.mem #[names, n]
    mkForallFVars #[n] (← mkArrow mem (← mkEq (mkApp f n) n))
  inStep "the proof that the parameters keep their names" <| mkDecideProof fixTy

/-- `FixesEntry names tys hlen l` for a composite of `trafo` and `rename ren`: each keeps the
parameters' names (checked by `decide`). -/
partial def fixesEntryProof (inst names tys hlen l : Expr) : MetaM Expr := do
  if l.isAppOfArity ``Lens.chain 5 then
    let hm ← fixesEntryProof inst names tys hlen (l.getArg! 3)
    let hl ← fixesEntryProof inst names tys hlen (l.getArg! 4)
    return ← mkAppM ``FixesEntry.chain #[hl, hm]
  if l.isAppOfArity ``trafo 1 then
    return ← mkAppOptM ``fixesEntry_trafo #[some inst, some names, some tys, some hlen,
      some (← fixesNamesProof names (mkConst ``escape))]
  if l.isAppOfArity ``rename 2 then
    let ren := l.getArg! 1
    return ← mkAppOptM ``fixesEntry_rename #[some inst, some ren, some names, some tys, some hlen,
      some (← fixesNamesProof names (mkApp (mkConst ``renameName) ren))]
  throwError "not a renaming of flattening:{indentExpr l}"

/-- `l.chain globalL = globalL` for a composite of `trafo` and `rename ren`, piece by piece.
(Not by `rfl`: the unifier would compare the renamed locals on the way, and get lost evaluating
the names of a variable it does not know.) -/
partial def keepsGlobalsProof (inst l : Expr) : MetaM Expr := do
  if l.isAppOfArity ``Lens.chain 5 then
    return ← mkAppM ``chain_chain_globalL
      #[← keepsGlobalsProof inst (l.getArg! 4), ← keepsGlobalsProof inst (l.getArg! 3)]
  if l.isAppOfArity ``trafo 1 then return ← mkAppOptM ``trafo_chain_globalL #[some inst]
  if l.isAppOfArity ``rename 2 then
    return ← mkAppOptM ``rename_chain_globalL #[some inst, some (l.getArg! 1)]
  throwError "not a renaming of flattening:{indentExpr l}"

/-- Run a pass on the body of a hole-free procedure and put the procedure back together: the
`return_val` re-targeted along the pass's lens and cleaned, and `procedureDenotation_congr` for
the proof.  Whatever else the pass reports (`α`) is passed on. -/
def inProcedure {α : Type} (p : Expr) (pass : Expr → Array String → MetaM (FlattenStep × α)) :
    MetaM (Expr × Expr × α) := do
  let ty ← whnf (← inferType p)
  unless ty.isAppOfArity ``ProcedureWithHoles 3 do
    throwError "not a procedure:{indentExpr ty}"
  let inst := ty.getAppArgs[0]!
  let hCtx ← whnf ty.getAppArgs[1]!
  unless hCtx.isAppOf ``HoleSigs.empty do
    throwError "this is stated for hole-free procedures; this one still has holes:\
      {indentExpr hCtx}"
  let sig := ty.getAppArgs[2]!
  let pW ← whnf p
  unless pW.isAppOfArity ``ProcedureWithHoles.mk 8 do
    throwError "the procedure is not spelled out:{indentExpr p}"
  let pa := pW.getAppArgs
  let (names, hlen, hnodup, body, retVal) := (pa[3]!, pa[4]!, pa[5]!, pa[6]!, pa[7]!)
  let (res, a) ← pass body (← stringListLit names).toArray
  -- the return value travels along the lens and is cleaned like the body
  let r ← cleanStmt (← mkAppM ``Lens.chainGetter #[res.trafo, retVal])
  let tys ← mkAppM ``ProcedureSignature.params #[sig]
  let hinit ← fixesEntryProof inst names tys hlen res.trafo
  let proof ← mkAppOptM ``procedureDenotation_congr
    #[some inst, some sig, some names, some hlen, some hnodup, some res.trafo, some body,
      some res.stmt, some retVal, some res.proof, some hinit,
      some (← keepsGlobalsProof inst res.trafo)]
  -- `procedureDenotation ⟨…, ret'⟩ = procedureDenotation ⟨…, ret⟩`, along the cleaning of `ret'`
  let mkProc (s rv : Expr) : MetaM Expr := mkAppOptM ``ProcedureWithHoles.mk
    #[some inst, some hCtx, some sig, some names, some hlen, some hnodup, some s, some rv]
  let proc' ← mkProc res.stmt r.expr
  let proof ← match r.proof? with
    | none => pure proof
    | some h => do
        let motive ← withLocalDeclD `g (← inferType r.expr) fun g => do
          mkLambdaFVars #[g] (← mkEq (← mkAppM ``procedureDenotation #[← mkProc res.stmt g])
            (← mkAppM ``procedureDenotation #[← mkProc body retVal]))
        mkEqNDRec motive proof h
  let proof ← mkExpectedTypeHint proof
    (← mkEq (← mkAppM ``procedureDenotation #[proc']) (← mkAppM ``procedureDenotation #[p]))
  return (proc', proof, a)

/-- Flatten the calls of a hole-free procedure.  Returns the new procedure, a proof that it has
the same `procedureDenotation`, and the number of calls flattened. -/
def flattenProcedure (p : Expr) : MetaM (Expr × Expr × Nat) :=
  inProcedure p fun body avoid => do
    let res ← flattenProcedureCalls body avoid
    return (res.toFlattenStep, res.count)

/-! ## Inlining: unfolding a module expression to a procedure

A call site may name its callee through *modules*: `call (Module.Proc.procedure (T.f (Module.app
M A))) …`.  Flattening cannot handle that — it wants the callee spelled out at the call site — so
this section provides the step before it: evaluate such a term to the procedure it denotes.

### What it evaluates, and how far

The term is built from `Module.app`, the constants the `module` and `moduletype` commands emit,
`Module.pair`/`Module.fst`/`Module.snd`, `Module.proc` and `Module.Proc.procedure`.  Two shapes
matter (`ModuleSyntax.lean` documents what each command declares):

* `T.f stuff` for a `moduletype` accessor `T.f` — the argument is evaluated **only as far as the
  accessor needs**: to a record, i.e. a `T.mk` or a `Module.pair`, and no further.  What comes
  out is the field, which is then evaluated in turn;
* `M.f stuff` for a `module`-declared procedure `M.f`, which for a module with no module
  parameters is a straight substitution of the definition.

The steps are the generated lemmas, each applied **at the head of the term and nowhere else**:
`M.apply_simp` (applying a module to its parameters, giving the record of its procedures),
`T.f.mk_simp` (reading a field off that record), `Module.fst_pair`/`snd_pair` (the same for the
anonymous record a `module` without a module type builds), `M.f.apply_simp` (applying a procedure
of a module to the parameters it uses, giving `Module.proc (M.f.procedure.instantiate ‹callees›)`)
and finally `M.f.procedure.apply_simp` (the body as written, with the hole calls turned back into
calls of those callees).  Nothing is rewritten *inside* the body: the callees it calls are left
exactly as the module wrote them.

Everything is head-position, so there is no simp set here and no risk of a lemma firing somewhere
unintended; what the pass cannot step is an error, not a silent stop.  In particular, a module
that is not concrete — `T.f (Module.app M A)` for a `M` that is a variable or an axiom — has no
body to find, and `unfoldProcedure` fails.

### And back into a statement

`inlineProcedureRaw n` rewrites call site `n` of a statement with `unfoldProcedure`, so that its
callee becomes literal; `inlineProcedure n` does that and then flattens the site with
`flattenCallCleaned n` — which is what "inlining" means here.  Call sites are numbered by
`countCallSites`, which counts `call`, `call'` *and* `hole` nodes: all three are calls as far as
someone reading the statement is concerned, and numbering them together makes the numbers
independent of which sites happen to be flattenable.  A hole has no callee, so both functions
fail on one. -/

/-- One rewrite with a named equation, at the head of `e` and nowhere else: instantiate the
lemma's binders with metavariables, unify its left-hand side with `e`, and hand back the
instantiated right-hand side together with the instantiated lemma as its proof.

`none` if the lemma does not exist (the callers name lemmas that a `module`/`moduletype`
declaration *may* have emitted), if it does not match, or if matching leaves anything open —
whatever comes back is a closed term. -/
def rewriteHead? (lem : Name) (e : Expr) : MetaM (Option (Expr × Expr)) := do
  unless (← getEnv).contains lem do return none
  -- the whole attempt is speculative: a failed match must not leave assignments behind, and the
  -- results are checked to be metavariable-free before the state is dropped
  withoutModifyingState do
    let c ← mkConstWithFreshMVarLevels lem
    let (mvars, bis, body) ← forallMetaTelescope (← inferType c)
    let some (_, lhs, _) := body.eq? | return none
    -- at reducible transparency: at default, `T.f.mk_simp` (`T.f (T.mk ?s) = …`) "matches"
    -- `T.f (Module.app M A)` by unfolding `Module.app` and `T.mk` into the same `Module.mk`
    unless ← withReducible (isDefEq lhs e) do return none
    -- an instance argument the unification did not pin down (there is none in practice: every
    -- generated lemma mentions its `ProgramSpec` in its statement)
    for (m, bi) in mvars.zip bis do
      if bi.isInstImplicit && !(← m.mvarId!.isAssigned) then
        let .some inst ← trySynthInstance (← inferType m) | return none
        unless ← isDefEq m inst do return none
    let proof ← instantiateMVars (mkAppN c mvars)
    let rhs ← instantiateMVars (← inferType proof)
    let some (_, _, rhs) := rhs.eq? | return none
    if proof.hasExprMVar || proof.hasLevelMVar || rhs.hasExprMVar || rhs.hasLevelMVar then
      return none
    return some (rhs, proof)

/-- Replace argument `i` of an application. -/
def setArg (e : Expr) (i : Nat) (x : Expr) : Expr :=
  mkAppN e.getAppFn (e.getAppArgs.set! i x)

/-- `congrArg` at argument `i` of an application: from `h : ‹arg i› = x` to `e = e[arg i := x]`. -/
def congrArgAt (e : Expr) (i : Nat) (h : Expr) : MetaM Expr := do
  let args := e.getAppArgs
  withLocalDeclD `x (← inferType args[i]!) fun x => do
    mkCongrArg (← mkLambdaFVars #[x] (setArg e i x)) h

/-- Lift a rewrite of argument `i` to the whole application. -/
def liftResultAt (e : Expr) (i : Nat) (r : Simp.Result) : MetaM Simp.Result := do
  match r.proof? with
  | none   => return { expr := setArg e i r.expr }
  | some h => return { expr := setArg e i r.expr, proof? := some (← congrArgAt e i h) }

/-- Peel the `let` telescope off a procedure and look at what is underneath. -/
partial def procCore (e : Expr) : MetaM Expr := do
  match ← whnfNoZeta e with
  | .letE _ _ v b _ => procCore (b.instantiate1 v)
  | e' => return e'

/-- Is this a procedure written out — a `ProcedureWithHoles.mk`, possibly under the `let`
telescope that binds its holes? -/
def isProcLiteral (e : Expr) : MetaM Bool :=
  return (← procCore e).isAppOfArity ``ProcedureWithHoles.mk 8

/-- `‹literal tuple›.lookup ‹literal index›`, computed.  This is what the three
`HoleSigs.Instantiation.lookup_*` lemmas say, and each of them is `rfl`, so the result is
*definitionally* the term it replaces — no proof is needed for the step, only a re-typing of the
proof that mentions it. -/
partial def lookupComponent? (e : Expr) : Option Expr := do
  guard (e.isAppOf ``HoleSigs.Instantiation.lookup)
  let args := e.getAppArgs
  guard (args.size ≥ 2)
  go args[args.size - 2]! args[args.size - 1]!
where
  /-- Walk the index, taking the tuple apart as it goes.  A one-hole instantiation is its
  procedure rather than a pair, which is the `tuple` that is not a `Prod.mk`. -/
  go (tuple idx : Expr) : Option Expr :=
    if idx.isAppOf ``HoleIndex.succ then
      if tuple.isAppOfArity ``Prod.mk 4 then go tuple.appArg! idx.appArg! else none
    else if idx.isAppOf ``HoleIndex.zero then
      some (if tuple.isAppOfArity ``Prod.mk 4 then tuple.getAppArgs[2]! else tuple)
    else none

/-- Compute away every `lookup` of a literal instantiation. -/
def reduceLookups (e : Expr) : Expr :=
  e.replace lookupComponent?

/-- Reduce a projection function applied to a record — the shape a `mk_simp` leaves behind
(`T.Structure.f {f := …, …}`).  Anything else is returned unchanged. -/
def reduceStructProj (e : Expr) : MetaM Expr := do
  let some n := e.getAppFn.constName? | return e
  let some _ ← getProjectionFnInfo? n | return e
  let some e' ← unfoldDefinition? e | return e
  let e'' ← whnfNoZeta e'
  -- only accept it if the projection really went away
  if e''.isProj || e''.getAppFn.constName? == some n then return e else return e''

/-- Spell a procedure out: `M.f.procedure.instantiate ‹callees›` becomes the body as it was
written — with each hole call turned back into a call of the callee it was made from — by the
`M.f.procedure.apply_simp` lemma the `module` command emits; a procedure named by a constant is
unfolded, its definition *being* the body.  Fails when no body can be reached. -/
partial def spellOutProcedure (e : Expr) (fuel : Nat := 32) : MetaM Simp.Result := do
  if ← isProcLiteral e then return { expr := e }
  if fuel == 0 then throwError "gave up looking for a procedure body in{indentExpr e}"
  if e.isAppOf ``ProcedureWithHoles.instantiate then
    let args := e.getAppArgs
    let p := args[args.size - 2]!
    let some c := p.getAppFn.constName?
      | throwError "no procedure body: the instantiated procedure is not a constant{indentExpr p}"
    let some (rhs, h) ← rewriteHead? (c ++ `apply_simp) e
      | throwError "no procedure body: `{c ++ `apply_simp}` does not apply to{indentExpr e}"
    -- the lemma's right-hand side calls `holeArgs.lookup ‹index›`; at a literal instantiation
    -- those are the callees themselves, definitionally
    let rhs' := reduceLookups rhs
    let h ← if rhs' == rhs then pure h else mkExpectedTypeHint h (← mkEq e rhs')
    let r ← spellOutProcedure rhs' (fuel - 1)
    ({ expr := rhs', proof? := some h } : Simp.Result).mkEqTrans r
  else if let some v ← unfoldDefinition? e then
    -- `v` is `e` by definition, so the step needs no proof of its own
    ({ expr := v } : Simp.Result).mkEqTrans (← spellOutProcedure v (fuel - 1))
  else
    throwError "no concrete procedure body:{indentExpr e}"

/-- The function argument of a `Module.app` — the last argument is what it is applied *to*. -/
def moduleAppFn? (e : Expr) : Option Nat :=
  if e.isAppOf ``Module.app && e.getAppNumArgs ≥ 2 then some (e.getAppNumArgs - 2) else none

/-- The head of a `Module.app` spine: `Module.app (… (Module.app h x₁) …) xₖ` ↦ `h`. -/
partial def moduleAppHead (e : Expr) : Expr :=
  match moduleAppFn? e with
  | some i => moduleAppHead e.getAppArgs[i]!
  | none   => e

/-- The lemma that reads a projection off a `Module.pair` — the anonymous record a `module`
without a module type builds. -/
def pairLemma? : Name → Option Name
  | ``Module.fst  => some ``Module.fst_pair
  | ``Module.snd  => some ``Module.snd_pair
  | ``Module.fst' => some ``Module.fst_pair'
  | ``Module.snd' => some ``Module.snd_pair'
  | _ => none

/-- Is this constant an accessor of a `moduletype` declaration?  It is exactly when the command
emitted the `mk_simp` lemma that reads the field back off a built module. -/
def isAccessor (c : Name) : MetaM Bool :=
  return (← getEnv).contains (c ++ `mk_simp)

/-- One step of head evaluation of a module expression: applying a module or one of its procedures
to its parameters, reading a field off a record, or — when none of those applies yet — the same
one step in the position that has to be evaluated first (the function of a `Module.app`, the
module a projection is taken of). -/
partial def moduleStep? (e : Expr) : MetaM (Option Simp.Result) := do
  let some c := e.getAppFn.constName? | return none
  let args := e.getAppArgs
  -- (1) applying a `module`-declared module, or one of its procedures, to its parameters
  if let some hc := (moduleAppHead e).getAppFn.constName? then
    if let some (rhs, h) ← rewriteHead? (hc ++ `apply_simp) e then
      return some { expr := rhs, proof? := some h }
  -- (2) a `moduletype` accessor `T.f` of a module built by `T.mk` — only then: matched against
  -- anything else, the lemma unifies by unfolding both sides
  if !args.isEmpty && args.back!.isAppOf (c.getPrefix ++ `mk) then
    if let some (rhs, h) ← rewriteHead? (c ++ `mk_simp) e then
      return some { expr := ← reduceStructProj rhs, proof? := some h }
  -- (3) a projection out of a `Module.pair`
  if let some lem := pairLemma? c then
    if let some (rhs, h) ← rewriteHead? lem e then
      return some { expr := rhs, proof? := some h }
  -- (4) not yet: evaluate the position that has to come first, one step
  let i? : Option Nat ←
    match moduleAppFn? e with                                      -- its function
    | some i => pure (some i)
    | none =>
      if (pairLemma? c).isSome || (← isAccessor c) then pure (some (args.size - 1))
      else pure none
  if let some i := i? then
    if let some r ← moduleStep? args[i]! then
      return some (← liftResultAt e i r)
  -- (5) a module named by a definition whose value is a record, `T.mk …` (a `module` with no
  -- parameters, which has no `apply_simp`): unfold it, by definition
  if let some v ← unfoldDefinition? e then
    if let some vc := v.getAppFn.constName? then
      -- `T.mk` of a `moduletype` `T` (which emits `T.mk_destruct` with it)
      if vc.getString! == "mk" && (← getEnv).contains (vc.getPrefix ++ `mk_destruct) then
        return some { expr := v }
  return none

/-- Evaluate a module expression until its head is `Module.proc`, then spell that procedure out.
Fails as soon as no step applies — which is exactly the case where the term has no concrete
procedure body. -/
partial def unfoldModuleExpr (e : Expr) (fuel : Nat := 64) : MetaM Simp.Result := do
  if e.isAppOf ``Module.proc then
    let i := e.getAppNumArgs - 1
    return ← liftResultAt e i (← spellOutProcedure e.appArg!)
  if fuel == 0 then throwError "gave up unfolding{indentExpr e}"
  let some step ← moduleStep? e
    | throwError "no concrete procedure body: nothing to unfold at the head of{indentExpr e}"
  step.mkEqTrans (← unfoldModuleExpr step.expr (fuel - 1))

/-- Unfold a term built from modules that evaluates to a procedure, and hand back the
result with a proof that it equals the term.

Accepts both levels: a module term of type `Module.Proc sig`, whose result is
`Module.proc ‹procedure›`, and a procedure term — `Module.Proc.procedure ‹module›`, the shape a
call site carries — whose result is the procedure itself.  Fails if no concrete body can be
found.

This is the pass itself; `unfoldProcedure` wraps it. -/
def unfoldProcedureCore (e : Expr) : MetaM Simp.Result := do
  let ty ← whnf (← inferType e)
  if ty.isAppOfArity ``ProcedureWithHoles 3 then
    unless e.isAppOf ``Module.Proc.procedure do
      -- a procedure named some other way: nothing module-ish to evaluate, only a body to reach
      return ← spellOutProcedure e
    let i := e.getAppNumArgs - 1
    let r₁ ← liftResultAt e i (← unfoldModuleExpr e.appArg!)
    let some (rhs, h) ← rewriteHead? ``Module.procedure_proc' r₁.expr
      | throwError "unexpected: the module did not unfold to a `Module.proc`{indentExpr r₁.expr}"
    let r ← r₁.mkEqTrans { expr := rhs, proof? := some h }
    r.mkEqTrans (← spellOutProcedure rhs)
  else if ty.isAppOf ``GaudisCrypt.Module then
    unfoldModuleExpr e
  else
    throwError "not a module or a procedure:{indentExpr (← inferType e)}"

/-- `unfoldProcedureCore`, with the proof re-typed to say what it proves.

A step that unfolds a *definition* carries no proof of its own — `none` is `rfl` — so what the
composed proof states can end at a term that is only definitionally the result.  Both are
correct; this is the one a caller (and a `#check`) would rather read. -/
def unfoldProcedure (e : Expr) : MetaM Simp.Result := do
  let r ← unfoldProcedureCore e
  let some h := r.proof? | return r
  return { r with proof? := some (← mkExpectedTypeHint h (← mkEq e r.expr)) }

/-- Rewrite call site `idx` of a statement by unfolding its callee, and prove that the result
*equals* the statement.  The traversal is the one that numbers the call sites, with the single
difference that it stops at a `StmtWithHoles.call` (`openStmt`): `whnf` would step through it to
the `call'` it is defined as, which spreads the callee over several arguments instead of one. -/
partial def rewriteCalleeAt (idx : Nat) (e₀ : Expr) : MetaM Simp.Result := do
  let e ← openStmt e₀
  if isCallSite e then
    unless idx == 0 do throwError "there is no call site number {idx} here:{indentExpr e}"
    match e.getAppFn.constName? with
    | some ``StmtWithHoles.call | some ``Stmt.call =>
        let i := e.getAppNumArgs - 2
        liftResultAt e i (← unfoldProcedure e.getAppArgs[i]!)
    | some ``StmtWithHoles.call' =>
        throwError "this call site has no callee to unfold: its callee is already spelled out"
    | _ => throwError "this call site is a hole: it has no callee to unfold"
  else match e with
  | .letE n ty val body _ =>
      withLetDecl n ty val fun fv => do
        let r ← rewriteCalleeAt idx (body.instantiate1 fv)
        let expr ← mkLetFVars #[fv] r.expr (usedLetOnly := false)
        match r.proof? with
        | none => return { expr }
        | some h =>
            -- `let x := v; (a = b)` and `(let x := v; a) = (let x := v; b)` differ by zeta
            let h ← mkLetFVars #[fv] h (usedLetOnly := false)
            return { expr, proof? := some (← mkExpectedTypeHint h (← mkEq e expr)) }
  | _ =>
    let args := e.getAppArgs
    let one (i : Nat) : MetaM Simp.Result := do
      liftResultAt e i (← rewriteCalleeAt idx args[i]!)
    let two (i j : Nat) : MetaM Simp.Result := do
      let ni ← countCallSites args[i]!
      if idx < ni then one i
      else liftResultAt e j (← rewriteCalleeAt (idx - ni) args[j]!)
    match e.getAppFn.constName? with
    | some ``StmtWithHoles.seq => two 2 3
    | some ``StmtWithHoles.ifThenElse => two 3 4
    | some ``StmtWithHoles.while => one 3
    | _ => throwError "no call site here:{indentExpr e}"

/-- Unfold the callee of call site `n`, leaving the call itself alone.  The proof is an
equation: the statement is rewritten, not re-targeted. -/
def inlineProcedureRaw (n : Nat) (stmt : Expr) : MetaM Simp.Result := do
  let total ← countCallSites stmt
  if n ≥ total then
    throwError "there is no call site number {n}: the statement has {total}"
  let r ← rewriteCalleeAt n stmt
  let some h := r.proof? | return r
  return { r with proof? := some (← mkExpectedTypeHint h (← mkEq stmt r.expr)) }

/-- Inline call site `n`, leaving the callee's variables with made-up names: unfold its callee
(`inlineProcedureRaw`), then flatten the call (`flattenCallCleaned`).  The two proofs compose: the
first is an equation, which transports the second's `EquivInLens` back to the statement it
started from. -/
def inlineCall (n : Nat) (stmt : Expr) : MetaM FlattenStep := do
  let r ← inlineProcedureRaw n stmt
  let step ← flattenCallCleaned n r.expr
  let some h := r.proof? | return step
  let motive ← withLocalDeclD `s (mkApp2 (mkConst ``StmtWithHoles) step.inst step.hCtx)
    fun s => do mkLambdaFVars #[s] (← mkEquivInLens step.inst step.hCtx s step.stmt step.trafo)
  return { step with proof := ← mkEqNDRec motive step.proof (← mkEqSymm h) }

/-- Inline call site `n` (`inlineCall`), then give the made-up names readable ones (avoiding
`avoid` too). -/
def inlineProcedure (n : Nat) (stmt : Expr) (avoid : Array String := #[]) :
    MetaM FlattenStep := do
  withRenaming avoid (← inlineCall n stmt)

/-- `inlineProcedure` at the procedure level: inline call site `n` of the body of a
hole-free procedure that is spelled out, and hand back the new procedure together with a proof
that it has the same `procedureDenotation`.

`proc (…) { xxx; call bla; yyy }` becomes `proc (…) { xxx; ‹the body of bla›; yyy }`, with the
callee's variables added to the procedure's own (renamed where they collide) and its result
stored where the call stored it. -/
def inlineInProcedure (n : Nat) (p : Expr) : MetaM (Expr × Expr) := do
  let (p', proof, _) ← inProcedure p fun body avoid => return (← inlineProcedure n body avoid, ())
  return (p', proof)

end Flatten

/-! ## Hoare triples

A statement triple is a triple about any statement equivalent to its own, with the conditions read
through the lens of the equivalence: so it can be proved about the flattened statement instead
(`hoare_inline`). -/

omit [ProgramSpec] in
/-- The chance of an event under `mapState f μ` is that of its preimage under `μ`. -/
theorem SubProbability.ofEvent_mapState {α : Type v} {s t : Type u} (f : t → s)
    (μ : SubProbability (α × t)) (E : Set (α × s)) :
    (μ.mapState f).ofEvent E = μ.ofEvent ((fun p => (p.1, f p.2)) ⁻¹' E) := by
  letI : MeasurableSpace (α × s) := ⊤
  letI : MeasurableSpace (α × t) := ⊤
  change (MeasureTheory.Measure.bind μ.1 (fun p => MeasureTheory.Measure.dirac (p.1, f p.2)) E
    ).toNNReal = (μ.1 _).toNNReal
  rw [MeasureTheory.Measure.bind_dirac_eq_map _ measurable_from_top,
    MeasureTheory.Measure.map_apply measurable_from_top (MeasurableSpace.measurableSet_top)]

/-- **A triple about an equivalent statement**: along `s.EquivInLens s' l`, the triple about `s`
is the triple about `s'` with both conditions read through `l`. -/
theorem hoareStmt_iff_of_equivInLens {A B : ProgramState → Prop} {s s' : Stmt}
    {l : Lens ProgramState ProgramState} (h : s.EquivInLens s' l) :
    hoareStmt A s B ↔ hoareStmt (fun τ => A (l.get τ)) s' (fun τ => B (l.get τ)) := by
  have h' : ∀ τ, (programDenotation s' τ).mapState l.get = programDenotation s (l.get τ) :=
    fun τ => by
      have := h ⟨⟩ (l.get τ) τ rfl
      rwa [StmtWithHoles.instantiate_empty, StmtWithHoles.instantiate_empty] at this
  constructor
  · intro hs τ hA
    have := hs _ hA
    rw [← h' τ, SubProbability.ofEvent_mapState] at this
    exact this
  · intro hs σ hA
    have hτ : l.get (l.set σ σ) = σ := l.set_get σ σ
    have := hs (l.set σ σ) (show A (l.get (l.set σ σ)) by rw [hτ]; exact hA)
    rw [← hτ, ← h', SubProbability.ofEvent_mapState]
    exact this

/-- `hoareStmt_iff_of_equivInLens`, backwards, with the conditions given up to an equation: what
`hoare_inline` applies, the equations being those of the cleaning pass. -/
theorem hoareStmt_of_equivInLens {A B A' B' : ProgramState → Prop} {s s' : Stmt}
    {l : Lens ProgramState ProgramState} (h : s.EquivInLens s' l)
    (hA : (fun τ => A (l.get τ)) = A') (hB : (fun τ => B (l.get τ)) = B')
    (h' : hoareStmt A' s' B') : hoareStmt A s B := by
  subst hA hB
  exact (hoareStmt_iff_of_equivInLens h).mpr h'

namespace Flatten

open Lean Meta Elab Tactic

/-- `fun τ => C (l.get τ)`, cleaned like a statement, with the equation. -/
def cleanCondition (C l : Expr) : MetaM (Expr × Expr) := do
  let ty ← inferType C
  let .forallE _ dom _ _ ← whnf ty | throwError "not a condition:{indentExpr C}"
  let lam ← withLocalDeclD `τ dom fun τ => do
    mkLambdaFVars #[τ] (C.beta #[← mkAppM ``Getter.get #[← mkAppM ``Lens.toGetter #[l], τ]])
  let r ← cleanStmt lam
  return (r.expr, ← r.getProof)

/-- On a goal `hoareStmt A s B`: inline call site `n` of `s` (`inlineProcedure`) and continue with
the triple about the result, its conditions read through the renaming and cleaned.  The names the
conditions use count as taken. -/
def hoareInline (n : Nat) (g : MVarId) : MetaM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``hoareStmt 4 do
    throwError "hoare_inline: expected a goal `hoareStmt A s B`, got{indentExpr ty}"
  let (A, s, B) := (ty.getArg! 1, ty.getArg! 2, ty.getArg! 3)
  let step ← inlineProcedure n s (namesIn B (namesIn A))
  let (A', hA) ← cleanCondition A step.trafo
  let (B', hB) ← cleanCondition B step.trafo
  let g' ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``hoareStmt #[A', step.stmt, B']) (← g.getTag)
  g.assign (← mkAppOptM ``hoareStmt_of_equivInLens
    #[some (ty.getArg! 0), some A, some B, some A', some B', some s, some step.stmt,
      some step.trafo, some step.proof, some hA, some hB, some g'])
  return g'.mvarId!

/-- `hoare_inline n`: on a goal `hoareStmt A s B`, inline call site `n` of `s` (numbered in
pre-order, holes included; the callee spelled out, named by a definition or through modules), and
continue with the triple about the result.  The callee's own calls stay calls. -/
elab "hoare_inline " n:num : tactic =>
  liftMetaTactic1 fun g => some <$> hoareInline n.getNat g

end Flatten

end GaudisCrypt
