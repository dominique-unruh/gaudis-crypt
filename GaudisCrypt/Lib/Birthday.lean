import GaudisCrypt.ProgramRange

/-!
# The birthday accumulation bound (generic)

A reusable "balls into bins" accumulation lemma for the bounded loop
combinator `loop_n`, independent of any random-oracle structure. Given a
loop body that

* bumps a *collision* potential `coll : s → ENNReal` by at most `size σ / N`
  per iteration, and
* bumps a *size* potential `size : s → ℕ` by at most `1` per iteration,

the `n`-fold loop bumps `coll` by at most the triangular sum
`n (2·size + n − 1) / 2N` — and starting from `size = 0` this is the
birthday bound `n(n−1)/2N`.

This is the abstract core shared by collision-resistance and the PRP/PRF
switching lemma; each supplies the two per-step facts (e.g. "a lazy query
collides with probability ≤ `RO_size/N`" and "the cache grows by ≤ 1") and
instantiates `loop_n_birthday_bound`.
-/

/-- **Form-conversion** for the induction step: `k·((2m+k)−1) = k·(2m+(k−1))`
    in `ENNReal` (the `↑k` factor annihilates the `k = 0` mismatch). -/
private lemma layer_C_term_alt (m_e : ENNReal) (k : ℕ) :
    (k : ENNReal) * ((2 * m_e + (k : ENNReal)) - 1)
    = (k : ENNReal) * (2 * m_e + ((k : ENNReal) - 1)) := by
  cases k with
  | zero => simp
  | succ n =>
    congr 1
    rw [ENNReal.natCast_succ_sub_one]
    push_cast
    rw [show (2 * m_e + ((n : ENNReal) + 1) - 1) = 2 * m_e + (n : ENNReal) from by
      rw [← add_assoc]
      exact ENNReal.add_sub_cancel_right (by norm_num)]

/-- **Combine helper** for the succ case:
    `m/N + k(2(m+1) + (k−1))/(2N) = (k+1)(2m+k)/(2N)`. -/
private lemma layer_C_combine_div (m k : ℕ) (N : ENNReal)
    (hN_pos : N ≠ 0) (hN_top : N ≠ ⊤) :
    (m : ENNReal) / N
      + ((k : ENNReal) * (2 * ((m : ENNReal) + 1) + ((k : ENNReal) - 1))) / (2 * N)
    = ((k : ENNReal) + 1) * (2 * (m : ENNReal) + (k : ENNReal)) / (2 * N) := by
  rw [show (m : ENNReal) / N = (2 * (m : ENNReal)) / (2 * N) from
    (ENNReal.mul_div_mul_left (m : ENNReal) N (by norm_num) (by norm_num)).symm]
  rw [ENNReal.div_add_div_same]
  congr 1
  cases k with
  | zero => push_cast; ring
  | succ n =>
    rw [ENNReal.natCast_succ_sub_one]
    push_cast
    ring

/-- **The birthday accumulation bound.** If `body` bumps `coll` by at most
    `size/N` and `size` by at most `1` per iteration, then `loop_n k body`
    bumps `coll` by at most `k(2·size + k − 1)/2N`. -/
lemma loop_n_birthday_bound {s : Type} (body : Program s Unit)
    (coll : s → ENNReal) (size : s → ℕ) (N : ENNReal)
    (hN_pos : N ≠ 0) (hN_top : N ≠ ⊤)
    (h_coll : ∀ σ, body.wp (fun yσ : Unit × s => coll yσ.2) σ
        ≤ coll σ + (size σ : ENNReal) / N)
    (h_size : ∀ σ, body.wp (fun yσ : Unit × s => (size yσ.2 : ENNReal)) σ
        ≤ (size σ : ENNReal) + 1)
    (k : ℕ) (σ : s) :
    (loop_n k body).wp (fun yσ : Unit × s => coll yσ.2) σ
    ≤ coll σ + (k * (2 * size σ + k - 1) : ENNReal) / (2 * N) := by
  induction k generalizing σ with
  | zero =>
    show (pure () : Program s Unit).wp _ σ ≤ _
    rw [wp_pure]
    simp
  | succ k ih =>
    show (body >>= fun _ => loop_n k body).wp _ σ ≤ _
    rw [wp_bind]
    push_cast
    rw [show (2 * (↑(size σ) : ENNReal) + ((k : ENNReal) + 1) - 1)
          = (2 * (↑(size σ) : ENNReal) + (k : ENNReal)) from by
      rw [← add_assoc]
      exact ENNReal.add_sub_cancel_right (by norm_num)]
    have h_inner_bound :
        body.wp (fun yσ : Unit × s =>
            2 * (↑(size yσ.2) : ENNReal) + ((k : ENNReal) - 1)) σ
        ≤ 2 * ((↑(size σ) : ENNReal) + 1) + ((k : ENNReal) - 1) := by
      calc body.wp (fun yσ : Unit × s =>
              2 * (↑(size yσ.2) : ENNReal) + ((k : ENNReal) - 1)) σ
          = body.wp (fun yσ : Unit × s => 2 * (↑(size yσ.2) : ENNReal)) σ
            + body.wp (fun _ : Unit × s => ((k : ENNReal) - 1)) σ := by
            rw [Program.wp_add]
        _ ≤ 2 * ((↑(size σ) : ENNReal) + 1) + ((k : ENNReal) - 1) := by
            gcongr
            · rw [Program.wp_const_mul]; gcongr; exact h_size σ
            · exact Program.wp_const_le body ((k : ENNReal) - 1) σ
    have h_IH_term_bound :
        body.wp (fun yσ : Unit × s =>
            ((k : ENNReal) * (2 * (↑(size yσ.2) : ENNReal) + ((k : ENNReal) - 1))) / (2 * N)) σ
        ≤ ((k : ENNReal) * (2 * ((↑(size σ) : ENNReal) + 1) + ((k : ENNReal) - 1))) / (2 * N) := by
      rw [show (fun yσ : Unit × s =>
              ((k : ENNReal) * (2 * (↑(size yσ.2) : ENNReal) + ((k : ENNReal) - 1))) / (2 * N))
            = (fun yσ : Unit × s =>
              (k : ENNReal) *
                ((2 * (↑(size yσ.2) : ENNReal) + ((k : ENNReal) - 1)) / (2 * N)))
            from by funext yσ; rw [mul_div_assoc]]
      rw [Program.wp_const_mul]
      rw [show ((k : ENNReal) *
              (2 * ((↑(size σ) : ENNReal) + 1) + ((k : ENNReal) - 1))) / (2 * N)
            = (k : ENNReal) *
                ((2 * ((↑(size σ) : ENNReal) + 1) + ((k : ENNReal) - 1)) / (2 * N))
            from by rw [mul_div_assoc]]
      gcongr
      calc body.wp (fun yσ : Unit × s =>
              (2 * (↑(size yσ.2) : ENNReal) + ((k : ENNReal) - 1)) / (2 * N)) σ
          = (1 / (2 * N)) * body.wp (fun yσ : Unit × s =>
              2 * (↑(size yσ.2) : ENNReal) + ((k : ENNReal) - 1)) σ := by
            rw [show (fun yσ : Unit × s =>
                  (2 * (↑(size yσ.2) : ENNReal) + ((k : ENNReal) - 1)) / (2 * N))
                  = (fun yσ : Unit × s =>
                  (1 / (2 * N)) *
                    (2 * (↑(size yσ.2) : ENNReal) + ((k : ENNReal) - 1)))
                from by funext yσ; rw [one_div, ← ENNReal.div_eq_inv_mul]]
            rw [Program.wp_const_mul]
        _ ≤ (1 / (2 * N)) * (2 * ((↑(size σ) : ENNReal) + 1) + ((k : ENNReal) - 1)) := by
            exact mul_le_mul_left' h_inner_bound _
        _ = (2 * ((↑(size σ) : ENNReal) + 1) + ((k : ENNReal) - 1)) / (2 * N) := by
            rw [one_div, ← ENNReal.div_eq_inv_mul]
    calc body.wp (fun yσ : Unit × s =>
            (loop_n k body).wp (fun yσ' : Unit × s => coll yσ'.2) yσ.2) σ
        ≤ body.wp (fun yσ : Unit × s =>
            coll yσ.2 +
              ((k : ENNReal) * ((2 * (↑(size yσ.2) : ENNReal) + (k : ENNReal)) - 1))
                / (2 * N)) σ := by
          exact Program.wp_le_wp_of_le _ _ _ (fun yσ => ih yσ.2) σ
      _ = body.wp (fun yσ : Unit × s =>
            coll yσ.2 +
              ((k : ENNReal) * (2 * (↑(size yσ.2) : ENNReal)
                + ((k : ENNReal) - 1))) / (2 * N)) σ := by
          congr 1; funext yσ
          rw [layer_C_term_alt _ k]
      _ = body.wp (fun yσ : Unit × s => coll yσ.2) σ
          + body.wp (fun yσ : Unit × s =>
              ((k : ENNReal) * (2 * (↑(size yσ.2) : ENNReal)
                + ((k : ENNReal) - 1))) / (2 * N)) σ := by
          rw [Program.wp_add]
      _ ≤ (coll σ + (↑(size σ) : ENNReal) / N)
          + ((k : ENNReal) * (2 * ((↑(size σ) : ENNReal) + 1) + ((k : ENNReal) - 1)))
              / (2 * N) := by
          apply add_le_add
          · exact h_coll σ
          · exact h_IH_term_bound
      _ = coll σ +
          ((k : ENNReal) + 1) * (2 * (↑(size σ) : ENNReal) + (k : ENNReal)) / (2 * N) := by
          rw [add_assoc, layer_C_combine_div (size σ) k N hN_pos hN_top]
