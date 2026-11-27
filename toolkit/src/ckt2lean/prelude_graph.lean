def lcol (m : ℕ) : ℕ → ℕ
  | 0 => 2 ^ m - 1
  | j + 1 => 2 ^ m * lcol m j

def rcol (m v : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => 2 ^ v + 2 ^ m * rcol m v k

def inCols (n m : ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => lcol m i) ++ List.ofFn (fun j : Fin m => rcol m j n)

theorem bit_lcol {m v : ℕ} (hv : v < m) :
    ∀ (j u : ℕ), (lcol m j).testBit (u * m + v) = decide (u = j) := by
  intro j
  induction j with
  | zero =>
    intro u
    cases u with
    | zero => simp [lcol, hv]
    | succ u =>
      simp only [lcol, Nat.testBit_two_pow_sub_one]
      have hle : m ≤ (u + 1) * m := Nat.le_mul_of_pos_left m (Nat.succ_pos u)
      simp
      omega
  | succ j ih =>
    intro u
    rw [lcol, Nat.testBit_two_pow_mul]
    cases u with
    | zero =>
      simp
      omega
    | succ u =>
      have e : (u + 1) * m + v - m = u * m + v := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v ≥ m := by rw [Nat.succ_mul]; omega
      simp only [ge_iff_le, g, decide_true, Bool.true_and, e, ih u]
      simp

theorem bit_rcol {m v v' : ℕ} (hv : v < m) (hv' : v' < m) :
    ∀ (n u : ℕ), (rcol m v n).testBit (u * m + v') = decide (u < n ∧ v' = v) := by
  intro n
  induction n with
  | zero =>
    intro u
    simp [rcol]
  | succ n ih =>
    intro u
    have hlt : 2 ^ v < 2 ^ m := Nat.pow_lt_pow_right (by norm_num) hv
    rw [rcol, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hlt, Nat.testBit_or, Nat.testBit_two_pow_mul,
      Nat.testBit_two_pow]
    cases u with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show decide (v' ≥ m) = false from decide_eq_false (by omega), Bool.false_and, Bool.false_or]
      by_cases h : v' = v
      · subst h
        simp
      · simp only [Nat.succ_pos, true_and, h, decide_false]
        exact decide_eq_false (fun e => h e.symm)
    | succ u =>
      have e : (u + 1) * m + v' - m = u * m + v' := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v' ≥ m := by rw [Nat.succ_mul]; omega
      have ne : v ≠ (u + 1) * m + v' := by rw [Nat.succ_mul]; omega
      simp only [g, decide_true, Bool.true_and, e, ih u, ne, decide_false, Bool.or_false]
      simp

theorem inCols_bit {n m : ℕ} (u : Fin n) (v : Fin m) (j : ℕ) :
    ((inCols n m).getD j 0).testBit (u.val * m + v.val) = (oneEach u v).getD j false := by
  by_cases hj : j < n
  · rw [inCols, oneEach, List.getD_append _ _ _ _ (by simpa using hj),
      List.getD_append _ _ _ _ (by simpa using hj)]
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [List.getElem_ofFn]
    rw [bit_lcol v.isLt j u.val]
    simp [Fin.ext_iff, eq_comm]
  · by_cases hj2 : j < n + m
    · have h1 : (List.ofFn (fun i : Fin n => lcol m i)).length ≤ j := by simp; omega
      have h2 : (List.ofFn (fun i : Fin n => decide (i = u))).length ≤ j := by simp; omega
      rw [inCols, oneEach, List.getD_append_right _ _ _ _ h1, List.getD_append_right _ _ _ _ h2]
      simp only [List.length_ofFn]
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_ofFn]
      rw [bit_rcol (by omega) v.isLt n u.val]
      simp only [u.isLt, true_and]
      simp [Fin.ext_iff]
      omega
    · rw [List.getD_eq_default _ _ (by simp [inCols]; omega),
        List.getD_eq_default _ _ (by simp [oneEach]; omega)]
      simp

def gmask (n m : ℕ) : ℕ := 2 ^ (n * m) - 1

def gcap (n m D : ℕ) (C : Circuit) : Bool := decide (n + m + C.gates.length ≤ 2 ^ D)

theorem graph_bit {n m : ℕ} (D : ℕ) (C : Circuit) (hg : aonB C = true) (hsz : gcap n m D C = true)
    (o : ℕ) (u : Fin n) (v : Fin m) :
    (wcol (gmask n m) D C (inCols n m) o).testBit (u.val * m + v.val) = (C.wires (oneEach u v)).getD o false := by
  have hk : u.val * m + v.val < n * m := by
    have h1 : u.val * m + v.val < (u.val + 1) * m := by rw [Nat.succ_mul]; omega
    have h2 : (u.val + 1) * m ≤ n * m := Nat.mul_le_mul_right m u.isLt
    omega
  have hM : (gmask n m).testBit (u.val * m + v.val) = true := by
    rw [gmask, Nat.testBit_two_pow_sub_one]
    exact decide_eq_true hk
  have hcap : (inCols n m).length + C.gates.length ≤ 2 ^ D := by
    have h3 : n + m + C.gates.length ≤ 2 ^ D := of_decide_eq_true hsz
    simpa [inCols] using h3
  exact wcol_bit hM C (inCols n m) (oneEach u v) hg (by simp [inCols, oneEach]) (inCols_bit u v) hcap o

theorem represents_of {n m : ℕ} (D : ℕ) (C : Circuit) (A : Fin n → Fin m → Bool)
    (hg : aonB C = true) (hsz : gcap n m D C = true)
    (h : ∀ u : Fin n, ∀ v : Fin m,
      (wcol (gmask n m) D C (inCols n m) C.output).testBit (u.val * m + v.val) = A u v) :
    Represents A C := by
  intro u v
  have h4 := graph_bit D C hg hsz C.output u v
  rw [h u v] at h4
  exact h4.symm

def tcol (m : ℕ) : List ℕ → ℕ
  | [] => 0
  | r :: rs => r + 2 ^ m * tcol m rs

theorem lt_two_pow_of_lt {a b c : ℕ} (h : a < 2 ^ b) (hbc : b ≤ c) : a < 2 ^ c :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hbc)

theorem bit_tcol {m v : ℕ} (hv : v < m) :
    ∀ (rows : List ℕ), (∀ r ∈ rows, r < 2 ^ m) → ∀ u : ℕ,
      (tcol m rows).testBit (u * m + v) = (rows.getD u 0).testBit v := by
  intro rows
  induction rows with
  | nil =>
    intro _ u
    simp [tcol]
  | cons r rs ih =>
    intro hr u
    have hr0 : r < 2 ^ m := hr r List.mem_cons_self
    rw [tcol, Nat.add_comm, Nat.two_pow_add_eq_or_of_lt hr0, Nat.testBit_or, Nat.testBit_two_pow_mul]
    cases u with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add]
      rw [show decide (v ≥ m) = false from decide_eq_false (by omega), Bool.false_and, Bool.false_or]
      simp
    | succ u =>
      have e : (u + 1) * m + v - m = u * m + v := by rw [Nat.succ_mul]; omega
      have g : (u + 1) * m + v ≥ m := by rw [Nat.succ_mul]; omega
      have hz : r.testBit ((u + 1) * m + v) = false :=
        Nat.testBit_lt_two_pow (lt_two_pow_of_lt hr0 (by rw [Nat.succ_mul]; omega))
      simp only [g, decide_true, Bool.true_and, e, ih (fun x hx => hr x (List.mem_cons_of_mem _ hx)) u, hz,
        Bool.or_false, List.getD_cons_succ]

def rowsB (m : ℕ) (rows : List ℕ) : Bool := rows.all fun r => decide (r < 2 ^ m)

theorem represents_rows {n m : ℕ} (D : ℕ) (C : Circuit) (rows : List ℕ)
    (hrows : rowsB m rows = true) (hg : aonB C = true) (hsz : gcap n m D C = true)
    (h : (wcol (gmask n m) D C (inCols n m) C.output == tcol m rows) = true) :
    Represents (fun (u : Fin n) (v : Fin m) => (rows.getD u.val 0).testBit v.val) C := by
  intro u v
  have hr : ∀ r ∈ rows, r < 2 ^ m := fun r hr0 => of_decide_eq_true (List.all_eq_true.mp hrows r hr0)
  have h4 := graph_bit D C hg hsz C.output u v
  rw [beq_iff_eq.mp h, bit_tcol v.isLt rows hr u.val] at h4
  exact h4.symm
