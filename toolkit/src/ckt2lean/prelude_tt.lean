theorem tableIndex_succ {n : ℕ} (x : Fin (n + 1) → Bool) :
    tableIndex x = tableIndex (fun i : Fin n => x i.castSucc)
      + (if x (Fin.last n) = true then 2 ^ n else 0) := by
  unfold tableIndex
  rw [Fin.sum_univ_castSucc]
  rfl

theorem tableIndex_lt : ∀ {n : ℕ} (x : Fin n → Bool), tableIndex x < 2 ^ n := by
  intro n
  induction n with
  | zero =>
    intro x
    simp [tableIndex]
  | succ n ih =>
    intro x
    rw [tableIndex_succ, pow_succ]
    have h0 := ih (fun i : Fin n => x i.castSucc)
    split <;> omega

theorem testBit_tableIndex : ∀ {n : ℕ} (x : Fin n → Bool) (i : Fin n),
    Nat.testBit (tableIndex x) i = x i := by
  intro n
  induction n with
  | zero =>
    intro x i
    exact i.elim0
  | succ n ih =>
    intro x i
    have hlt := tableIndex_lt (fun i : Fin n => x i.castSucc)
    rw [tableIndex_succ]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.val_last]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hlt]
        rfl
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero, Nat.testBit_lt_two_pow hlt]
    · have hj : (j.castSucc : ℕ) = (j : ℕ) := rfl
      rw [hj]
      by_cases h : x (Fin.last n) = true
      · simp only [h, ↓reduceIte]
        rw [Nat.add_comm, Nat.testBit_two_pow_add_gt j.isLt]
        exact ih _ j
      · simp only [h, Bool.false_eq_true, ↓reduceIte]
        rw [Nat.add_zero]
        exact ih _ j

def tmask (n : ℕ) : ℕ := 2 ^ (2 ^ n) - 1

theorem testBit_tmask {n k : ℕ} (hk : k < 2 ^ n) : (tmask n).testBit k = true := by
  simp [tmask, Nat.testBit_two_pow_sub_one, hk]

theorem tmask_lt (m : ℕ) : tmask m < 2 ^ (2 ^ m) := by
  unfold tmask
  exact Nat.sub_lt (Nat.two_pow_pos _) Nat.one_pos

def icol (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | m + 1 => 2 ^ (2 ^ m) * (if m = i then tmask m else icol i m) + icol i m

theorem icol_lt (i : ℕ) : ∀ m, icol i m < 2 ^ (2 ^ m) := by
  intro m
  induction m with
  | zero => simp [icol]
  | succ m ih =>
    have hp : 2 ^ (2 ^ (m + 1)) = 2 ^ (2 ^ m) * 2 ^ (2 ^ m) := by
      rw [pow_succ, pow_mul, sq]
    have hu : (if m = i then tmask m else icol i m) < 2 ^ (2 ^ m) := by
      split
      · exact tmask_lt m
      · exact ih
    rw [hp, icol]
    calc 2 ^ 2 ^ m * (if m = i then tmask m else icol i m) + icol i m
        < 2 ^ 2 ^ m * (if m = i then tmask m else icol i m) + 2 ^ 2 ^ m := by omega
      _ = 2 ^ 2 ^ m * ((if m = i then tmask m else icol i m) + 1) := by ring
      _ ≤ 2 ^ 2 ^ m * 2 ^ 2 ^ m := Nat.mul_le_mul_left _ hu

theorem testBit_icol (i : ℕ) : ∀ m r, r < 2 ^ m → (icol i m).testBit r = r.testBit i := by
  intro m
  induction m with
  | zero =>
    intro r hr
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    simp [icol]
  | succ m ih =>
    intro r hr
    rw [icol, Nat.testBit_two_pow_mul_add _ (icol_lt i m)]
    split
    · next h => exact ih r h
    · next h =>
      obtain ⟨r', rfl⟩ : ∃ r', r = 2 ^ m + r' := ⟨r - 2 ^ m, by omega⟩
      have hr' : r' < 2 ^ m := by rw [pow_succ] at hr; omega
      rw [Nat.add_sub_cancel_left]
      split
      · next hmi =>
        subst hmi
        rw [testBit_tmask hr', Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr']
        rfl
      · next hmi =>
        rw [ih _ hr']
        rcases Nat.lt_or_gt_of_ne hmi with hlt | hgt
        · rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hr' (Nat.pow_le_pow_right (by norm_num) hlt.le)),
            Nat.testBit_lt_two_pow]
          calc 2 ^ m + r' < 2 ^ m + 2 ^ m := by omega
            _ = 2 ^ (m + 1) := by ring
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hlt
        · rw [Nat.testBit_two_pow_add_gt hgt]

def ttCols (n : ℕ) : List ℕ := List.ofFn fun i : Fin n => icol i.val n

theorem ttCols_bit {n : ℕ} (x : Fin n → Bool) (j : ℕ) :
    ((ttCols n).getD j 0).testBit (tableIndex x) = (List.ofFn x).getD j false := by
  by_cases hj : j < n
  · rw [ttCols, List.getD_eq_getElem _ _ (by simpa using hj), List.getD_eq_getElem _ _ (by simpa using hj)]
    simp only [List.getElem_ofFn]
    rw [testBit_icol j n _ (tableIndex_lt x)]
    exact testBit_tableIndex x ⟨j, hj⟩
  · rw [List.getD_eq_default _ _ (by simp [ttCols]; omega), List.getD_eq_default _ _ (by simp; omega)]
    simp

def tcap (n D : ℕ) (C : Circuit) : Bool := decide (n + C.gates.length ≤ 2 ^ D)

theorem tt_bit {n : ℕ} (D : ℕ) (C : Circuit) (hg : aonB C = true) (hsz : tcap n D C = true)
    (o : ℕ) (x : Fin n → Bool) :
    (wcol (tmask n) D C (ttCols n) o).testBit (tableIndex x) = (C.wires (List.ofFn x)).getD o false := by
  have hcap : (ttCols n).length + C.gates.length ≤ 2 ^ D := by
    have h3 : n + C.gates.length ≤ 2 ^ D := of_decide_eq_true hsz
    simpa [ttCols] using h3
  exact wcol_bit (testBit_tmask (tableIndex_lt x)) C (ttCols n) (List.ofFn x) hg (by simp [ttCols])
    (ttCols_bit x) hcap o

def bitsIn (n k : ℕ) : Fin n → Bool := fun i => k.testBit i

theorem bitsIn_tableIndex {n : ℕ} (x : Fin n → Bool) : bitsIn n (tableIndex x) = x := by
  funext i
  exact testBit_tableIndex x i

def allFrom (t : ℕ → Bool) : ℕ → ℕ → Bool
  | 0, a => t a
  | m + 1, a => allFrom t m a && allFrom t m (a + 2 ^ m)

theorem allFrom_spec (t : ℕ → Bool) :
    ∀ (m a : ℕ), allFrom t m a = true → ∀ r, r < 2 ^ m → t (a + r) = true := by
  intro m
  induction m with
  | zero =>
    intro a h r hr
    have hr0 : r = 0 := by simpa using hr
    subst hr0
    simpa [allFrom] using h
  | succ m ih =>
    intro a h r hr
    simp only [allFrom, Bool.and_eq_true] at h
    by_cases hr' : r < 2 ^ m
    · exact ih a h.1 r hr'
    · have h2 := ih (a + 2 ^ m) h.2 (r - 2 ^ m) (by rw [pow_succ] at hr; omega)
      have e : a + 2 ^ m + (r - 2 ^ m) = a + r := by omega
      rwa [e] at h2

def ttOK (n D : ℕ) (C : Circuit) (o : ℕ) (f : (Fin n → Bool) → Bool) : Bool :=
  allFrom (fun a => (wcol (tmask n) D C (ttCols n) o).testBit a == f (bitsIn n a)) n 0

theorem wire_of_enum {n : ℕ} (D : ℕ) (C : Circuit) (o : ℕ) (f : (Fin n → Bool) → Bool)
    (hg : aonB C = true) (hsz : tcap n D C = true) (h : ttOK n D C o f = true) :
    ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD o false = f x := by
  intro x
  have h1 := allFrom_spec _ n 0 h (tableIndex x) (tableIndex_lt x)
  simp only [Nat.zero_add, bitsIn_tableIndex, beq_iff_eq] at h1
  rw [← tt_bit D C hg hsz o x]
  exact h1

theorem eval_of_enum {n : ℕ} (D : ℕ) (C : Circuit) (f : (Fin n → Bool) → Bool)
    (hg : aonB C = true) (hsz : tcap n D C = true) (h : ttOK n D C C.output f = true) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x :=
  wire_of_enum D C C.output f hg hsz h

theorem wire_of_expr {n : ℕ} (D : ℕ) (C : Circuit) (o E : ℕ) (f : (Fin n → Bool) → Bool)
    (hg : aonB C = true) (hsz : tcap n D C = true)
    (h : (wcol (tmask n) D C (ttCols n) o == E) = true)
    (hE : ∀ x : Fin n → Bool, E.testBit (tableIndex x) = f x) :
    ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD o false = f x := by
  intro x
  rw [← tt_bit D C hg hsz o x, beq_iff_eq.mp h]
  exact hE x

theorem eval_of_expr {n : ℕ} (D : ℕ) (C : Circuit) (E : ℕ) (f : (Fin n → Bool) → Bool)
    (hg : aonB C = true) (hsz : tcap n D C = true)
    (h : (wcol (tmask n) D C (ttCols n) C.output == E) = true)
    (hE : ∀ x : Fin n → Bool, E.testBit (tableIndex x) = f x) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x :=
  wire_of_expr D C C.output E f hg hsz h hE

def vcol (n : ℕ) (i : Fin n) : ℕ := icol i.val n

def ncol (n a : ℕ) : ℕ := tmask n ^^^ a

theorem vcol_bit {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (vcol n i).testBit (tableIndex x) = x i := by
  rw [vcol, testBit_icol i.val n _ (tableIndex_lt x)]
  exact testBit_tableIndex x i

theorem ncol_bit {n : ℕ} (x : Fin n → Bool) (a : ℕ) :
    (ncol n a).testBit (tableIndex x) = !(a.testBit (tableIndex x)) := by
  rw [ncol, Nat.testBit_xor, testBit_tmask (tableIndex_lt x)]
  simp

theorem tmask_bit {n : ℕ} (x : Fin n → Bool) : (tmask n).testBit (tableIndex x) = true :=
  testBit_tmask (tableIndex_lt x)

theorem and_all {α : Type} {p q : α → Prop} (hp : ∀ x, p x) (hq : ∀ x, q x) : ∀ x, p x ∧ q x :=
  fun x => ⟨hp x, hq x⟩
