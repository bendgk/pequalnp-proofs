def tget : ℕ → BinaryTree ℕ → ℕ → ℕ
  | _, BinaryTree.nil, _ => 0
  | 0, BinaryTree.node v _ _, _ => v
  | d + 1, BinaryTree.node _ l r, i => if i % 2 = 0 then tget d l (i / 2) else tget d r (i / 2)

def tset : ℕ → BinaryTree ℕ → ℕ → ℕ → BinaryTree ℕ
  | 0, _, _, v => BinaryTree.node v BinaryTree.nil BinaryTree.nil
  | d + 1, BinaryTree.nil, i, v =>
    if i % 2 = 0 then BinaryTree.node 0 (tset d BinaryTree.nil (i / 2) v) BinaryTree.nil
    else BinaryTree.node 0 BinaryTree.nil (tset d BinaryTree.nil (i / 2) v)
  | d + 1, BinaryTree.node _ l r, i, v =>
    if i % 2 = 0 then BinaryTree.node 0 (tset d l (i / 2) v) r
    else BinaryTree.node 0 l (tset d r (i / 2) v)

theorem tget_nil (d i : ℕ) : tget d BinaryTree.nil i = 0 := by
  cases d <;> simp [tget]

theorem tget_tset : ∀ (d : ℕ) (t : BinaryTree ℕ) (i j v : ℕ), i < 2 ^ d → j < 2 ^ d →
    tget d (tset d t i v) j = if i = j then v else tget d t j := by
  intro d
  induction d with
  | zero =>
    intro t i j v hi hj
    have hi0 : i = 0 := by simpa using hi
    have hj0 : j = 0 := by simpa using hj
    subst hi0
    subst hj0
    simp [tset, tget]
  | succ d ih =>
    intro t i j v hi hj
    have hi2 : i / 2 < 2 ^ d := by rw [pow_succ] at hi; omega
    have hj2 : j / 2 < 2 ^ d := by rw [pow_succ] at hj; omega
    cases t with
    | nil =>
      by_cases hpi : i % 2 = 0 <;> by_cases hpj : j % 2 = 0
      · simp only [tset, hpi, ite_true, tget, hpj, ih _ _ _ _ hi2 hj2, tget_nil]
        by_cases e : i = j
        · simp [e]
        · have hne : i / 2 ≠ j / 2 := by omega
          simp [e, hne]
      · simp only [tset, hpi, ite_true, tget, hpj, ite_false, tget_nil]
        have hne : i ≠ j := by omega
        simp [hne]
      · simp only [tset, hpi, ite_false, tget, hpj, ite_true, tget_nil]
        have hne : i ≠ j := by omega
        simp [hne]
      · simp only [tset, hpi, ite_false, tget, hpj, ih _ _ _ _ hi2 hj2, tget_nil]
        by_cases e : i = j
        · simp [e]
        · have hne : i / 2 ≠ j / 2 := by omega
          simp [e, hne]
    | node a l r =>
      by_cases hpi : i % 2 = 0 <;> by_cases hpj : j % 2 = 0
      · simp only [tset, hpi, ite_true, tget, hpj, ih _ _ _ _ hi2 hj2]
        by_cases e : i = j
        · simp [e]
        · have hne : i / 2 ≠ j / 2 := by omega
          simp [e, hne]
      · simp only [tset, hpi, ite_true, tget, hpj, ite_false]
        have hne : i ≠ j := by omega
        simp [hne]
      · simp only [tset, hpi, ite_false, tget, hpj, ite_true]
        have hne : i ≠ j := by omega
        simp [hne]
      · simp only [tset, hpi, ite_false, tget, hpj, ih _ _ _ _ hi2 hj2]
        by_cases e : i = j
        · simp [e]
        · have hne : i / 2 ≠ j / 2 := by omega
          simp [e, hne]

def rd (D : ℕ) (t : BinaryTree ℕ) (i : ℕ) : ℕ := if i < 2 ^ D then tget D t i else 0

def push (D : ℕ) (st : BinaryTree ℕ × ℕ) (c : ℕ) : BinaryTree ℕ × ℕ := (tset D st.1 st.2 c, st.2 + 1)

def gcol (M D : ℕ) (g : Gate) (t : BinaryTree ℕ) : ℕ :=
  match g.op with
  | GateOp.and => (g.inputs.map fun a => rd D t a).foldr (fun p q => p &&& q) M
  | GateOp.or => (g.inputs.map fun a => rd D t a).foldr (fun p q => p ||| q) 0
  | GateOp.not => M ^^^ (g.inputs.map fun a => rd D t a).headD 0
  | _ => 0

def run (M D : ℕ) (gs : List Gate) (init : List ℕ) : BinaryTree ℕ × ℕ :=
  gs.foldl (fun st g => push D st (gcol M D g st.1)) (init.foldl (push D) (BinaryTree.nil, 0))

def wcol (M D : ℕ) (C : Circuit) (init : List ℕ) (o : ℕ) : ℕ := rd D (run M D C.gates init).1 o

def isAON : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | GateOp.not => true
  | _ => false

def isAO : GateOp → Bool
  | GateOp.and => true
  | GateOp.or => true
  | _ => false

def aonB (C : Circuit) : Bool := C.gates.all fun g => isAON g.op

def fanInTwoB (C : Circuit) : Bool :=
  C.gates.all fun g => isAON g.op && decide (g.inputs.length ≤ 2)

def monotone2B (C : Circuit) : Bool :=
  C.gates.all fun g => isAO g.op && decide (g.inputs.length ≤ 2)

theorem fanInTwoB_sound {C : Circuit} (h : fanInTwoB C = true) : FanInTwo C := by
  intro g hg
  have h0 := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
  refine ⟨?_, h0.2⟩
  have h1 := h0.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [isAON]

theorem monotone2B_sound {C : Circuit} (h : monotone2B C = true) : Monotone2 C := by
  intro g hg
  have h0 := List.all_eq_true.mp h g hg
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h0
  refine ⟨?_, h0.2⟩
  have h1 := h0.1
  cases hop : g.op <;> rw [hop] at h1 <;> simp_all [isAO]

def Agree (k D : ℕ) (st : BinaryTree ℕ × ℕ) (w : List Bool) : Prop :=
  st.2 = w.length ∧ ∀ j, (rd D st.1 j).testBit k = w.getD j false

theorem agree_push {k D : ℕ} {st : BinaryTree ℕ × ℕ} {w : List Bool} {c : ℕ} {b : Bool}
    (h : Agree k D st w) (hl : w.length < 2 ^ D) (hc : c.testBit k = b) :
    Agree k D (push D st c) (w ++ [b]) := by
  obtain ⟨hn, hr⟩ := h
  refine ⟨by simp [push, hn], fun j => ?_⟩
  simp only [push, rd]
  by_cases hj : j < 2 ^ D
  · rw [ite_eq_left hj, tget_tset D _ _ _ _ (hn ▸ hl) hj]
    rcases lt_trichotomy j w.length with h1 | h1 | h1
    · have hne : st.2 ≠ j := by omega
      rw [ite_eq_right hne, List.getD_append _ _ _ _ h1]
      have h2 := hr j
      simp only [rd, ite_eq_left hj] at h2
      exact h2
    · subst h1
      rw [ite_eq_left hn, List.getD_append_right _ _ _ _ le_rfl]
      simp [hc]
    · have hne : st.2 ≠ j := by omega
      rw [ite_eq_right hne, List.getD_eq_default _ _ (by simp; omega)]
      have h2 := hr j
      simp only [rd, ite_eq_left hj] at h2
      rw [h2, List.getD_eq_default _ _ (by omega)]
  · rw [ite_eq_right hj, List.getD_eq_default _ _ (by simp; omega)]
    simp

theorem foldr_and_bit {k M : ℕ} (hM : M.testBit k = true) (l : List ℕ) :
    (l.foldr (fun p q => p &&& q) M).testBit k = (l.map fun c => c.testBit k).all id := by
  induction l with
  | nil => simp [hM]
  | cons c l ih => simp [ih]

theorem foldr_or_bit {k : ℕ} (l : List ℕ) :
    (l.foldr (fun p q => p ||| q) 0).testBit k = (l.map fun c => c.testBit k).any id := by
  induction l with
  | nil => simp
  | cons c l ih => simp [ih]

theorem gcol_bit {k M D : ℕ} (hM : M.testBit k = true) {st : BinaryTree ℕ × ℕ} {w : List Bool}
    (h : Agree k D st w) (g : Gate) (hg : isAON g.op = true) :
    (gcol M D g st.1).testBit k = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have hmap : ((g.inputs.map fun a => rd D st.1 a).map fun c => c.testBit k)
      = g.inputs.map fun i => w.getD i false := by
    rw [List.map_map]
    exact List.map_congr_left (fun a _ => h.2 a)
  cases hop : g.op with
  | and =>
    simp only [gcol, hop, GateOp.eval]
    rw [foldr_and_bit hM, hmap]
  | or =>
    simp only [gcol, hop, GateOp.eval]
    rw [foldr_or_bit, hmap]
  | not =>
    simp only [gcol, hop, GateOp.eval]
    rw [Nat.testBit_xor, hM, ← hmap]
    cases g.inputs <;> simp
  | mod q =>
    rw [hop] at hg
    simp [isAON] at hg
  | maj =>
    rw [hop] at hg
    simp [isAON] at hg

theorem agree_gates {k M D : ℕ} (hM : M.testBit k = true) :
    ∀ (gs : List Gate) (st : BinaryTree ℕ × ℕ) (w : List Bool), (∀ g ∈ gs, isAON g.op = true) →
      Agree k D st w → w.length + gs.length ≤ 2 ^ D →
      Agree k D (gs.foldl (fun st g => push D st (gcol M D g st.1)) st)
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w) := by
  intro gs
  induction gs with
  | nil =>
    intro st w _ h _
    exact h
  | cons g gs ih =>
    intro st w hg h hl
    simp only [List.foldl_cons]
    have hl1 : w.length < 2 ^ D := by
      simp only [List.length_cons] at hl
      omega
    refine ih _ _ (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
      (agree_push h hl1 (gcol_bit hM h g (hg g List.mem_cons_self))) ?_
    simp only [List.length_cons, List.length_append, List.length_nil] at hl ⊢
    omega

theorem agree_inputs {k D : ℕ} :
    ∀ (cs : List ℕ) (bs : List Bool) (st : BinaryTree ℕ × ℕ) (w : List Bool),
      Agree k D st w → cs.length = bs.length →
      (∀ j, (cs.getD j 0).testBit k = bs.getD j false) →
      w.length + cs.length ≤ 2 ^ D → Agree k D (cs.foldl (push D) st) (w ++ bs) := by
  intro cs
  induction cs with
  | nil =>
    intro bs st w h hlen _ _
    cases bs with
    | nil => simpa using h
    | cons b bs => simp at hlen
  | cons c cs ih =>
    intro bs st w h hlen hb hl
    cases bs with
    | nil => simp at hlen
    | cons b bs =>
      have h0 : c.testBit k = b := by simpa using hb 0
      have hl1 : w.length < 2 ^ D := by
        simp only [List.length_cons] at hl
        omega
      have hlen1 : cs.length = bs.length := by simpa using hlen
      have hl2 : (w ++ [b]).length + cs.length ≤ 2 ^ D := by
        simp only [List.length_cons, List.length_append, List.length_nil] at hl ⊢
        omega
      have h1 := ih bs (push D st c) (w ++ [b]) (agree_push h hl1 h0) hlen1
        (fun j => by simpa using hb (j + 1)) hl2
      simpa using h1

theorem wcol_bit {k M D : ℕ} (hM : M.testBit k = true) (C : Circuit) (init : List ℕ) (x : List Bool)
    (hg : aonB C = true) (hlen : init.length = x.length)
    (hin : ∀ j, (init.getD j 0).testBit k = x.getD j false)
    (hsz : init.length + C.gates.length ≤ 2 ^ D) (o : ℕ) :
    (wcol M D C init o).testBit k = (C.wires x).getD o false := by
  have h0 : Agree k D (BinaryTree.nil, 0) [] := ⟨rfl, fun j => by simp [rd, tget_nil]⟩
  have h1 := agree_inputs init x _ [] h0 hlen hin (by simp only [List.length_nil]; omega)
  simp only [List.nil_append] at h1
  have h2 := agree_gates hM C.gates _ x (fun g hg' => List.all_eq_true.mp hg g hg') h1
    (by rw [← hlen]; exact hsz)
  exact h2.2 o
