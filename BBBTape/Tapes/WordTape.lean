import BBBTape.Core.Tape

namespace BBBTape

structure WordTape where
  left  : List UInt64
  cur   : UInt64
  off   : UInt8
  right : List UInt64
  h_off : off < 64

namespace WordTape

def blank : WordTape := ⟨[], 0, 0, [], by decide⟩

@[inline] def wordBit (w b : UInt64) : Bool :=
  ((w >>> b) &&& 1) == 1

@[inline] def head (t : WordTape) : Bool :=
  wordBit t.cur t.off.toUInt64

@[inline] def flip (t : WordTape) : WordTape :=
  ⟨t.left, t.cur ^^^ (1 <<< t.off.toUInt64), t.off, t.right, t.h_off⟩

@[inline] def moveR (t : WordTape) : WordTape :=
  if h : t.off < 63 then
    ⟨t.left, t.cur, t.off + 1, t.right, by
      show (t.off.toNat + 1) % 256 < 64
      have : t.off.toNat < 63 := h
      omega⟩
  else
    match t.right with
    | []      => ⟨t.cur :: t.left, 0, 0, [], by decide⟩
    | w :: ws => ⟨t.cur :: t.left, w, 0, ws, by decide⟩

@[inline] def moveL (t : WordTape) : WordTape :=
  if h : 0 < t.off then
    ⟨t.left, t.cur, t.off - 1, t.right, by
      show (t.off - 1).toNat < 64
      have h1 : 0 < t.off.toNat := h
      have h2 : t.off.toNat < 64 := t.h_off
      rw [UInt8.toNat_sub_of_le _ _ h]
      omega⟩
  else
    match t.left with
    | []      => ⟨[], 0, 63, t.cur :: t.right, by decide⟩
    | w :: ws => ⟨ws, w, 63, t.cur :: t.right, by decide⟩

def cellsAt (left : List UInt64) (cur : UInt64) (right : List UInt64) (pos : Int) : Bool :=
  if 0 ≤ pos then
    let p := pos.toNat
    if p < 64 then wordBit cur p.toUInt64
    else wordBit (right.getD ((p - 64) / 64) 0) (p % 64).toUInt64
  else
    let d := (-pos).toNat - 1
    wordBit (left.getD (d / 64) 0) (63 - d % 64).toUInt64

@[inline] def cells (t : WordTape) : Int → Bool
  | .ofNat 0 => t.head
  | i        => cellsAt t.left t.cur t.right ((t.off.toNat : Int) + i)

theorem wordBit_nat_eq_testBit (w : UInt64) (b : Nat) (h : b < 64) :
    wordBit w b.toUInt64 = w.toNat.testBit b := by
  have hb : b.toUInt64.toNat = b := by
    show b % 2 ^ 64 = b
    exact Nat.mod_eq_of_lt (by omega)
  have hmod : b % 64 = b := Nat.mod_eq_of_lt h
  have htoNat : (w >>> b.toUInt64 &&& 1).toNat = (w.toNat >>> b) % 2 := by
    rw [UInt64.toNat_and, UInt64.toNat_shiftRight, hb, hmod]
    exact Nat.and_one_is_mod (w.toNat >>> b)
  simp only [wordBit, Nat.testBit, Nat.and_comm 1, Nat.and_one_is_mod]
  rcases Nat.mod_two_eq_zero_or_one (w.toNat >>> b) with h0 | h1
  · have hne : (w >>> b.toUInt64 &&& 1) ≠ 1 := fun he => by
      have h2 := congrArg UInt64.toNat he
      rw [htoNat, h0] at h2
      contradiction
    simp [h0, hne]
  · have heq : (w >>> b.toUInt64 &&& 1) = 1 :=
      UInt64.eq_of_toBitVec_eq (BitVec.eq_of_toNat_eq (htoNat.trans h1))
    simp [h1, heq]

theorem wordBit_eq_testBit (w : UInt64) (b : UInt8) (h : b < 64) :
    wordBit w b.toUInt64 = w.toNat.testBit b.toNat := by
  have hb : b.toUInt64 = b.toNat.toUInt64 := by
    apply UInt64.eq_of_toBitVec_eq
    apply BitVec.eq_of_toNat_eq
    show b.toUInt64.toNat = b.toNat % 2 ^ 64
    rw [UInt8.toNat_toUInt64]
    have : b.toNat < 64 := h
    exact (Nat.mod_eq_of_lt (by omega)).symm
  rw [hb]
  exact wordBit_nat_eq_testBit w b.toNat h

@[simp] theorem cellsAt_testBit (left : List UInt64) (cur : UInt64) (right : List UInt64) (pos : Int) :
    cellsAt left cur right pos =
      if 0 ≤ pos then
        let p := pos.toNat
        if p < 64 then cur.toNat.testBit p
        else (right.getD ((p - 64) / 64) 0).toNat.testBit (p % 64)
      else
        let d := (-pos).toNat - 1
        (left.getD (d / 64) 0).toNat.testBit (63 - d % 64) := by
  unfold cellsAt
  split
  · dsimp only
    split
    · next hp => exact wordBit_nat_eq_testBit cur pos.toNat hp
    · exact wordBit_nat_eq_testBit _ _ (Nat.mod_lt _ (by decide))
  · dsimp only
    exact wordBit_nat_eq_testBit _ _ (by omega)

theorem cells_eq (t : WordTape) (i : Int) :
    t.cells i = cellsAt t.left t.cur t.right ((t.off.toNat : Int) + i) := by
  cases i with
  | ofNat n =>
    cases n with
    | zero =>
      change t.head = cellsAt t.left t.cur t.right ((t.off.toNat : Int) + 0)
      have hoff : t.off.toNat < 64 := t.h_off
      simp [head, wordBit_eq_testBit t.cur t.off t.h_off, hoff]
    | succ n => rfl
  | negSucc n => rfl

theorem testBit_xor_one_shift (w : UInt64) (b : UInt8) (hb : b < 64) (p : Nat) :
    (w ^^^ (1 <<< b.toUInt64)).toNat.testBit p =
      if p = b.toNat then !w.toNat.testBit p else w.toNat.testBit p := by
  have hb1 : b.toUInt64.toNat = b.toNat := UInt8.toNat_toUInt64 b
  have hb2 : b.toNat < 64 := hb
  have hmod : b.toNat % 64 = b.toNat := Nat.mod_eq_of_lt hb2
  have hpow : (1 <<< b.toUInt64).toNat = 2 ^ b.toNat := by
    rw [UInt64.toNat_shiftLeft, hb1, hmod]
    have h1 : (1 : UInt64).toNat <<< b.toNat = 2 ^ b.toNat := by
      change 1 <<< b.toNat = 2 ^ b.toNat
      rw [Nat.shiftLeft_eq, Nat.one_mul]
    rw [h1]
    exact Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) hb2)
  rw [UInt64.toNat_xor, hpow, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases h : b.toNat = p
  · subst h; simp
  · have hne : p ≠ b.toNat := fun h' => h h'.symm
    simp [h, hne]

theorem getD_tail_u64 (l : List UInt64) (n : Nat) :
    l.tail.getD n 0 = l.getD (n + 1) 0 := by
  cases l <;> simp

theorem headD_eq_getD_u64 (l : List UInt64) :
    l.headD 0 = l.getD 0 0 := by
  cases l <;> rfl

theorem cellsAt_shiftR (left : List UInt64) (cur : UInt64) (right : List UInt64) (pos : Int) :
    cellsAt (cur :: left) (right.headD 0) right.tail pos =
      cellsAt left cur right (pos + 64) := by
  simp only [cellsAt_testBit]
  by_cases h1 : 0 ≤ pos
  · have h2 : 0 ≤ pos + 64 := by omega
    simp only [h1, h2, ↓reduceIte]
    have hp : (pos + 64).toNat = pos.toNat + 64 := by omega
    have hge : ¬ (pos.toNat + 64 < 64) := by omega
    simp only [hp, hge, ↓reduceIte]
    by_cases h3 : pos.toNat < 64
    · have hdiv1 : (pos.toNat + 64 - 64) / 64 = 0 := by omega
      have hmod : (pos.toNat + 64) % 64 = pos.toNat := by omega
      simp only [h3, ↓reduceIte, hdiv1, hmod, headD_eq_getD_u64]
    · have hdiv : (pos.toNat + 64 - 64) / 64 = (pos.toNat - 64) / 64 + 1 := by omega
      have hmod : (pos.toNat + 64) % 64 = pos.toNat % 64 := by omega
      simp only [h3, ↓reduceIte, getD_tail_u64, hdiv, hmod]
  · simp only [h1, ↓reduceIte]
    by_cases h2 : 0 ≤ pos + 64
    · have hlt : (pos + 64).toNat < 64 := by omega
      have hddiv : ((-pos).toNat - 1) / 64 = 0 := by omega
      have hdmod : 63 - ((-pos).toNat - 1) % 64 = (pos + 64).toNat := by omega
      simp [h2, hlt, hddiv, hdmod]
    · have hddiv : ((-pos).toNat - 1) / 64 = ((-(pos + 64)).toNat - 1) / 64 + 1 := by omega
      have hdmod : ((-pos).toNat - 1) % 64 = ((-(pos + 64)).toNat - 1) % 64 := by omega
      simp [h2, hddiv, hdmod]

theorem cellsAt_shiftL (left : List UInt64) (cur : UInt64) (right : List UInt64) (pos : Int) :
    cellsAt left.tail (left.headD 0) (cur :: right) (pos + 63) =
      cellsAt left cur right (pos - 1) := by
  have h := (cellsAt_shiftR left.tail (left.headD 0) (cur :: right) (pos - 1)).symm
  have h64 : pos - 1 + 64 = pos + 63 := by omega
  rw [h64] at h
  rw [h]
  cases left with
  | nil =>
    simp only [List.headD, List.tail, cellsAt_testBit]
    split
    · rfl
    · next hneg =>
      rcases Nat.eq_zero_or_pos (((-(pos - 1)).toNat - 1) / 64) with h0 | hpos
      · simp [h0]
      · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        simp [hk]
  | cons x xs => rfl

theorem cells_blank (i : Int) : blank.cells i = false := by
  rw [cells_eq]
  simp only [blank, UInt8.toNat_zero, Int.ofNat_zero, Int.zero_add, cellsAt_testBit]
  split
  · split <;> simp
  · simp

theorem cells_flip (t : WordTape) (i : Int) :
    t.flip.cells i = if i = 0 then !t.cells 0 else t.cells i := by
  rw [cells_eq, cells_eq, cells_eq]
  simp only [flip, Int.add_zero]
  have hoff : t.off.toNat < 64 := t.h_off
  by_cases hi : i = 0
  · subst hi
    simp only [Int.add_zero, ↓reduceIte, cellsAt_testBit]
    have h0 : (0 : Int) ≤ (t.off.toNat : Int) := by omega
    have hnat : (t.off.toNat : Int).toNat = t.off.toNat := Int.toNat_natCast t.off.toNat
    simp only [h0, hnat, hoff, ↓reduceIte]
    rw [testBit_xor_one_shift t.cur t.off t.h_off]
    simp
  · simp only [hi, ↓reduceIte, cellsAt_testBit]
    by_cases hpos : 0 ≤ (t.off.toNat : Int) + i
    · simp only [hpos, ↓reduceIte]
      by_cases hlt : ((t.off.toNat : Int) + i).toNat < 64
      · have hne : ((t.off.toNat : Int) + i).toNat ≠ t.off.toNat := by omega
        simp only [hlt, ↓reduceIte]
        rw [testBit_xor_one_shift t.cur t.off t.h_off]
        simp [hne]
      · simp [hlt]
    · simp [hpos]

theorem cells_moveR (t : WordTape) (i : Int) :
    t.moveR.cells i = t.cells (i + 1) := by
  rw [cells_eq, cells_eq]
  unfold moveR
  split
  · next h =>
    have hlt : t.off.toNat < 63 := h
    have hadd : ((t.off + 1).toNat : Int) + i = (t.off.toNat : Int) + (i + 1) := by
      change (((t.off.toNat + 1) % 256 : Nat) : Int) + i = (t.off.toNat : Int) + (i + 1)
      omega
    dsimp only
    rw [hadd]
  · next h =>
    have hge : ¬ (t.off.toNat < 63) := h
    have hlt : t.off.toNat < 64 := t.h_off
    have hoff : t.off.toNat = 63 := by omega
    have hmatch :
        (match t.right with
        | [] => (⟨t.cur :: t.left, 0, 0, [], by decide⟩ : WordTape)
        | w :: ws => ⟨t.cur :: t.left, w, 0, ws, by decide⟩) =
          ⟨t.cur :: t.left, t.right.headD 0, 0, t.right.tail, by decide⟩ := by
      cases t.right <;> rfl
    rw [hmatch]
    dsimp only
    simp only [UInt8.toNat_zero, Int.ofNat_zero, Int.zero_add]
    rw [cellsAt_shiftR, hoff]
    have h64 : i + 64 = ((63 : Nat) : Int) + (i + 1) := by omega
    rw [h64]

theorem cells_moveL (t : WordTape) (i : Int) :
    t.moveL.cells i = t.cells (i - 1) := by
  rw [cells_eq, cells_eq]
  unfold moveL
  split
  · next h =>
    have h1 : 0 < t.off.toNat := h
    have hsub : ((t.off - 1).toNat : Int) + i = (t.off.toNat : Int) + (i - 1) := by
      rw [UInt8.toNat_sub_of_le _ _ h]
      change ((t.off.toNat - 1 : Nat) : Int) + i = (t.off.toNat : Int) + (i - 1)
      omega
    dsimp only
    rw [hsub]
  · next h =>
    have hle : ¬ (0 < t.off.toNat) := h
    have hoff : t.off.toNat = 0 := by omega
    have hcomm : (63 : Int) + i = i + 63 := by omega
    have hmatch :
        (match t.left with
        | [] => (⟨[], 0, 63, t.cur :: t.right, by decide⟩ : WordTape)
        | w :: ws => ⟨ws, w, 63, t.cur :: t.right, by decide⟩) =
          ⟨t.left.tail, t.left.headD 0, 63, t.cur :: t.right, by decide⟩ := by
      cases t.left <;> rfl
    rw [hmatch]
    dsimp only
    change cellsAt t.left.tail (t.left.headD 0) (t.cur :: t.right) ((63 : Int) + i) = _
    rw [hcomm, cellsAt_shiftL, hoff]
    simp

@[inline] instance : Tape WordTape where
  cells       := cells
  blank       := blank
  flip        := flip
  moveL       := moveL
  moveR       := moveR
  cells_blank := cells_blank
  cells_flip  := cells_flip
  cells_moveL := cells_moveL
  cells_moveR := cells_moveR

end WordTape

end BBBTape
