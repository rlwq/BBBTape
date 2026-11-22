import BBBTape.Solved.Known

namespace BBBTape

open scoped Program Machine

namespace RightCounter

open Known

def clrBody : Program := .flip (.left (.left ε))

def walkBody : Program := .right (.flip (.right ε))

def after : Program := .right (.flip (.loop walkBody (.flip (.left (.left ε)))))

def outer : Program := .loop (.loop clrBody after) ε

def prog : Program := .flip outer

theorem clearL (rest : Program) : ∀ (n : Nat) (f : Int → Bool) (p : Int),
    (∀ i : Nat, i < n → f (p - 2 * i) = true) → f (p - 2 * n) = false →
    ∃ (k : Nat) (g : Int → Bool),
      (Machine.mk (tp f p) (.loop clrBody rest)) ⇒ (k + 1) = some ⟨tp g (p - 2 * n), rest⟩ ∧
      ∀ x, g x = if p - 2 * n < x ∧ x ≤ p ∧ x % 2 = p % 2 then false else f x := by
  intro n
  induction n with
  | zero =>
    intro f p _ h
    have h0 : f p = false := by simpa using h
    refine ⟨0, f, run (step_loop_false h0 _ _) (by simp; rfl), fun x => ?_⟩
    split
    · omega
    · rfl
  | succ n ih =>
    intro f p h1 h
    have hp : f p = true := by simpa using h1 0 (by omega)
    obtain ⟨k, g, hs, hg⟩ := ih (flp f p) (p - 2)
      (fun i hi => by rw [flp_ne (by omega), ← h1 (i + 1) (by omega)]; congr 1; omega)
      (by rw [flp_ne (by omega), ← h]; congr 1; omega)
    refine ⟨k + 4, g, ?_, fun x => ?_⟩
    · refine run (step_loop_true hp _ _) (run (step_flip _ _ _) (run (step_left _ _ _)
        (run (step_left _ _ _) ?_)))
      rw [show p - 1 - 1 = p - 2 by omega, show p - 2 * ↑(n + 1) = p - 2 - 2 * ↑n by omega]
      exact hs
    · rw [hg x]
      by_cases hx : x = p
      · subst hx; rw [flp_eq, hp]
        split <;> split <;> first | rfl | omega
      · rw [flp_ne hx]
        split <;> split <;> first | rfl | omega

theorem walkR (rest : Program) : ∀ (m : Nat) (f : Int → Bool) (o : Int),
    (∀ i : Nat, i < m → f (o + 2 * i) = true) → f (o + 2 * m) = false →
    ∃ (k : Nat) (g : Int → Bool),
      (Machine.mk (tp f o) (.loop walkBody rest)) ⇒ (k + 1) = some ⟨tp g (o + 2 * m), rest⟩ ∧
      ∀ x, g x = if o < x ∧ x < o + 2 * m ∧ x % 2 ≠ o % 2 then !f x else f x := by
  intro m
  induction m with
  | zero =>
    intro f o _ h
    have h0 : f o = false := by simpa using h
    refine ⟨0, f, run (step_loop_false h0 _ _) (by simp; rfl), fun x => ?_⟩
    split
    · omega
    · rfl
  | succ m ih =>
    intro f o h1 h
    have ho : f o = true := by simpa using h1 0 (by omega)
    obtain ⟨k, g, hs, hg⟩ := ih (flp f (o + 1)) (o + 2)
      (fun i hi => by rw [flp_ne (by omega), ← h1 (i + 1) (by omega)]; congr 1; omega)
      (by rw [flp_ne (by omega), ← h]; congr 1; omega)
    refine ⟨k + 4, g, ?_, fun x => ?_⟩
    · refine run (step_loop_true ho _ _) (run (step_right _ _ _) (run (step_flip _ _ _)
        (run (step_right _ _ _) ?_)))
      rw [show o + 1 + 1 = o + 2 by omega, show o + 2 * ↑(m + 1) = o + 2 + 2 * ↑m by omega]
      exact hs
    · rw [hg x]
      by_cases hx : x = o + 1
      · subst hx; rw [flp_eq]
        split <;> split <;> first | rfl | omega
      · rw [flp_ne hx]
        split <;> split <;> first | rfl | omega

theorem iterB {f : Int → Bool} {p : Int} {j m : Nat}
    (hp : f p = true) (hj : ∀ i : Nat, i < j → f (p - 2 * i) = true) (hj' : f (p - 2 * j) = false)
    (ho : f (p - 2 * j + 1) = false)
    (hm : ∀ i : Nat, 1 ≤ i → i < m → f (p - 2 * j + 1 + 2 * i) = true)
    (hm' : f (p - 2 * j + 1 + 2 * m) = false) (hm1 : 1 ≤ m) :
    ∃ (k : Nat) (F : Int → Bool),
      (Machine.mk (tp f p) outer) ⇒ (k + 1) = some ⟨tp F (p - 2 * j + 2 * m - 1), outer⟩ ∧
      ∀ x, F x =
        if x = p - 2 * j + 1 ∨ x = p - 2 * j + 1 + 2 * m then true
        else if p - 2 * j + 1 < x ∧ x < p - 2 * j + 1 + 2 * m ∧ x % 2 = p % 2 then
          (if x ≤ p then true else !f x)
        else if p - 2 * j < x ∧ x ≤ p ∧ x % 2 = p % 2 then false
        else f x := by
  obtain ⟨k₁, g, hs₁, hg⟩ := clearL (after ++ outer) j f p hj hj'
  have hgo : ∀ x, x % 2 ≠ p % 2 → g x = f x := fun x hx => by
    rw [hg x]; split
    · omega
    · rfl
  obtain ⟨k₂, h, hs₂, hh⟩ := walkR (.flip (.left (.left outer))) m
    (flp g (p - 2 * j + 1)) (p - 2 * j + 1)
    (fun i hi => by
      cases i with
      | zero =>
        rw [show p - 2 * ↑j + 1 + 2 * ↑(0 : Nat) = p - 2 * ↑j + 1 by omega, flp_eq,
          hgo _ (by omega), ho]; rfl
      | succ i =>
        rw [flp_ne (by omega), hgo _ (by omega)]; exact hm (i + 1) (by omega) hi)
    (by rw [flp_ne (by omega), hgo _ (by omega)]; exact hm')
  refine ⟨k₁ + k₂ + 7, flp h (p - 2 * j + 1 + 2 * m), ?_, fun x => ?_⟩
  · refine run (step_loop_true hp _ _) ?_
    rw [show k₁ + k₂ + 7 = (k₁ + 1) + (k₂ + 6) by omega, Machine.steps_add]
    refine (congrArg (·.bind (·⇒(k₂ + 6))) hs₁).trans ?_
    simp only [Option.bind_some]
    refine run (step_right _ _ _) (run (step_flip _ _ _) ?_)
    rw [show k₂ + 4 = (k₂ + 1) + 3 by omega, Machine.steps_add]
    refine (congrArg (·.bind (·⇒3)) hs₂).trans ?_
    simp only [Option.bind_some]
    refine run (step_flip _ _ _) (run (step_left _ _ _) (run (step_left _ _ _) ?_))
    rw [show p - 2 * ↑j + 1 + 2 * ↑m - 1 - 1 = p - 2 * ↑j + 2 * ↑m - 1 by omega]
    rfl
  · by_cases h1 : x = p - 2 * j + 1 + 2 * m
    · subst h1
      rw [flp_eq, hh, flp_ne (by omega), hgo _ (by omega), hm']
      split
      · omega
      · split
        · rfl
        · omega
    · rw [flp_ne h1, hh x]
      by_cases h2 : x = p - 2 * j + 1
      · subst h2
        rw [flp_eq, hgo _ (by omega), ho]
        split
        · omega
        · split
          · rfl
          · omega
      · rw [flp_ne h2, hg x]
        repeat' split
        all_goals first | rfl | (exfalso; omega)

def dig (D : Int → Bool) (s x : Int) : Bool := D ((x - s) / 2)

def cons (b : Bool) (D : Int → Bool) : Int → Bool := fun k => if k = 0 then b else D (k - 1)

def shift (n : Nat) (D : Int → Bool) : Int → Bool := fun k => if k < n then false else D (k - n)

def Fin (D : Int → Bool) : Prop := ∃ N : Int, ∀ k, N ≤ k → D k = false

def G1 (c : Nat) (D : Int → Bool) (p : Int) (f : Int → Bool) : Prop :=
  ∀ x, f x = if x < p - 2 * c then false else if x ≤ p then true else if x = p + 1 then false
    else if x = p + 2 then true else dig D (p + 3) x

def G2 (c : Nat) (D : Int → Bool) (p : Int) (f : Int → Bool) : Prop :=
  ∀ x, f x = if x < p - 2 * c then false else if x ≤ p + 1 then true
    else dig (cons true D) (p + 2) x

def G3 (c : Nat) (D : Int → Bool) (p : Int) (f : Int → Bool) : Prop :=
  ∀ x, f x = if x < p - 2 * c then false else if x ≤ p + 2 then true else if x = p + 3 then false
    else dig D (p + 4) x

def G4 (c b : Nat) (D : Int → Bool) (p : Int) (f : Int → Bool) : Prop :=
  ∀ x, f x = if x < p - 2 * b - 2 * c - 2 then false else if x < p - 2 * b - 1 then true
    else if x < p then decide ((p - x) % 2 = 0) else if x = p then true else dig D (p + 1) x

def Inv (f : Int → Bool) (p : Int) : Prop :=
  ∃ (c : Nat) (D : Int → Bool), Fin D ∧
    (G1 c D p f ∨ G2 c D p f ∨ G3 c D p f ∨ ∃ b : Nat, G4 c b D p f)

theorem firstFalse : ∀ (n : Nat) (E : Int → Bool), E n = false →
    ∃ r : Nat, (∀ i : Int, 0 ≤ i → i < r → E i = true) ∧ E r = false := by
  intro n
  induction n with
  | zero => intro E h; exact ⟨0, fun i h0 h1 => by omega, by simpa using h⟩
  | succ n ih =>
    intro E h
    cases h0 : E 0 with
    | false => exact ⟨0, fun i a b => by omega, by simpa using h0⟩
    | true =>
      obtain ⟨r, hr, hr'⟩ := ih (fun k => E (k + 1)) (by simpa using h)
      refine ⟨r + 1, fun i a b => ?_, by simpa using hr'⟩
      by_cases hi : i = 0
      · subst hi; exact h0
      · have := hr (i - 1) (by omega) (by omega)
        simp only [Int.sub_add_cancel] at this
        exact this

theorem step1 {c : Nat} {D : Int → Bool} {p : Int} {f : Int → Bool} (hf : G1 c D p f) :
    ∃ (k : Nat) (F : Int → Bool),
      (Machine.mk (tp f p) outer) ⇒ (k + 1) = some ⟨tp F (p - 1), outer⟩ ∧ G2 c D (p - 1) F := by
  obtain ⟨k, F, hs, hF⟩ := iterB (j := c + 1) (m := c + 1) (f := f) (p := p)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (fun i hi => by rw [hf]; repeat' split
                    all_goals first | rfl | omega)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (fun i h1 h2 => by rw [hf]; repeat' split
                       all_goals first | rfl | omega)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (by omega)
  refine ⟨k, F, by rw [show p - 1 = p - 2 * ↑(c + 1) + 2 * ↑(c + 1) - 1 by omega]; exact hs,
    fun x => ?_⟩
  rw [hF x, hf x]
  simp only [dig, cons]
  repeat' split
  all_goals first | rfl | omega | (congr 1; omega) | simp_all

theorem step3 {c : Nat} {D : Int → Bool} {p : Int} {f : Int → Bool} (hf : G3 c D p f) :
    ∃ (k : Nat) (F : Int → Bool),
      (Machine.mk (tp f p) outer) ⇒ (k + 1) = some ⟨tp F (p + 1), outer⟩ ∧
        G1 (c + 1) D (p + 1) F := by
  obtain ⟨k, F, hs, hF⟩ := iterB (j := c + 1) (m := c + 2) (f := f) (p := p)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (fun i hi => by rw [hf]; repeat' split
                    all_goals first | rfl | omega)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (fun i h1 h2 => by rw [hf]; repeat' split
                       all_goals first | rfl | omega)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (by omega)
  refine ⟨k, F, by rw [show p + 1 = p - 2 * ↑(c + 1) + 2 * ↑(c + 2) - 1 by omega]; exact hs,
    fun x => ?_⟩
  rw [hF x, hf x]
  simp only [dig]
  repeat' split
  all_goals first | rfl | omega | (congr 1; omega) | simp_all

theorem step4 {c b : Nat} {D : Int → Bool} {p : Int} {f : Int → Bool} (hf : G4 c b D p f) :
    ∃ (k : Nat) (F : Int → Bool),
      (Machine.mk (tp f p) outer) ⇒ (k + 1) = some ⟨tp F (p - 2 * b - 3), outer⟩ ∧
        G3 c (shift b D) (p - 2 * b - 3) F := by
  obtain ⟨k, F, hs, hF⟩ := iterB (j := b + c + 2) (m := c + 1) (f := f) (p := p)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (fun i hi => by rw [hf]; repeat' split
                    all_goals first | rfl | omega | (simp; omega))
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (fun i h1 h2 => by rw [hf]; repeat' split
                       all_goals first | rfl | omega)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega | (simp; omega))
    (by omega)
  refine ⟨k, F, by
    rw [show p - 2 * ↑b - 3 = p - 2 * ↑(b + c + 2) + 2 * ↑(c + 1) - 1 by omega]; exact hs,
    fun x => ?_⟩
  rw [hF x, hf x]
  simp only [dig, shift]
  repeat' split
  all_goals first | rfl | omega | (congr 1; omega) | (simp; omega) | simp_all

set_option maxHeartbeats 2000000 in
theorem step2 {c : Nat} {D : Int → Bool} {p : Int} {f : Int → Bool} (hD : Fin D)
    (hf : G2 c D p f) :
    ∃ (k : Nat) (F : Int → Bool) (p' : Int) (b : Nat) (D' : Int → Bool),
      (Machine.mk (tp f p) outer) ⇒ (k + 1) = some ⟨tp F p', outer⟩ ∧ Fin D' ∧
        G4 (c + 1) b D' p' F := by
  obtain ⟨N, hN⟩ := hD
  obtain ⟨r, hr, hr'⟩ := firstFalse (N.toNat + 1) (cons true D) (by
    simp only [cons]; split
    · omega
    · exact hN _ (by omega))
  have hr0 : 0 < r := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    subst h0; simp [cons] at hr'
  have hE : ∀ x, p + 2 ≤ x → x < p + 2 + 2 * r → dig (cons true D) (p + 2) x = true :=
    fun x h1 h2 => hr _ (by omega) (by omega)
  have hE' : ∀ x, x = p + 2 + 2 * r ∨ x = p + 3 + 2 * r → dig (cons true D) (p + 2) x = false :=
    fun x hx => by unfold dig; rw [← hr']; congr 1; omega
  obtain ⟨k, F, hs, hF⟩ := iterB (j := c + 1) (m := c + r + 2) (f := f) (p := p)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (fun i hi => by rw [hf]; repeat' split
                    all_goals first | rfl | omega)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega)
    (fun i h1 h2 => by
      rw [hf]; repeat' split
      all_goals first | rfl | omega | exact hE _ (by omega) (by omega))
    (by rw [hf]; repeat' split
        all_goals first | rfl | omega | exact hE' _ (by omega))
    (by omega)
  refine ⟨k, F, p + 2 * r + 1, r - 1, cons true (fun k => cons true D (k + r + 1)),
    by rw [show p + 2 * ↑r + 1 = p - 2 * ↑(c + 1) + 2 * ↑(c + r + 2) - 1 by omega]; exact hs,
    ⟨max N 0 + 1, fun k hk => ?_⟩, fun x => ?_⟩
  · simp only [cons]; split
    · omega
    · split
      · omega
      · exact hN _ (by omega)
  · rw [hF x, hf x]
    by_cases hx : p + 2 ≤ x ∧ x < p + 2 + 2 * r
    · rw [hE x hx.1 hx.2]
      repeat' split
      all_goals first | rfl | omega | (simp; omega) | simp_all
    · by_cases hx' : x = p + 2 + 2 * r ∨ x = p + 3 + 2 * r
      · rw [hE' x hx']
        simp only [dig, cons]
        repeat' split
        all_goals first | rfl | (exfalso; omega) | (simp; omega) | (congr 1; omega)
      · by_cases hlo : x < p + 2
        · repeat' split
          all_goals first | rfl | (exfalso; omega) | (simp; omega)
        · have hd : dig (cons true D) (p + 2) x =
              dig (cons true (fun k => cons true D (k + r + 1))) (p + 2 * r + 1 + 1) x := by
            simp only [dig, cons]
            split
            · omega
            · split
              · omega
              · split
                · omega
                · congr 1; omega
          rw [← hd]
          repeat' split
          all_goals first | rfl | (exfalso; omega)

theorem iter {f : Int → Bool} {p : Int} (hi : Inv f p) :
    ∃ (k : Nat) (f' : Int → Bool) (p' : Int),
      (Machine.mk (tp f p) outer) ⇒ (k + 1) = some ⟨tp f' p', outer⟩ ∧ Inv f' p' := by
  obtain ⟨c, D, hD, h1 | h2 | h3 | ⟨b, h4⟩⟩ := hi
  · obtain ⟨k, F, hs, hF⟩ := step1 h1
    exact ⟨k, F, _, hs, c, D, hD, .inr (.inl hF)⟩
  · obtain ⟨k, F, p', b, D', hs, hD', hF⟩ := step2 hD h2
    exact ⟨k, F, p', hs, c + 1, D', hD', .inr (.inr (.inr ⟨b, hF⟩))⟩
  · obtain ⟨k, F, hs, hF⟩ := step3 h3
    exact ⟨k, F, _, hs, c + 1, D, hD, .inl hF⟩
  · obtain ⟨k, F, hs, hF⟩ := step4 h4
    obtain ⟨N, hN⟩ := hD
    refine ⟨k, F, _, hs, c, shift b D, ⟨N + b, fun k hk => ?_⟩, .inr (.inr (.inl hF))⟩
    simp only [shift]; split
    · rfl
    · exact hN _ (by omega)

theorem outer_diverges {f : Int → Bool} {p : Int} (hi : Inv f p) :
    (Machine.mk (tp f p) outer)⇑ := by
  refine Machine.Progress.diverges (S := fun m => ∃ f p, m = ⟨tp f p, outer⟩ ∧ Inv f p) ?_
    ⟨f, p, rfl, hi⟩
  rintro m ⟨f, p, rfl, hi⟩
  obtain ⟨k, f', p', hs, hi'⟩ := iter hi
  exact ⟨k + 1, _, by omega, hs, f', p', rfl, hi'⟩

theorem diverges : prog⇑ := by
  have h1 : flp (fun _ => false) 0 0 = true := by simp [flp]
  have h2 : ∀ i : Nat, i < 1 → flp (fun _ => false) 0 (0 - 2 * (i : Int)) = true := by
    intro i hi; simp [flp]; omega
  have h3 : flp (fun _ => false) 0 (0 - 2 * ((1 : Nat) : Int)) = false := by simp [flp]
  have h4 : flp (fun _ => false) 0 (0 - 2 * ((1 : Nat) : Int) + 1) = false := by simp [flp]
  have h5 : ∀ i : Nat, 1 ≤ i → i < 1 →
      flp (fun _ => false) 0 (0 - 2 * ((1 : Nat) : Int) + 1 + 2 * (i : Int)) = true := by
    intro i a b; omega
  have h6 : flp (fun _ => false) 0 (0 - 2 * ((1 : Nat) : Int) + 1 + 2 * ((1 : Nat) : Int)) = false := by
    simp [flp]
  obtain ⟨k, F, hs, hF⟩ := iterB h1 h2 h3 h4 h5 h6 (by omega)
  refine diverges_of_tp (k := 1 + (k + 1)) (r := outer) (f := F)
    (p := 0 - 2 * ((1 : Nat) : Int) + 2 * ((1 : Nat) : Int) - 1) ?_
    (outer_diverges ⟨0, fun _ => false, ⟨0, fun _ _ => rfl⟩, .inr (.inr (.inl fun x => ?_))⟩)
  · rw [Machine.steps_add]
    refine (congrArg (·.bind (·⇒(k + 1))) (run (step_flip (fun _ => false) 0 outer) rfl)).trans ?_
    exact hs
  · rw [hF x]
    unfold flp
    repeat' split
    all_goals first | rfl | (exfalso; omega)

end RightCounter

def Decider.rightCounter : Decider := Decider.known RightCounter.prog RightCounter.diverges

end BBBTape
