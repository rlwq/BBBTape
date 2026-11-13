import Bf.Solved.Block

namespace Bf.Solved.Bouncers11

open Block

def deadTailShape : Shape where
  outer := bf!"[<*[>][]*]"
  inner := bf!"[>][]*[<*[>][]*]"
  tA := 3
  tB := 2
  tC := 3
  tD := 6
  gA := 1
  e := 0
  pos := by decide
  ge := by decide
  hA := fun (h : Nat) => by blk_tac
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by blk_tac
  hC := fun (lo : Int) (h : lo ≤ -1) => by blk_tac
  hD := fun (lo hi : Int) (h₁ : lo ≤ -1) (h₂ : 0 ≤ hi) => by blk_tac

def deadTail : Bf.Solved :=
  ⟨bf!"*[<*[>][]*]", .nonhalts, deadTailShape.not_halts (j := 1) (b := 0) (by simp only [deadTailShape]; blk_tac)⟩

def innerFirstShape : Shape where
  outer := bf!"[<]*[>]*[[<]*[>]*]"
  inner := bf!"[>]*[[<]*[>]*]"
  tA := 4
  tB := 2
  tC := 3
  tD := 2
  gA := 1
  e := 0
  pos := by decide
  ge := by decide
  hA := fun (h : Nat) => by blk_tac
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by blk_tac
  hC := fun (lo : Int) (h : lo ≤ -1) => by blk_tac
  hD := fun (lo hi : Int) (h₁ : lo ≤ -1) (h₂ : 0 ≤ hi) => by blk_tac

def innerFirst : Bf.Solved :=
  ⟨bf!"*[[<]*[>]*]", .nonhalts, innerFirstShape.not_halts (j := 2) (b := 0) (by simp only [innerFirstShape]; blk_tac)⟩

def nestedShape : Shape where
  outer := bf!"[[<*[>]]*]"
  inner := bf!"[>][<*[>]]*[[<*[>]]*]"
  tA := 4
  tB := 2
  tC := 3
  tD := 7
  gA := 1
  e := 0
  pos := by decide
  ge := by decide
  hA := fun (h : Nat) => by blk_tac
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by blk_tac
  hC := fun (lo : Int) (h : lo ≤ -1) => by blk_tac
  hD := fun (lo hi : Int) (h₁ : lo ≤ -1) (h₂ : 0 ≤ hi) => by blk_tac

def nested : Bf.Solved :=
  ⟨bf!"*[[<*[>]]*]", .nonhalts, nestedShape.not_halts (j := 1) (b := 0) (by simp only [nestedShape]; blk_tac)⟩

def slowShape : Shape where
  outer := bf!"[<]*[>]<[[<]*[>]<]"
  inner := bf!"[>]<[[<]*[>]<]"
  tA := 4
  tB := 2
  tC := 3
  tD := 2
  gA := 1
  e := 1
  pos := by decide
  ge := by decide
  hA := fun (h : Nat) => by blk_tac
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by blk_tac
  hC := fun (lo : Int) (h : lo ≤ -1) => by blk_tac
  hD := fun (lo hi : Int) (h₁ : lo ≤ -1) (h₂ : 0 ≤ hi) => by blk_tac

def slow : Bf.Solved :=
  ⟨bf!"*[[<]*[>]<]", .nonhalts, slowShape.not_halts (j := 2) (b := 0) (by simp only [slowShape]; blk_tac)⟩

def tripleShape : Shape where
  outer := bf!"[<*[>]***]"
  inner := bf!"[>]***[<*[>]***]"
  tA := 3
  tB := 2
  tC := 4
  tD := 7
  gA := 1
  e := 0
  pos := by decide
  ge := by decide
  hA := fun (h : Nat) => by blk_tac
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by blk_tac
  hC := fun (lo : Int) (h : lo ≤ -1) => by blk_tac
  hD := fun (lo hi : Int) (h₁ : lo ≤ -1) (h₂ : 0 ≤ hi) => by blk_tac

def triple : Bf.Solved :=
  ⟨bf!"*[<*[>]***]", .nonhalts, tripleShape.not_halts (j := 1) (b := 0) (by simp only [tripleShape]; blk_tac)⟩

def shiftedShape : Shape where
  outer := bf!"[<*[>]*]"
  inner := bf!"[>]*[<*[>]*]"
  tA := 3
  tB := 2
  tC := 2
  tD := 5
  gA := 1
  e := 0
  pos := by decide
  ge := by decide
  hA := fun (h : Nat) => by blk_tac
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by blk_tac
  hC := fun (lo : Int) (h : lo ≤ -1) => by blk_tac
  hD := fun (lo hi : Int) (h₁ : lo ≤ -1) (h₂ : 0 ≤ hi) => by blk_tac

def shifted : Bf.Solved :=
  ⟨bf!"*<*[<*[>]*]", .nonhalts, shiftedShape.not_halts (j := 3) (b := 1) (by simp only [shiftedShape]; blk_tac)⟩

def doubleFlipShape : Shape where
  outer := bf!"[**<*[>]*]"
  inner := bf!"[>]*[**<*[>]*]"
  tA := 5
  tB := 2
  tC := 2
  tD := 7
  gA := 1
  e := 0
  pos := by decide
  ge := by decide
  hA := fun (h : Nat) => by blk_tac
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by blk_tac
  hC := fun (lo : Int) (h : lo ≤ -1) => by blk_tac
  hD := fun (lo hi : Int) (h₁ : lo ≤ -1) (h₂ : 0 ≤ hi) => by blk_tac

def doubleFlip : Bf.Solved :=
  ⟨bf!"*[**<*[>]*]", .nonhalts, doubleFlipShape.not_halts (j := 1) (b := 0) (by simp only [doubleFlipShape]; blk_tac)⟩

def flipRunShape : Shape where
  outer := bf!"[<*[**>]*]"
  inner := bf!"[**>]*[<*[**>]*]"
  tA := 3
  tB := 4
  tC := 2
  tD := 5
  gA := 1
  e := 0
  pos := by decide
  ge := by decide
  hA := fun (h : Nat) => by blk_tac
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by blk_tac
  hC := fun (lo : Int) (h : lo ≤ -1) => by blk_tac
  hD := fun (lo hi : Int) (h₁ : lo ≤ -1) (h₂ : 0 ≤ hi) => by blk_tac

def flipRun : Bf.Solved :=
  ⟨bf!"*[<*[**>]*]", .nonhalts, flipRunShape.not_halts (j := 1) (b := 0) (by simp only [flipRunShape]; blk_tac)⟩

def stepBackShape : Shape where
  outer := bf!"[<]>[>]*[[<]>[>]*]"
  inner := bf!"[>]*[[<]>[>]*]"
  tA := 4
  tB := 2
  tC := 3
  tD := 2
  gA := 0
  e := 0
  pos := by decide
  ge := by decide
  hA := fun (h : Nat) => by blk_tac
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by blk_tac
  hC := fun (lo : Int) (h : lo ≤ -1) => by blk_tac
  hD := fun (lo hi : Int) (h₁ : lo ≤ -1) (h₂ : 0 ≤ hi) => by blk_tac

def stepBack : Bf.Solved :=
  ⟨bf!"*[[<]>[>]*]", .nonhalts, stepBackShape.not_halts (j := 2) (b := 0) (by simp only [stepBackShape]; blk_tac)⟩

def nestedRunShape : Shape where
  outer := bf!"[<*[[>]]*]"
  inner := bf!"[>][[>]]*[<*[[>]]*]"
  tA := 4
  tB := 2
  tC := 3
  tD := 5
  gA := 1
  e := 0
  pos := by decide
  ge := by decide
  hA := fun (h : Nat) => by blk_tac
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by blk_tac
  hC := fun (lo : Int) (h : lo ≤ -1) => by blk_tac
  hD := fun (lo hi : Int) (h₁ : lo ≤ -1) (h₂ : 0 ≤ hi) => by blk_tac

def nestedRun : Bf.Solved :=
  ⟨bf!"*[<*[[>]]*]", .nonhalts, nestedRunShape.not_halts (j := 1) (b := 0) (by simp only [nestedRunShape]; blk_tac)⟩

def wrappedShape : Shape where
  outer := bf!"[<*[>]*][[<*[>]*]]"
  inner := bf!"[>]*[<*[>]*][[<*[>]*]]"
  tA := 3
  tB := 2
  tC := 2
  tD := 5
  gA := 1
  e := 0
  pos := by decide
  ge := by decide
  hA := fun (h : Nat) => by blk_tac
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by blk_tac
  hC := fun (lo : Int) (h : lo ≤ -1) => by blk_tac
  hD := fun (lo hi : Int) (h₁ : lo ≤ -1) (h₂ : 0 ≤ hi) => by blk_tac

def wrapped : Bf.Solved :=
  ⟨bf!"*[[<*[>]*]]", .nonhalts, wrappedShape.not_halts (j := 2) (b := 0) (by simp only [wrappedShape]; blk_tac)⟩

def reflectedShape : Shape where
  outer := bf!"[<*[>]*]"
  inner := bf!"[>]*[<*[>]*]"
  tA := 3
  tB := 2
  tC := 2
  tD := 5
  gA := 1
  e := 0
  pos := by decide
  ge := by decide
  hA := fun (h : Nat) => by blk_tac
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by blk_tac
  hC := fun (lo : Int) (h : lo ≤ -1) => by blk_tac
  hD := fun (lo hi : Int) (h₁ : lo ≤ -1) (h₂ : 0 ≤ hi) => by blk_tac

theorem reflectedStart : (bf!"*>*[<*[>]*]").init.steps (3 + 5) = some ⟨blk 0 1, reflectedShape.outer⟩ := by
  have h₁ : (bf!"*>*[<*[>]*]").init.steps 3 = some ⟨blk (-1) 0, reflectedShape.outer⟩ := by
    simp only [reflectedShape]; blk_tac
  have h₂ := reflectedShape.hD (-1) 0 (by omega) (by omega)
  exact steps_trans h₁ (shift h₂ (by omega) (by omega))

def reflected : Bf.Solved := ⟨bf!"*>*[<*[>]*]", .nonhalts, reflectedShape.not_halts (b := 1) reflectedStart⟩

def all : List Bf.Solved :=
  [deadTail, innerFirst, nested, slow, triple, shifted, doubleFlip, flipRun, stepBack, nestedRun, wrapped, reflected]

end Bf.Solved.Bouncers11
