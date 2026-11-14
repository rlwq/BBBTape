import Bf.Solved.Wide2

namespace Bf.Solved.Bouncers12b

open Block

set_option maxHeartbeats 2000000 in
theorem w0A_0 (h : Nat) (hh : 9 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>>]*]")).steps 3 = some ⟨blk (-((0 : Nat) : Int)) ((h : Int) + ((1 : Nat) : Int)), bf!"[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0C_0 (lo : Int) (hl : lo ≤ -(12 : Nat)) :
    (Config.mk (blk (lo) ((-((2 : Nat) : Int)))) (bf!"[>>]*[<*[>>]*]")).steps 8 = some ⟨nf (lo + (-1 : Int)) ((-((2 : Nat) : Int)) + (-1 : Int)) [(-2 : Int), (-1 : Int)], bf!"[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0C_8 (lo : Int) (hl : lo ≤ -(12 : Nat)) :
    (Config.mk (nf (lo + (-1 : Int)) ((-((2 : Nat) : Int)) + (-1 : Int)) [(-2 : Int), (-1 : Int)]) (bf!"[>>]*[<*[>>]*]")).steps 2 = some ⟨blk (lo + (-1 : Int)) ((0 : Nat) : Int), bf!"[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_0 :
    (Config.mk Tape.blank (bf!"*<*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!">[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!">[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (1 : Int)], bf!"*[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_16 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (1 : Int)]) (bf!"*[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"*[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_24 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"*[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_32 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_40 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!"<*[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_48 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!"<*[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_56 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (0 : Int)], bf!"[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_64 :
    (Config.mk (nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (0 : Int)]) (bf!"[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-9 : Int), (-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!"[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_72 :
    (Config.mk (nf 0 (-1) [(-9 : Int), (-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!"[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int)], bf!"[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_80 :
    (Config.mk (nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int)]) (bf!"[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"<*[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_88 :
    (Config.mk (nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"<*[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!"*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_96 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!"*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)], bf!"*[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_104 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)]) (bf!"*[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)], bf!"[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_112 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)]) (bf!"[<*[>>]*]")).steps 5 = some ⟨blk 0 ((9 : Nat) : Int), bf!"[<*[>>]*]"⟩ := by
  nf_tac

theorem w0Start : (bf!"*<*[<*[>>]*]").init.steps 117 = some ⟨blk 0 ((9 : Nat) : Int), bf!"[<*[>>]*]"⟩ := by
  have c := w0S_0
  have c := steps_trans c w0S_8
  have c := steps_trans c w0S_16
  have c := steps_trans c w0S_24
  have c := steps_trans c w0S_32
  have c := steps_trans c w0S_40
  have c := steps_trans c w0S_48
  have c := steps_trans c w0S_56
  have c := steps_trans c w0S_64
  have c := steps_trans c w0S_72
  have c := steps_trans c w0S_80
  have c := steps_trans c w0S_88
  have c := steps_trans c w0S_96
  have c := steps_trans c w0S_104
  have c := steps_trans c w0S_112
  exact c

def w0Shape : Wide2 where
  outer := bf!"[<*[>>]*]"
  inner := bf!"[>>]*[<*[>>]*]"
  tA := 3
  tB := 3
  tC := 10
  tD := 5
  d := 2
  dD := 1
  a := 0
  gA := 1
  r := 2
  c := 0
  L := 12
  hmin := 9
  e := (-1 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 9 ≤ h) => w0A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(12 : Nat)) => steps_trans (w0C_0 lo hl) (w0C_8 lo hl)
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w0_not_halts : ¬ (bf!"*<*[<*[>>]*]").init.Halts :=
  w0Shape.not_halts (j := 117) (b := 9) (g := 4) (fun (m : Nat) => 6 + 2 * m) (fun (m : Nat) => 13 + 4 * m)
    w0Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w0Shape]; omega)
    (fun (m : Nat) => by simp only [w0Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w0Shape]; omega)
    (by decide)

def w0 : Bf.Solved := ⟨bf!"*<*[<*[>>]*]", .nonhalts, w0_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w1A_0 (h : Nat) (hh : 5 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>]*<]")).steps 3 = some ⟨blk (-((0 : Nat) : Int)) ((h : Int) + ((1 : Nat) : Int)), bf!"[>]*<[<*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1C_0 (lo : Int) (hl : lo ≤ -(7 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*<[<*[>]*<]")).steps 3 = some ⟨blk (lo + (1 : Int)) ((1 : Nat) : Int), bf!"[<*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_0 :
    (Config.mk Tape.blank (bf!"*<*[<*[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!"[>]*<[<*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!"[>]*<[<*[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"<*[>]*<[<*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_16 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"<*[>]*<[<*[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"[>]*<[<*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_24 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"[>]*<[<*[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!"[>]*<[<*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_32 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!"[>]*<[<*[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int)], bf!"[>]*<[<*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_40 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int)]) (bf!"[>]*<[<*[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"<[<*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_48 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"<[<*[>]*<]")).steps 1 = some ⟨blk 0 ((5 : Nat) : Int), bf!"[<*[>]*<]"⟩ := by
  nf_tac

theorem w1Start : (bf!"*<*[<*[>]*<]").init.steps 49 = some ⟨blk 0 ((5 : Nat) : Int), bf!"[<*[>]*<]"⟩ := by
  have c := w1S_0
  have c := steps_trans c w1S_8
  have c := steps_trans c w1S_16
  have c := steps_trans c w1S_24
  have c := steps_trans c w1S_32
  have c := steps_trans c w1S_40
  have c := steps_trans c w1S_48
  exact c

def w1Shape : Wide2 where
  outer := bf!"[<*[>]*<]"
  inner := bf!"[>]*<[<*[>]*<]"
  tA := 3
  tB := 2
  tC := 3
  tD := 6
  d := 1
  dD := 2
  a := 0
  gA := 1
  r := 1
  c := 1
  L := 7
  hmin := 5
  e := (1 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 5 ≤ h) => w1A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(7 : Nat)) => w1C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(2 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w1_not_halts : ¬ (bf!"*<*[<*[>]*<]").init.Halts :=
  w1Shape.not_halts (j := 49) (b := 5) (g := 2) (fun (m : Nat) => 7 + 2 * m) (fun (m : Nat) => 3 + 1 * m)
    w1Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w1Shape]; omega)
    (fun (m : Nat) => by simp only [w1Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w1Shape]; omega)
    (by decide)

def w1 : Bf.Solved := ⟨bf!"*<*[<*[>]*<]", .nonhalts, w1_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w2A_0 (h : Nat) (hh : 5 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>]*]")).steps 3 = some ⟨blk (-((0 : Nat) : Int)) ((h : Int) + ((1 : Nat) : Int)), bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2C_0 (lo : Int) (hl : lo ≤ -(7 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*[<*[>]*]")).steps 2 = some ⟨blk (lo + (0 : Int)) ((0 : Nat) : Int), bf!"[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_0 :
    (Config.mk Tape.blank (bf!"*>*<[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int)], bf!">[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_8 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int)]) (bf!">[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!"<*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_16 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!"<*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int)], bf!"*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_24 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int)]) (bf!"*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_32 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!">[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_40 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!">[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int)], bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_48 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int)]) (bf!"[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"<*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_56 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"<*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_64 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"*[<*[>]*]")).steps 6 = some ⟨blk 0 ((5 : Nat) : Int), bf!"[<*[>]*]"⟩ := by
  nf_tac

theorem w2Start : (bf!"*>*<[<*[>]*]").init.steps 70 = some ⟨blk 0 ((5 : Nat) : Int), bf!"[<*[>]*]"⟩ := by
  have c := w2S_0
  have c := steps_trans c w2S_8
  have c := steps_trans c w2S_16
  have c := steps_trans c w2S_24
  have c := steps_trans c w2S_32
  have c := steps_trans c w2S_40
  have c := steps_trans c w2S_48
  have c := steps_trans c w2S_56
  have c := steps_trans c w2S_64
  exact c

def w2Shape : Wide2 where
  outer := bf!"[<*[>]*]"
  inner := bf!"[>]*[<*[>]*]"
  tA := 3
  tB := 2
  tC := 2
  tD := 5
  d := 1
  dD := 1
  a := 0
  gA := 1
  r := 1
  c := 0
  L := 7
  hmin := 5
  e := (0 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 5 ≤ h) => w2A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(7 : Nat)) => w2C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w2_not_halts : ¬ (bf!"*>*<[<*[>]*]").init.Halts :=
  w2Shape.not_halts (j := 70) (b := 5) (g := 2) (fun (m : Nat) => 7 + 2 * m) (fun (m : Nat) => 7 + 2 * m)
    w2Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w2Shape]; omega)
    (fun (m : Nat) => by simp only [w2Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w2Shape]; omega)
    (by decide)

def w2 : Bf.Solved := ⟨bf!"*>*<[<*[>]*]", .nonhalts, w2_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w3A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>[>]]*]")).steps 5 = some ⟨blk (-((1 : Nat) : Int)) ((h : Int) + ((0 : Nat) : Int)), bf!"[>][>[>]]*[<*[>[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>][>[>]]*[<*[>[>]]*]")).steps 3 = some ⟨blk (lo + (0 : Int)) ((0 : Nat) : Int), bf!"[<*[>[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_0 :
    (Config.mk Tape.blank (bf!"*[<*[>[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int)], bf!"[>][>[>]]*[<*[>[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_8 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int)]) (bf!"[>][>[>]]*[<*[>[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!"[<*[>[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<*[>[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[>[>]]*[<*[>[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_24 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[>[>]]*[<*[>[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"[>][>[>]]*[<*[>[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_32 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"[>][>[>]]*[<*[>[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"[<*[>[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_40 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<*[>[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[>[>]]*[<*[>[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_48 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[>[>]]*[<*[>[>]]*]")).steps 7 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>[>]]*]"⟩ := by
  nf_tac

theorem w3Start : (bf!"*[<*[>[>]]*]").init.steps 55 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>[>]]*]"⟩ := by
  have c := w3S_0
  have c := steps_trans c w3S_8
  have c := steps_trans c w3S_16
  have c := steps_trans c w3S_24
  have c := steps_trans c w3S_32
  have c := steps_trans c w3S_40
  have c := steps_trans c w3S_48
  exact c

def w3Shape : Wide2 where
  outer := bf!"[<*[>[>]]*]"
  inner := bf!"[>][>[>]]*[<*[>[>]]*]"
  tA := 5
  tB := 2
  tC := 3
  tD := 5
  d := 1
  dD := 1
  a := 1
  gA := 0
  r := 1
  c := 0
  L := 6
  hmin := 4
  e := (0 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w3A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w3C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w3_not_halts : ¬ (bf!"*[<*[>[>]]*]").init.Halts :=
  w3Shape.not_halts (j := 55) (b := 4) (g := 2) (fun (m : Nat) => 5 + 2 * m) (fun (m : Nat) => 6 + 2 * m)
    w3Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w3Shape]; omega)
    (fun (m : Nat) => by simp only [w3Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w3Shape]; omega)
    (by decide)

def w3 : Bf.Solved := ⟨bf!"*[<*[>[>]]*]", .nonhalts, w3_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w4A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[[>>]]*]")).steps 4 = some ⟨blk (-((0 : Nat) : Int)) ((h : Int) + ((1 : Nat) : Int)), bf!"[>>][[>>]]*[<*[[>>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>>][[>>]]*[<*[[>>]]*]")).steps 3 = some ⟨blk (lo + (0 : Int)) ((0 : Nat) : Int), bf!"[<*[[>>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_0 :
    (Config.mk Tape.blank (bf!"*[<*[[>>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int)], bf!"[>>][[>>]]*[<*[[>>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_8 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int)]) (bf!"[>>][[>>]]*[<*[[>>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!"[<*[[>>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<*[[>>]]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[[>>]]*[<*[[>>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_24 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[[>>]]*[<*[[>>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"[[>>]]*[<*[[>>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_32 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"[[>>]]*[<*[[>>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"<*[[>>]]*[<*[[>>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_40 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"<*[[>>]]*[<*[[>>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"*[<*[[>>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_48 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"*[<*[[>>]]*]")).steps 6 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[[>>]]*]"⟩ := by
  nf_tac

theorem w4Start : (bf!"*[<*[[>>]]*]").init.steps 54 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[[>>]]*]"⟩ := by
  have c := w4S_0
  have c := steps_trans c w4S_8
  have c := steps_trans c w4S_16
  have c := steps_trans c w4S_24
  have c := steps_trans c w4S_32
  have c := steps_trans c w4S_40
  have c := steps_trans c w4S_48
  exact c

def w4Shape : Wide2 where
  outer := bf!"[<*[[>>]]*]"
  inner := bf!"[>>][[>>]]*[<*[[>>]]*]"
  tA := 4
  tB := 3
  tC := 3
  tD := 5
  d := 2
  dD := 1
  a := 0
  gA := 1
  r := 1
  c := 0
  L := 6
  hmin := 4
  e := (0 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w4A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w4C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w4_not_halts : ¬ (bf!"*[<*[[>>]]*]").init.Halts :=
  w4Shape.not_halts (j := 54) (b := 4) (g := 2) (fun (m : Nat) => 3 + 1 * m) (fun (m : Nat) => 6 + 2 * m)
    w4Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w4Shape]; omega)
    (fun (m : Nat) => by simp only [w4Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w4Shape]; omega)
    (by decide)

def w4 : Bf.Solved := ⟨bf!"*[<*[[>>]]*]", .nonhalts, w4_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w5A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<]*>[>]*[[<]*>[>]*]")).steps 5 = some ⟨blk (-((1 : Nat) : Int)) ((h : Int) + ((0 : Nat) : Int)), bf!"[>]*[[<]*>[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*[[<]*>[>]*]")).steps 3 = some ⟨blk (lo + (0 : Int)) ((0 : Nat) : Int), bf!"[<]*>[>]*[[<]*>[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_0 :
    (Config.mk Tape.blank (bf!"*[[<]*>[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int)], bf!">[>]*[[<]*>[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int)]) (bf!">[>]*[[<]*>[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int)], bf!"[<]*>[>]*[[<]*>[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_16 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int)]) (bf!"[<]*>[>]*[[<]*>[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!">[>]*[[<]*>[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_24 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!">[>]*[[<]*>[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"[<]*>[>]*[[<]*>[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_32 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<]*>[>]*[[<]*>[>]*]")).steps 6 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<]*>[>]*[[<]*>[>]*]"⟩ := by
  nf_tac

theorem w5Start : (bf!"*[[<]*>[>]*]").init.steps 38 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<]*>[>]*[[<]*>[>]*]"⟩ := by
  have c := w5S_0
  have c := steps_trans c w5S_8
  have c := steps_trans c w5S_16
  have c := steps_trans c w5S_24
  have c := steps_trans c w5S_32
  exact c

def w5Shape : Wide2 where
  outer := bf!"[<]*>[>]*[[<]*>[>]*]"
  inner := bf!"[>]*[[<]*>[>]*]"
  tA := 5
  tB := 2
  tC := 3
  tD := 2
  d := 1
  dD := 1
  a := 1
  gA := 0
  r := 1
  c := 0
  L := 6
  hmin := 4
  e := (0 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w5A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w5C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w5_not_halts : ¬ (bf!"*[[<]*>[>]*]").init.Halts :=
  w5Shape.not_halts (j := 38) (b := 4) (g := 2) (fun (m : Nat) => 5 + 2 * m) (fun (m : Nat) => 6 + 2 * m)
    w5Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w5Shape]; omega)
    (fun (m : Nat) => by simp only [w5Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w5Shape]; omega)
    (by decide)

def w5 : Bf.Solved := ⟨bf!"*[[<]*>[>]*]", .nonhalts, w5_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w6A_0 (h : Nat) (hh : 2 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<]*[>]<<[[<]*[>]<<]")).steps 4 = some ⟨blk (-((0 : Nat) : Int)) ((h : Int) + ((1 : Nat) : Int)), bf!"[>]<<[[<]*[>]<<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w6C_0 (lo : Int) (hl : lo ≤ -(4 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]<<[[<]*[>]<<]")).steps 4 = some ⟨blk (lo + (2 : Int)) ((1 : Nat) : Int), bf!"[<]*[>]<<[[<]*[>]<<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w6S_0 :
    (Config.mk Tape.blank (bf!"*[[<]*[>]<<]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int)], bf!"[>]<<[[<]*[>]<<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w6S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int)]) (bf!"[>]<<[[<]*[>]<<]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int)], bf!"[<]*[>]<<[[<]*[>]<<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w6S_16 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int)]) (bf!"[<]*[>]<<[[<]*[>]<<]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int)], bf!"[>]<<[[<]*[>]<<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w6S_24 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"[>]<<[[<]*[>]<<]")).steps 6 = some ⟨blk 0 ((2 : Nat) : Int), bf!"[<]*[>]<<[[<]*[>]<<]"⟩ := by
  nf_tac

theorem w6Start : (bf!"*[[<]*[>]<<]").init.steps 30 = some ⟨blk 0 ((2 : Nat) : Int), bf!"[<]*[>]<<[[<]*[>]<<]"⟩ := by
  have c := w6S_0
  have c := steps_trans c w6S_8
  have c := steps_trans c w6S_16
  have c := steps_trans c w6S_24
  exact c

def w6Shape : Wide2 where
  outer := bf!"[<]*[>]<<[[<]*[>]<<]"
  inner := bf!"[>]<<[[<]*[>]<<]"
  tA := 4
  tB := 2
  tC := 4
  tD := 2
  d := 1
  dD := 1
  a := 0
  gA := 1
  r := 1
  c := 1
  L := 4
  hmin := 2
  e := (2 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 2 ≤ h) => w6A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(4 : Nat)) => w6C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w6_not_halts : ¬ (bf!"*[[<]*[>]<<]").init.Halts :=
  w6Shape.not_halts (j := 30) (b := 2) (g := 1) (fun (m : Nat) => 4 + 1 * m) (fun (m : Nat) => 2 + 1 * m)
    w6Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w6Shape]; omega)
    (fun (m : Nat) => by simp only [w6Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w6Shape]; omega)
    (by decide)

def w6 : Bf.Solved := ⟨bf!"*[[<]*[>]<<]", .nonhalts, w6_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w7A_0 (h : Nat) (hh : 2 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<]*>[>]<[[<]*>[>]<]")).steps 5 = some ⟨blk (-((1 : Nat) : Int)) ((h : Int) + ((0 : Nat) : Int)), bf!"[>]<[[<]*>[>]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7C_0 (lo : Int) (hl : lo ≤ -(4 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]<[[<]*>[>]<]")).steps 3 = some ⟨blk (lo + (1 : Int)) ((0 : Nat) : Int), bf!"[<]*>[>]<[[<]*>[>]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7S_0 :
    (Config.mk Tape.blank (bf!"*[[<]*>[>]<]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int)], bf!">[>]<[[<]*>[>]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int)]) (bf!">[>]<[[<]*>[>]<]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int)], bf!"[<]*>[>]<[[<]*>[>]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7S_16 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int)]) (bf!"[<]*>[>]<[[<]*>[>]<]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int)], bf!"<[[<]*>[>]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7S_24 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"<[[<]*>[>]<]")).steps 6 = some ⟨blk 0 ((2 : Nat) : Int), bf!"[<]*>[>]<[[<]*>[>]<]"⟩ := by
  nf_tac

theorem w7Start : (bf!"*[[<]*>[>]<]").init.steps 30 = some ⟨blk 0 ((2 : Nat) : Int), bf!"[<]*>[>]<[[<]*>[>]<]"⟩ := by
  have c := w7S_0
  have c := steps_trans c w7S_8
  have c := steps_trans c w7S_16
  have c := steps_trans c w7S_24
  exact c

def w7Shape : Wide2 where
  outer := bf!"[<]*>[>]<[[<]*>[>]<]"
  inner := bf!"[>]<[[<]*>[>]<]"
  tA := 5
  tB := 2
  tC := 3
  tD := 2
  d := 1
  dD := 1
  a := 1
  gA := 0
  r := 1
  c := 0
  L := 4
  hmin := 2
  e := (1 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 2 ≤ h) => w7A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(4 : Nat)) => w7C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w7_not_halts : ¬ (bf!"*[[<]*>[>]<]").init.Halts :=
  w7Shape.not_halts (j := 30) (b := 2) (g := 1) (fun (m : Nat) => 3 + 1 * m) (fun (m : Nat) => 3 + 1 * m)
    w7Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w7Shape]; omega)
    (fun (m : Nat) => by simp only [w7Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w7Shape]; omega)
    (by decide)

def w7 : Bf.Solved := ⟨bf!"*[[<]*>[>]<]", .nonhalts, w7_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w8A_0 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<<*[[>]]*]")).steps 8 = some ⟨nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int)], bf!"[[>]]*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8A_8 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int)]) (bf!"[[>]]*[<<*[[>]]*]")).steps 7 = some ⟨blk (-((0 : Nat) : Int)) ((h : Int) + ((3 : Nat) : Int)), bf!"[>][[>]]*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8C_0 (lo : Int) (hl : lo ≤ -(12 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>][[>]]*[<<*[[>]]*]")).steps 3 = some ⟨blk (lo + (0 : Int)) ((0 : Nat) : Int), bf!"[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_0 :
    (Config.mk Tape.blank (bf!"*[<<*[[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int)], bf!"[>][[>]]*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int)]) (bf!"[>][[>]]*[<<*[[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[>][[>]]*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_16 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[>][[>]]*[<<*[[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"[>][[>]]*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_24 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"[>][[>]]*[<<*[[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int)], bf!"*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_32 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int)]) (bf!"*[<<*[[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"<<*[[>]]*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_40 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"<<*[[>]]*[<<*[[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!"*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_48 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!"*[<<*[[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"[>][[>]]*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_56 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"[>][[>]]*[<<*[[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"[>][[>]]*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_64 :
    (Config.mk (nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"[>][[>]]*[<<*[[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_72 :
    (Config.mk (nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"*[<<*[[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"<<*[[>]]*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_80 :
    (Config.mk (nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"<<*[[>]]*[<<*[[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"*[[>]]*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_88 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"*[[>]]*[<<*[[>]]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)], bf!"*[<<*[[>]]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_96 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)]) (bf!"*[<<*[[>]]*]")).steps 1 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[<<*[[>]]*]"⟩ := by
  nf_tac

theorem w8Start : (bf!"*[<<*[[>]]*]").init.steps 97 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[<<*[[>]]*]"⟩ := by
  have c := w8S_0
  have c := steps_trans c w8S_8
  have c := steps_trans c w8S_16
  have c := steps_trans c w8S_24
  have c := steps_trans c w8S_32
  have c := steps_trans c w8S_40
  have c := steps_trans c w8S_48
  have c := steps_trans c w8S_56
  have c := steps_trans c w8S_64
  have c := steps_trans c w8S_72
  have c := steps_trans c w8S_80
  have c := steps_trans c w8S_88
  have c := steps_trans c w8S_96
  exact c

def w8Shape : Wide2 where
  outer := bf!"[<<*[[>]]*]"
  inner := bf!"[>][[>]]*[<<*[[>]]*]"
  tA := 15
  tB := 2
  tC := 3
  tD := 6
  d := 1
  dD := 2
  a := 0
  gA := 3
  r := 1
  c := 0
  L := 12
  hmin := 8
  e := (0 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 8 ≤ h) => steps_trans (w8A_0 h hh) (w8A_8 h hh)
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(12 : Nat)) => w8C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(2 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w8_not_halts : ¬ (bf!"*[<<*[[>]]*]").init.Halts :=
  w8Shape.not_halts (j := 97) (b := 8) (g := 4) (fun (m : Nat) => 12 + 4 * m) (fun (m : Nat) => 6 + 2 * m)
    w8Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w8Shape]; omega)
    (fun (m : Nat) => by simp only [w8Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w8Shape]; omega)
    (by decide)

def w8 : Bf.Solved := ⟨bf!"*[<<*[[>]]*]", .nonhalts, w8_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w9A_0 (h : Nat) (hh : 9 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>>]*]")).steps 3 = some ⟨blk (-((0 : Nat) : Int)) ((h : Int) + ((1 : Nat) : Int)), bf!"[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9C_0 (lo : Int) (hl : lo ≤ -(12 : Nat)) :
    (Config.mk (blk (lo) ((-((2 : Nat) : Int)))) (bf!"[>>]*[<*[>>]*]")).steps 8 = some ⟨nf (lo + (-1 : Int)) ((-((2 : Nat) : Int)) + (-1 : Int)) [(-2 : Int), (-1 : Int)], bf!"[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9C_8 (lo : Int) (hl : lo ≤ -(12 : Nat)) :
    (Config.mk (nf (lo + (-1 : Int)) ((-((2 : Nat) : Int)) + (-1 : Int)) [(-2 : Int), (-1 : Int)]) (bf!"[>>]*[<*[>>]*]")).steps 2 = some ⟨blk (lo + (-1 : Int)) ((0 : Nat) : Int), bf!"[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_0 :
    (Config.mk Tape.blank (bf!"*>*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int)], bf!"[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_8 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int)]) (bf!"[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int)], bf!">[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_16 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int)]) (bf!">[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!">[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_24 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!">[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_32 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_40 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"<*[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_48 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"<*[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!">>[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_56 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!">>[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!"[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_64 :
    (Config.mk (nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!"[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_72 :
    (Config.mk (nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int)], bf!"[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_80 :
    (Config.mk (nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int)]) (bf!"[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"<*[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_88 :
    (Config.mk (nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"<*[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_96 :
    (Config.mk (nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"*[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_104 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"*[>>]*[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)], bf!"[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_112 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)]) (bf!"[<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int)], bf!"[>>]*[<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_120 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int)]) (bf!"[>>]*[<*[>>]*]")).steps 2 = some ⟨blk 0 ((9 : Nat) : Int), bf!"[<*[>>]*]"⟩ := by
  nf_tac

theorem w9Start : (bf!"*>*[<*[>>]*]").init.steps 122 = some ⟨blk 0 ((9 : Nat) : Int), bf!"[<*[>>]*]"⟩ := by
  have c := w9S_0
  have c := steps_trans c w9S_8
  have c := steps_trans c w9S_16
  have c := steps_trans c w9S_24
  have c := steps_trans c w9S_32
  have c := steps_trans c w9S_40
  have c := steps_trans c w9S_48
  have c := steps_trans c w9S_56
  have c := steps_trans c w9S_64
  have c := steps_trans c w9S_72
  have c := steps_trans c w9S_80
  have c := steps_trans c w9S_88
  have c := steps_trans c w9S_96
  have c := steps_trans c w9S_104
  have c := steps_trans c w9S_112
  have c := steps_trans c w9S_120
  exact c

def w9Shape : Wide2 where
  outer := bf!"[<*[>>]*]"
  inner := bf!"[>>]*[<*[>>]*]"
  tA := 3
  tB := 3
  tC := 10
  tD := 5
  d := 2
  dD := 1
  a := 0
  gA := 1
  r := 2
  c := 0
  L := 12
  hmin := 9
  e := (-1 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 9 ≤ h) => w9A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(12 : Nat)) => steps_trans (w9C_0 lo hl) (w9C_8 lo hl)
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w9_not_halts : ¬ (bf!"*>*[<*[>>]*]").init.Halts :=
  w9Shape.not_halts (j := 122) (b := 9) (g := 4) (fun (m : Nat) => 6 + 2 * m) (fun (m : Nat) => 13 + 4 * m)
    w9Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w9Shape]; omega)
    (fun (m : Nat) => by simp only [w9Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w9Shape]; omega)
    (by decide)

def w9 : Bf.Solved := ⟨bf!"*>*[<*[>>]*]", .nonhalts, w9_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w10A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<]*[>]*<[[<]*[>]*<]")).steps 4 = some ⟨blk (-((0 : Nat) : Int)) ((h : Int) + ((1 : Nat) : Int)), bf!"[>]*<[[<]*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*<[[<]*[>]*<]")).steps 4 = some ⟨blk (lo + (1 : Int)) ((1 : Nat) : Int), bf!"[<]*[>]*<[[<]*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_0 :
    (Config.mk Tape.blank (bf!"*[[<]*[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int)], bf!"[>]*<[[<]*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int)]) (bf!"[>]*<[[<]*[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int)], bf!"[<]*[>]*<[[<]*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_16 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int)]) (bf!"[<]*[>]*<[[<]*[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"[>]*<[[<]*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_24 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"[>]*<[[<]*[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"[<]*[>]*<[[<]*[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_32 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<]*[>]*<[[<]*[>]*<]")).steps 6 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<]*[>]*<[[<]*[>]*<]"⟩ := by
  nf_tac

theorem w10Start : (bf!"*[[<]*[>]*<]").init.steps 38 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<]*[>]*<[[<]*[>]*<]"⟩ := by
  have c := w10S_0
  have c := steps_trans c w10S_8
  have c := steps_trans c w10S_16
  have c := steps_trans c w10S_24
  have c := steps_trans c w10S_32
  exact c

def w10Shape : Wide2 where
  outer := bf!"[<]*[>]*<[[<]*[>]*<]"
  inner := bf!"[>]*<[[<]*[>]*<]"
  tA := 4
  tB := 2
  tC := 4
  tD := 2
  d := 1
  dD := 1
  a := 0
  gA := 1
  r := 1
  c := 1
  L := 6
  hmin := 4
  e := (1 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w10A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w10C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w10_not_halts : ¬ (bf!"*[[<]*[>]*<]").init.Halts :=
  w10Shape.not_halts (j := 38) (b := 4) (g := 2) (fun (m : Nat) => 6 + 2 * m) (fun (m : Nat) => 5 + 2 * m)
    w10Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w10Shape]; omega)
    (fun (m : Nat) => by simp only [w10Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w10Shape]; omega)
    (by decide)

def w10 : Bf.Solved := ⟨bf!"*[[<]*[>]*<]", .nonhalts, w10_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w11A_0 (h : Nat) (hh : 2 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<]>[>]*<[[<]>[>]*<]")).steps 4 = some ⟨blk (-((0 : Nat) : Int)) ((h : Int) + ((0 : Nat) : Int)), bf!"[>]*<[[<]>[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11C_0 (lo : Int) (hl : lo ≤ -(3 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*<[[<]>[>]*<]")).steps 4 = some ⟨blk (lo + (1 : Int)) ((1 : Nat) : Int), bf!"[<]>[>]*<[[<]>[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_0 :
    (Config.mk Tape.blank (bf!"*[[<]>[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int)], bf!"[>]*<[[<]>[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int)]) (bf!"[>]*<[[<]>[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int)], bf!"[>]*<[[<]>[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_16 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int)]) (bf!"[>]*<[[<]>[>]*<]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!"[<]>[>]*<[[<]>[>]*<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_24 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<]>[>]*<[[<]>[>]*<]")).steps 2 = some ⟨blk 0 ((2 : Nat) : Int), bf!"[<]>[>]*<[[<]>[>]*<]"⟩ := by
  nf_tac

theorem w11Start : (bf!"*[[<]>[>]*<]").init.steps 26 = some ⟨blk 0 ((2 : Nat) : Int), bf!"[<]>[>]*<[[<]>[>]*<]"⟩ := by
  have c := w11S_0
  have c := steps_trans c w11S_8
  have c := steps_trans c w11S_16
  have c := steps_trans c w11S_24
  exact c

def w11Shape : Wide2 where
  outer := bf!"[<]>[>]*<[[<]>[>]*<]"
  inner := bf!"[>]*<[[<]>[>]*<]"
  tA := 4
  tB := 2
  tC := 4
  tD := 2
  d := 1
  dD := 1
  a := 0
  gA := 0
  r := 1
  c := 1
  L := 3
  hmin := 2
  e := (1 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 2 ≤ h) => w11A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(3 : Nat)) => w11C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w11_not_halts : ¬ (bf!"*[[<]>[>]*<]").init.Halts :=
  w11Shape.not_halts (j := 26) (b := 2) (g := 1) (fun (m : Nat) => 3 + 1 * m) (fun (m : Nat) => 2 + 1 * m)
    w11Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w11Shape]; omega)
    (fun (m : Nat) => by simp only [w11Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w11Shape]; omega)
    (by decide)

def w11 : Bf.Solved := ⟨bf!"*[[<]>[>]*<]", .nonhalts, w11_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w12A_0 (h : Nat) (hh : 7 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>]*]")).steps 3 = some ⟨blk (-((0 : Nat) : Int)) ((h : Int) + ((1 : Nat) : Int)), bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12C_0 (lo : Int) (hl : lo ≤ -(9 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*[<*[>]*]")).steps 2 = some ⟨blk (lo + (0 : Int)) ((0 : Nat) : Int), bf!"[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_0 :
    (Config.mk Tape.blank (bf!"*>>*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!">[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!">[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int)], bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_16 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int)]) (bf!"[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"<*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_24 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"<*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!">[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_32 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!">[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!">[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_40 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!">[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_48 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_56 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"<*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_64 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"<*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!">[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_72 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!">[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!">[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_80 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!">[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!"<*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_88 :
    (Config.mk (nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!"<*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int)], bf!"*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_96 :
    (Config.mk (nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int)]) (bf!"*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_104 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!"[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_112 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!"[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)], bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_120 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)]) (bf!"[>]*[<*[>]*]")).steps 2 = some ⟨blk 0 ((7 : Nat) : Int), bf!"[<*[>]*]"⟩ := by
  nf_tac

theorem w12Start : (bf!"*>>*[<*[>]*]").init.steps 122 = some ⟨blk 0 ((7 : Nat) : Int), bf!"[<*[>]*]"⟩ := by
  have c := w12S_0
  have c := steps_trans c w12S_8
  have c := steps_trans c w12S_16
  have c := steps_trans c w12S_24
  have c := steps_trans c w12S_32
  have c := steps_trans c w12S_40
  have c := steps_trans c w12S_48
  have c := steps_trans c w12S_56
  have c := steps_trans c w12S_64
  have c := steps_trans c w12S_72
  have c := steps_trans c w12S_80
  have c := steps_trans c w12S_88
  have c := steps_trans c w12S_96
  have c := steps_trans c w12S_104
  have c := steps_trans c w12S_112
  have c := steps_trans c w12S_120
  exact c

def w12Shape : Wide2 where
  outer := bf!"[<*[>]*]"
  inner := bf!"[>]*[<*[>]*]"
  tA := 3
  tB := 2
  tC := 2
  tD := 5
  d := 1
  dD := 1
  a := 0
  gA := 1
  r := 1
  c := 0
  L := 9
  hmin := 7
  e := (0 : Int)
  pos := by decide
  hA := fun (h : Nat) (hh : 7 ≤ h) => w12A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(9 : Nat)) => w12C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w12_not_halts : ¬ (bf!"*>>*[<*[>]*]").init.Halts :=
  w12Shape.not_halts (j := 122) (b := 7) (g := 2) (fun (m : Nat) => 9 + 2 * m) (fun (m : Nat) => 9 + 2 * m)
    w12Start (by decide) (by decide)
    (fun (m : Nat) => by simp only [w12Shape]; omega)
    (fun (m : Nat) => by simp only [w12Shape]; push_cast; omega)
    (fun (m : Nat) => by simp only [w12Shape]; omega)
    (by decide)

def w12 : Bf.Solved := ⟨bf!"*>>*[<*[>]*]", .nonhalts, w12_not_halts⟩

def all : List Bf.Solved :=
  [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12]

end Bf.Solved.Bouncers12b

