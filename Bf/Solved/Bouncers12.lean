import Bf.Solved.Block

namespace Bf.Solved.Bouncers12

open Block

set_option maxHeartbeats 2000000 in
theorem w0A_0 (h : Nat) (hh : 12 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<<<*[>>]*]")).steps 8 = some ⟨nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-2 : Int)], bf!"[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0A_8 (h : Nat) (hh : 12 ≤ h) :
    (Config.mk (nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-2 : Int)]) (bf!"[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf (0 + (4 : Int)) ((h : Int) + (4 : Int)) [(0 : Int), (1 : Int), (3 : Int)], bf!">>[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0A_16 (h : Nat) (hh : 12 ≤ h) :
    (Config.mk (nf (0 + (4 : Int)) ((h : Int) + (4 : Int)) [(0 : Int), (1 : Int), (3 : Int)]) (bf!">>[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf (0 + (5 : Int)) ((h : Int) + (5 : Int)) [(1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"*[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0A_24 (h : Nat) (hh : 12 ≤ h) :
    (Config.mk (nf (0 + (5 : Int)) ((h : Int) + (5 : Int)) [(1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"*[>>]*[<<<*[>>]*]")).steps 1 = some ⟨blk 0 ((h : Int) + ((5 : Nat) : Int)), bf!"[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0C_0 (lo : Int) (hl : lo ≤ -(18 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>>]*[<<<*[>>]*]")).steps 2 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_0 :
    (Config.mk Tape.blank (bf!"*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (2 : Int)], bf!">[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (2 : Int)]) (bf!">[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (3 : Int), (4 : Int)], bf!"[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_16 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (3 : Int), (4 : Int)]) (bf!"[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"<*[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_24 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"<*[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_32 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"<*[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_40 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"<*[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"*[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_48 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"*[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int)], bf!"[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_56 :
    (Config.mk (nf 0 (-1) [(0 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int)]) (bf!"[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int)], bf!"<*[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_64 :
    (Config.mk (nf 0 (-1) [(0 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int)]) (bf!"<*[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)], bf!"<<<*[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_72 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)]) (bf!"<<<*[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int)], bf!">>[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_80 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int)]) (bf!">>[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_88 :
    (Config.mk (nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-12 : Int), (-11 : Int), (-10 : Int), (-9 : Int), (-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!"[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_96 :
    (Config.mk (nf 0 (-1) [(-12 : Int), (-11 : Int), (-10 : Int), (-9 : Int), (-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!"[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-9 : Int), (-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"<<<*[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_104 :
    (Config.mk (nf 0 (-1) [(-9 : Int), (-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"<<<*[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)], bf!"<<*[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_112 :
    (Config.mk (nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)]) (bf!"<<*[>>]*[<<<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int), (10 : Int), (11 : Int)], bf!"<*[>>]*[<<<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w0S_120 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int), (9 : Int), (10 : Int), (11 : Int)]) (bf!"<*[>>]*[<<<*[>>]*]")).steps 4 = some ⟨blk 0 ((12 : Nat) : Int), bf!"[<<<*[>>]*]"⟩ := by
  nf_tac

theorem w0Start : (bf!"*[<<<*[>>]*]").init.steps 124 = some ⟨blk 0 ((12 : Nat) : Int), bf!"[<<<*[>>]*]"⟩ := by
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
  have c := steps_trans c w0S_120
  exact c

def w0Shape : Wide where
  outer := bf!"[<<<*[>>]*]"
  inner := bf!"[>>]*[<<<*[>>]*]"
  tA := 25
  tB := 3
  tC := 2
  tD := 7
  d := 2
  dD := 3
  gA := 5
  r := 1
  e := 0
  L := 18
  hmin := 12
  pos := by decide
  hA := fun (h : Nat) (hh : 12 ≤ h) => steps_trans (steps_trans (steps_trans (w0A_0 h hh) (w0A_8 h hh)) (w0A_16 h hh)) (w0A_24 h hh)
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(18 : Nat)) => w0C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(3 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w0_not_halts : ¬ (bf!"*[<<<*[>>]*]").init.Halts :=
  w0Shape.not_halts (j := 124) (b := 12) (g := 6) (fun (m : Nat) => 9 + 3 * m) (fun (m : Nat) => 6 + 2 * m)
    w0Start (by decide) (by decide)
    (fun (m : Nat) => by show (9 + 3 * m) * 2 = 12 + 6 * m + 5 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 3 + 0 = 12 + 6 * m + 5 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 3 = 12 + 6 * (m + 1); omega)
    (by decide)

def w0 : Bf.Solved := ⟨bf!"*[<<<*[>>]*]", .nonhalts, w0_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w1A_0 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<<*[>]***]")).steps 8 = some ⟨nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int), (0 : Int)], bf!"**[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1A_8 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int), (0 : Int)]) (bf!"**[<<*[>]***]")).steps 6 = some ⟨blk 0 ((h : Int) + ((3 : Nat) : Int)), bf!"[>]***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1C_0 (lo : Int) (hl : lo ≤ -(12 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]***[<<*[>]***]")).steps 4 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_0 :
    (Config.mk Tape.blank (bf!"*[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int)], bf!"***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int)]) (bf!"***[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!">[>]***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_16 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!">[>]***[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_24 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"***[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int)], bf!"***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_32 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int)]) (bf!"***[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_40 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"***[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!">[>]***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_48 :
    (Config.mk (nf 0 (-1) [(0 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!">[>]***[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)], bf!"*[>]***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_56 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)]) (bf!"*[>]***[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!">[>]***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_64 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!">[>]***[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!">[>]***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_72 :
    (Config.mk (nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!">[>]***[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"*[>]***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_80 :
    (Config.mk (nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"*[>]***[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"*[>]***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_88 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"*[>]***[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"*[>]***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_96 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"*[>]***[<<*[>]***]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)], bf!"*[>]***[<<*[>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w1S_104 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)]) (bf!"*[>]***[<<*[>]***]")).steps 5 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[<<*[>]***]"⟩ := by
  nf_tac

theorem w1Start : (bf!"*[<<*[>]***]").init.steps 109 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[<<*[>]***]"⟩ := by
  have c := w1S_0
  have c := steps_trans c w1S_8
  have c := steps_trans c w1S_16
  have c := steps_trans c w1S_24
  have c := steps_trans c w1S_32
  have c := steps_trans c w1S_40
  have c := steps_trans c w1S_48
  have c := steps_trans c w1S_56
  have c := steps_trans c w1S_64
  have c := steps_trans c w1S_72
  have c := steps_trans c w1S_80
  have c := steps_trans c w1S_88
  have c := steps_trans c w1S_96
  have c := steps_trans c w1S_104
  exact c

def w1Shape : Wide where
  outer := bf!"[<<*[>]***]"
  inner := bf!"[>]***[<<*[>]***]"
  tA := 14
  tB := 2
  tC := 4
  tD := 8
  d := 1
  dD := 2
  gA := 3
  r := 1
  e := 0
  L := 12
  hmin := 8
  pos := by decide
  hA := fun (h : Nat) (hh : 8 ≤ h) => steps_trans (w1A_0 h hh) (w1A_8 h hh)
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(12 : Nat)) => w1C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(2 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w1_not_halts : ¬ (bf!"*[<<*[>]***]").init.Halts :=
  w1Shape.not_halts (j := 109) (b := 8) (g := 4) (fun (m : Nat) => 12 + 4 * m) (fun (m : Nat) => 6 + 2 * m)
    w1Start (by decide) (by decide)
    (fun (m : Nat) => by show (12 + 4 * m) * 1 = 8 + 4 * m + 3 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 2 + 0 = 8 + 4 * m + 3 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 2 = 8 + 4 * (m + 1); omega)
    (by decide)

def w1 : Bf.Solved := ⟨bf!"*[<<*[>]***]", .nonhalts, w1_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w2A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>]*]*[[<*[>]*]*]")).steps 3 = some ⟨blk 0 ((h : Int) + ((1 : Nat) : Int)), bf!"[>]*[<*[>]*]*[[<*[>]*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*[<*[>]*]*[[<*[>]*]*]")).steps 2 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<*[>]*]*[[<*[>]*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_0 :
    (Config.mk Tape.blank (bf!"*[[<*[>]*]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int)], bf!">[>]*[<*[>]*]*[[<*[>]*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int)]) (bf!">[>]*[<*[>]*]*[[<*[>]*]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!"[<*[>]*]*[[<*[>]*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<*[>]*]*[[<*[>]*]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[>]*[<*[>]*]*[[<*[>]*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_24 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[>]*[<*[>]*]*[[<*[>]*]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"[>]*[<*[>]*]*[[<*[>]*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_32 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"[>]*[<*[>]*]*[[<*[>]*]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"<*[>]*[<*[>]*]*[[<*[>]*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_40 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"<*[>]*[<*[>]*]*[[<*[>]*]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"*[<*[>]*]*[[<*[>]*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w2S_48 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"*[<*[>]*]*[[<*[>]*]*]")).steps 6 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>]*]*[[<*[>]*]*]"⟩ := by
  nf_tac

theorem w2Start : (bf!"*[[<*[>]*]*]").init.steps 54 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>]*]*[[<*[>]*]*]"⟩ := by
  have c := w2S_0
  have c := steps_trans c w2S_8
  have c := steps_trans c w2S_16
  have c := steps_trans c w2S_24
  have c := steps_trans c w2S_32
  have c := steps_trans c w2S_40
  have c := steps_trans c w2S_48
  exact c

def w2Shape : Wide where
  outer := bf!"[<*[>]*]*[[<*[>]*]*]"
  inner := bf!"[>]*[<*[>]*]*[[<*[>]*]*]"
  tA := 3
  tB := 2
  tC := 2
  tD := 5
  d := 1
  dD := 1
  gA := 1
  r := 1
  e := 0
  L := 6
  hmin := 4
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w2A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w2C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w2_not_halts : ¬ (bf!"*[[<*[>]*]*]").init.Halts :=
  w2Shape.not_halts (j := 54) (b := 4) (g := 2) (fun (m : Nat) => 6 + 2 * m) (fun (m : Nat) => 6 + 2 * m)
    w2Start (by decide) (by decide)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 + 0 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * (m + 1); omega)
    (by decide)

def w2 : Bf.Solved := ⟨bf!"*[[<*[>]*]*]", .nonhalts, w2_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w3A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>>]*][[<*[>>]*]]")).steps 3 = some ⟨blk 0 ((h : Int) + ((1 : Nat) : Int)), bf!"[>>]*[<*[>>]*][[<*[>>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>>]*[<*[>>]*][[<*[>>]*]]")).steps 2 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<*[>>]*][[<*[>>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_0 :
    (Config.mk Tape.blank (bf!"*[[<*[>>]*]]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int)], bf!"[>>]*[<*[>>]*][[<*[>>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_8 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int)]) (bf!"[>>]*[<*[>>]*][[<*[>>]*]]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!"<*[>>]*[<*[>>]*][[<*[>>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!"<*[>>]*[<*[>>]*][[<*[>>]*]]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!">>[>>]*[<*[>>]*][[<*[>>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_24 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!">>[>>]*[<*[>>]*][[<*[>>]*]]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!"<*[>>]*[<*[>>]*][[<*[>>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_32 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!"<*[>>]*[<*[>>]*][[<*[>>]*]]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int)], bf!"*[<*[>>]*][[<*[>>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_40 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int)]) (bf!"*[<*[>>]*][[<*[>>]*]]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"*[>>]*[<*[>>]*][[<*[>>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w3S_48 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"*[>>]*[<*[>>]*][[<*[>>]*]]")).steps 3 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>>]*][[<*[>>]*]]"⟩ := by
  nf_tac

theorem w3Start : (bf!"*[[<*[>>]*]]").init.steps 51 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>>]*][[<*[>>]*]]"⟩ := by
  have c := w3S_0
  have c := steps_trans c w3S_8
  have c := steps_trans c w3S_16
  have c := steps_trans c w3S_24
  have c := steps_trans c w3S_32
  have c := steps_trans c w3S_40
  have c := steps_trans c w3S_48
  exact c

def w3Shape : Wide where
  outer := bf!"[<*[>>]*][[<*[>>]*]]"
  inner := bf!"[>>]*[<*[>>]*][[<*[>>]*]]"
  tA := 3
  tB := 3
  tC := 2
  tD := 5
  d := 2
  dD := 1
  gA := 1
  r := 1
  e := 0
  L := 6
  hmin := 4
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w3A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w3C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w3_not_halts : ¬ (bf!"*[[<*[>>]*]]").init.Halts :=
  w3Shape.not_halts (j := 51) (b := 4) (g := 2) (fun (m : Nat) => 3 + 1 * m) (fun (m : Nat) => 6 + 2 * m)
    w3Start (by decide) (by decide)
    (fun (m : Nat) => by show (3 + 1 * m) * 2 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 + 0 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * (m + 1); omega)
    (by decide)

def w3 : Bf.Solved := ⟨bf!"*[[<*[>>]*]]", .nonhalts, w3_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w4A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[**>>]*]")).steps 3 = some ⟨blk 0 ((h : Int) + ((1 : Nat) : Int)), bf!"[**>>]*[<*[**>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[**>>]*[<*[**>>]*]")).steps 2 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<*[**>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_0 :
    (Config.mk Tape.blank (bf!"*[<*[**>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int)], bf!">[**>>]*[<*[**>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int)]) (bf!">[**>>]*[<*[**>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!"[<*[**>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<*[**>>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[**>>]*[<*[**>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_24 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[**>>]*[<*[**>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!">>[**>>]*[<*[**>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_32 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!">>[**>>]*[<*[**>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (1 : Int)], bf!"*[<*[**>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_40 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (1 : Int)]) (bf!"*[<*[**>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"*[**>>]*[<*[**>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w4S_48 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"*[**>>]*[<*[**>>]*]")).steps 8 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[**>>]*]"⟩ := by
  nf_tac

theorem w4Start : (bf!"*[<*[**>>]*]").init.steps 56 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[**>>]*]"⟩ := by
  have c := w4S_0
  have c := steps_trans c w4S_8
  have c := steps_trans c w4S_16
  have c := steps_trans c w4S_24
  have c := steps_trans c w4S_32
  have c := steps_trans c w4S_40
  have c := steps_trans c w4S_48
  exact c

def w4Shape : Wide where
  outer := bf!"[<*[**>>]*]"
  inner := bf!"[**>>]*[<*[**>>]*]"
  tA := 3
  tB := 5
  tC := 2
  tD := 5
  d := 2
  dD := 1
  gA := 1
  r := 1
  e := 0
  L := 6
  hmin := 4
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w4A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w4C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w4_not_halts : ¬ (bf!"*[<*[**>>]*]").init.Halts :=
  w4Shape.not_halts (j := 56) (b := 4) (g := 2) (fun (m : Nat) => 3 + 1 * m) (fun (m : Nat) => 6 + 2 * m)
    w4Start (by decide) (by decide)
    (fun (m : Nat) => by show (3 + 1 * m) * 2 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 + 0 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * (m + 1); omega)
    (by decide)

def w4 : Bf.Solved := ⟨bf!"*[<*[**>>]*]", .nonhalts, w4_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w5A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>>][]*]")).steps 3 = some ⟨blk 0 ((h : Int) + ((1 : Nat) : Int)), bf!"[>>][]*[<*[>>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>>][]*[<*[>>][]*]")).steps 3 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<*[>>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_0 :
    (Config.mk Tape.blank (bf!"*[<*[>>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int)], bf!"[]*[<*[>>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_8 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int)]) (bf!"[]*[<*[>>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!"[<*[>>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<*[>>][]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int)], bf!"*[>>][]*[<*[>>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_24 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int)]) (bf!"*[>>][]*[<*[>>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"[]*[<*[>>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_32 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"[]*[<*[>>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"[<*[>>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_40 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<*[>>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"*[>>][]*[<*[>>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_48 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"*[>>][]*[<*[>>][]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"[]*[<*[>>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w5S_56 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"[]*[<*[>>][]*]")).steps 2 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>>][]*]"⟩ := by
  nf_tac

theorem w5Start : (bf!"*[<*[>>][]*]").init.steps 58 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>>][]*]"⟩ := by
  have c := w5S_0
  have c := steps_trans c w5S_8
  have c := steps_trans c w5S_16
  have c := steps_trans c w5S_24
  have c := steps_trans c w5S_32
  have c := steps_trans c w5S_40
  have c := steps_trans c w5S_48
  have c := steps_trans c w5S_56
  exact c

def w5Shape : Wide where
  outer := bf!"[<*[>>][]*]"
  inner := bf!"[>>][]*[<*[>>][]*]"
  tA := 3
  tB := 3
  tC := 3
  tD := 6
  d := 2
  dD := 1
  gA := 1
  r := 1
  e := 0
  L := 6
  hmin := 4
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w5A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w5C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w5_not_halts : ¬ (bf!"*[<*[>>][]*]").init.Halts :=
  w5Shape.not_halts (j := 58) (b := 4) (g := 2) (fun (m : Nat) => 3 + 1 * m) (fun (m : Nat) => 6 + 2 * m)
    w5Start (by decide) (by decide)
    (fun (m : Nat) => by show (3 + 1 * m) * 2 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 + 0 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * (m + 1); omega)
    (by decide)

def w5 : Bf.Solved := ⟨bf!"*[<*[>>][]*]", .nonhalts, w5_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w6A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<]*[>>]*[[<]*[>>]*]")).steps 4 = some ⟨blk 0 ((h : Int) + ((1 : Nat) : Int)), bf!"[>>]*[[<]*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w6C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>>]*[[<]*[>>]*]")).steps 3 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<]*[>>]*[[<]*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w6S_0 :
    (Config.mk Tape.blank (bf!"*[[<]*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int)], bf!">[>>]*[[<]*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w6S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int)]) (bf!">[>>]*[[<]*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int)], bf!"[<]*[>>]*[[<]*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w6S_16 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int)]) (bf!"[<]*[>>]*[[<]*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!">>[>>]*[[<]*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w6S_24 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!">>[>>]*[[<]*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"<[<]*[>>]*[[<]*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w6S_32 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"<[<]*[>>]*[[<]*[>>]*]")).steps 5 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<]*[>>]*[[<]*[>>]*]"⟩ := by
  nf_tac

theorem w6Start : (bf!"*[[<]*[>>]*]").init.steps 37 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<]*[>>]*[[<]*[>>]*]"⟩ := by
  have c := w6S_0
  have c := steps_trans c w6S_8
  have c := steps_trans c w6S_16
  have c := steps_trans c w6S_24
  have c := steps_trans c w6S_32
  exact c

def w6Shape : Wide where
  outer := bf!"[<]*[>>]*[[<]*[>>]*]"
  inner := bf!"[>>]*[[<]*[>>]*]"
  tA := 4
  tB := 3
  tC := 3
  tD := 2
  d := 2
  dD := 1
  gA := 1
  r := 1
  e := 0
  L := 6
  hmin := 4
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w6A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w6C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w6_not_halts : ¬ (bf!"*[[<]*[>>]*]").init.Halts :=
  w6Shape.not_halts (j := 37) (b := 4) (g := 2) (fun (m : Nat) => 3 + 1 * m) (fun (m : Nat) => 6 + 2 * m)
    w6Start (by decide) (by decide)
    (fun (m : Nat) => by show (3 + 1 * m) * 2 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 + 0 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * (m + 1); omega)
    (by decide)

def w6 : Bf.Solved := ⟨bf!"*[[<]*[>>]*]", .nonhalts, w6_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w7A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>]*]>[[<*[>]*]>]")).steps 3 = some ⟨blk 0 ((h : Int) + ((1 : Nat) : Int)), bf!"[>]*[<*[>]*]>[[<*[>]*]>]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*[<*[>]*]>[[<*[>]*]>]")).steps 2 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<*[>]*]>[[<*[>]*]>]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7S_0 :
    (Config.mk Tape.blank (bf!"*[[<*[>]*]>]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int)], bf!">[>]*[<*[>]*]>[[<*[>]*]>]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int)]) (bf!">[>]*[<*[>]*]>[[<*[>]*]>]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!"[<*[>]*]>[[<*[>]*]>]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<*[>]*]>[[<*[>]*]>]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[>]*[<*[>]*]>[[<*[>]*]>]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7S_24 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[>]*[<*[>]*]>[[<*[>]*]>]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"[>]*[<*[>]*]>[[<*[>]*]>]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7S_32 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"[>]*[<*[>]*]>[[<*[>]*]>]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"<*[>]*[<*[>]*]>[[<*[>]*]>]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7S_40 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"<*[>]*[<*[>]*]>[[<*[>]*]>]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"*[<*[>]*]>[[<*[>]*]>]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w7S_48 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"*[<*[>]*]>[[<*[>]*]>]")).steps 6 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>]*]>[[<*[>]*]>]"⟩ := by
  nf_tac

theorem w7Start : (bf!"*[[<*[>]*]>]").init.steps 54 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>]*]>[[<*[>]*]>]"⟩ := by
  have c := w7S_0
  have c := steps_trans c w7S_8
  have c := steps_trans c w7S_16
  have c := steps_trans c w7S_24
  have c := steps_trans c w7S_32
  have c := steps_trans c w7S_40
  have c := steps_trans c w7S_48
  exact c

def w7Shape : Wide where
  outer := bf!"[<*[>]*]>[[<*[>]*]>]"
  inner := bf!"[>]*[<*[>]*]>[[<*[>]*]>]"
  tA := 3
  tB := 2
  tC := 2
  tD := 5
  d := 1
  dD := 1
  gA := 1
  r := 1
  e := 0
  L := 6
  hmin := 4
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w7A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w7C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w7_not_halts : ¬ (bf!"*[[<*[>]*]>]").init.Halts :=
  w7Shape.not_halts (j := 54) (b := 4) (g := 2) (fun (m : Nat) => 6 + 2 * m) (fun (m : Nat) => 6 + 2 * m)
    w7Start (by decide) (by decide)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 + 0 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * (m + 1); omega)
    (by decide)

def w7 : Bf.Solved := ⟨bf!"*[[<*[>]*]>]", .nonhalts, w7_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w8A_0 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<<*[>][]*]")).steps 8 = some ⟨nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int)], bf!"*[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8A_8 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int)]) (bf!"*[<<*[>][]*]")).steps 5 = some ⟨blk 0 ((h : Int) + ((3 : Nat) : Int)), bf!"[>][]*[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8C_0 (lo : Int) (hl : lo ≤ -(12 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>][]*[<<*[>][]*]")).steps 3 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_0 :
    (Config.mk Tape.blank (bf!"*[<<*[>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int)], bf!"[]*[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int)]) (bf!"[]*[<<*[>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"[>][]*[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"[>][]*[<<*[>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"*[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_24 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"*[<<*[>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_32 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"[<<*[>][]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"<<*[>][]*[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_40 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"<<*[>][]*[<<*[>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!"[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_48 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!"[<<*[>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!"[>][]*[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_56 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!"[>][]*[<<*[>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"[>][]*[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_64 :
    (Config.mk (nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"[>][]*[<<*[>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!"<<*[>][]*[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_72 :
    (Config.mk (nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!"<<*[>][]*[<<*[>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"<*[>][]*[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_80 :
    (Config.mk (nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"<*[>][]*[<<*[>][]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"*[>][]*[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_88 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"*[>][]*[<<*[>][]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)], bf!"[>][]*[<<*[>][]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w8S_96 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)]) (bf!"[>][]*[<<*[>][]*]")).steps 3 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[<<*[>][]*]"⟩ := by
  nf_tac

theorem w8Start : (bf!"*[<<*[>][]*]").init.steps 99 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[<<*[>][]*]"⟩ := by
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

def w8Shape : Wide where
  outer := bf!"[<<*[>][]*]"
  inner := bf!"[>][]*[<<*[>][]*]"
  tA := 13
  tB := 2
  tC := 3
  tD := 7
  d := 1
  dD := 2
  gA := 3
  r := 1
  e := 0
  L := 12
  hmin := 8
  pos := by decide
  hA := fun (h : Nat) (hh : 8 ≤ h) => steps_trans (w8A_0 h hh) (w8A_8 h hh)
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(12 : Nat)) => w8C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(2 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w8_not_halts : ¬ (bf!"*[<<*[>][]*]").init.Halts :=
  w8Shape.not_halts (j := 99) (b := 8) (g := 4) (fun (m : Nat) => 12 + 4 * m) (fun (m : Nat) => 6 + 2 * m)
    w8Start (by decide) (by decide)
    (fun (m : Nat) => by show (12 + 4 * m) * 1 = 8 + 4 * m + 3 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 2 + 0 = 8 + 4 * m + 3 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 2 = 8 + 4 * (m + 1); omega)
    (by decide)

def w8 : Bf.Solved := ⟨bf!"*[<<*[>][]*]", .nonhalts, w8_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w9A_0 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[**<<*[>]*]")).steps 8 = some ⟨nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int)], bf!"[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9A_8 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int)]) (bf!"[>]*[**<<*[>]*]")).steps 8 = some ⟨blk 0 ((h : Int) + ((3 : Nat) : Int)), bf!"[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9C_0 (lo : Int) (hl : lo ≤ -(12 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*[**<<*[>]*]")).steps 2 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_0 :
    (Config.mk Tape.blank (bf!"*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (2 : Int)], bf!">[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_8 :
    (Config.mk (nf 0 (-1) [(0 : Int), (2 : Int)]) (bf!">[>]*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int)], bf!"*[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_16 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int)]) (bf!"*[>]*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!">[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_24 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!">[>]*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"*[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_32 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"*[>]*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"*[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_40 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"*[>]*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"*[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_48 :
    (Config.mk (nf 0 (-1) [(2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"*[>]*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!"<<*[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_56 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!"<<*[>]*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!">[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_64 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!">[>]*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!">[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_72 :
    (Config.mk (nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!">[>]*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!"<<*[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_80 :
    (Config.mk (nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!"<<*[>]*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"<<*[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_88 :
    (Config.mk (nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"<<*[>]*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"<<*[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_96 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"<<*[>]*[**<<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"<<*[>]*[**<<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w9S_104 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"<<*[>]*[**<<*[>]*]")).steps 5 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[**<<*[>]*]"⟩ := by
  nf_tac

theorem w9Start : (bf!"*[**<<*[>]*]").init.steps 109 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[**<<*[>]*]"⟩ := by
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
  exact c

def w9Shape : Wide where
  outer := bf!"[**<<*[>]*]"
  inner := bf!"[>]*[**<<*[>]*]"
  tA := 16
  tB := 2
  tC := 2
  tD := 8
  d := 1
  dD := 2
  gA := 3
  r := 1
  e := 0
  L := 12
  hmin := 8
  pos := by decide
  hA := fun (h : Nat) (hh : 8 ≤ h) => steps_trans (w9A_0 h hh) (w9A_8 h hh)
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(12 : Nat)) => w9C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(2 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w9_not_halts : ¬ (bf!"*[**<<*[>]*]").init.Halts :=
  w9Shape.not_halts (j := 109) (b := 8) (g := 4) (fun (m : Nat) => 12 + 4 * m) (fun (m : Nat) => 6 + 2 * m)
    w9Start (by decide) (by decide)
    (fun (m : Nat) => by show (12 + 4 * m) * 1 = 8 + 4 * m + 3 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 2 + 0 = 8 + 4 * m + 3 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 2 = 8 + 4 * (m + 1); omega)
    (by decide)

def w9 : Bf.Solved := ⟨bf!"*[**<<*[>]*]", .nonhalts, w9_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w10A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>][*]*]")).steps 3 = some ⟨blk 0 ((h : Int) + ((1 : Nat) : Int)), bf!"[>][*]*[<*[>][*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>][*]*[<*[>][*]*]")).steps 3 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<*[>][*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_0 :
    (Config.mk Tape.blank (bf!"*[<*[>][*]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int)], bf!"[>][*]*[<*[>][*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_8 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int)]) (bf!"[>][*]*[<*[>][*]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int)], bf!"*[<*[>][*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int)]) (bf!"*[<*[>][*]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int)], bf!"<*[>][*]*[<*[>][*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_24 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int)]) (bf!"<*[>][*]*[<*[>][*]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!"[>][*]*[<*[>][*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_32 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!"[>][*]*[<*[>][*]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (1 : Int)], bf!"[>][*]*[<*[>][*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_40 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (1 : Int)]) (bf!"[>][*]*[<*[>][*]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int)], bf!"*[<*[>][*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_48 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int)]) (bf!"*[<*[>][*]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"<*[>][*]*[<*[>][*]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w10S_56 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"<*[>][*]*[<*[>][*]*]")).steps 5 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>][*]*]"⟩ := by
  nf_tac

theorem w10Start : (bf!"*[<*[>][*]*]").init.steps 61 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>][*]*]"⟩ := by
  have c := w10S_0
  have c := steps_trans c w10S_8
  have c := steps_trans c w10S_16
  have c := steps_trans c w10S_24
  have c := steps_trans c w10S_32
  have c := steps_trans c w10S_40
  have c := steps_trans c w10S_48
  have c := steps_trans c w10S_56
  exact c

def w10Shape : Wide where
  outer := bf!"[<*[>][*]*]"
  inner := bf!"[>][*]*[<*[>][*]*]"
  tA := 3
  tB := 2
  tC := 3
  tD := 6
  d := 1
  dD := 1
  gA := 1
  r := 1
  e := 0
  L := 6
  hmin := 4
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w10A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w10C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w10_not_halts : ¬ (bf!"*[<*[>][*]*]").init.Halts :=
  w10Shape.not_halts (j := 61) (b := 4) (g := 2) (fun (m : Nat) => 6 + 2 * m) (fun (m : Nat) => 6 + 2 * m)
    w10Start (by decide) (by decide)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 + 0 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * (m + 1); omega)
    (by decide)

def w10 : Bf.Solved := ⟨bf!"*[<*[>][*]*]", .nonhalts, w10_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w11A_0 (h : Nat) (hh : 5 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>]*]")).steps 3 = some ⟨blk 0 ((h : Int) + ((1 : Nat) : Int)), bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11C_0 (lo : Int) (hl : lo ≤ -(7 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*[<*[>]*]")).steps 2 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_0 :
    (Config.mk Tape.blank (bf!"*<*>[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int)], bf!"*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_8 :
    (Config.mk (nf 0 (-1) [(1 : Int)]) (bf!"*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int)], bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_16 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int)]) (bf!"[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int)], bf!"*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_24 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int)]) (bf!"*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_32 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_40 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_48 :
    (Config.mk (nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"<*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_56 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"<*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_64 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!"*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w11S_72 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!"*[>]*[<*[>]*]")).steps 3 = some ⟨blk 0 ((5 : Nat) : Int), bf!"[<*[>]*]"⟩ := by
  nf_tac

theorem w11Start : (bf!"*<*>[<*[>]*]").init.steps 75 = some ⟨blk 0 ((5 : Nat) : Int), bf!"[<*[>]*]"⟩ := by
  have c := w11S_0
  have c := steps_trans c w11S_8
  have c := steps_trans c w11S_16
  have c := steps_trans c w11S_24
  have c := steps_trans c w11S_32
  have c := steps_trans c w11S_40
  have c := steps_trans c w11S_48
  have c := steps_trans c w11S_56
  have c := steps_trans c w11S_64
  have c := steps_trans c w11S_72
  exact c

def w11Shape : Wide where
  outer := bf!"[<*[>]*]"
  inner := bf!"[>]*[<*[>]*]"
  tA := 3
  tB := 2
  tC := 2
  tD := 5
  d := 1
  dD := 1
  gA := 1
  r := 1
  e := 0
  L := 7
  hmin := 5
  pos := by decide
  hA := fun (h : Nat) (hh : 5 ≤ h) => w11A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(7 : Nat)) => w11C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w11_not_halts : ¬ (bf!"*<*>[<*[>]*]").init.Halts :=
  w11Shape.not_halts (j := 75) (b := 5) (g := 2) (fun (m : Nat) => 7 + 2 * m) (fun (m : Nat) => 7 + 2 * m)
    w11Start (by decide) (by decide)
    (fun (m : Nat) => by show (7 + 2 * m) * 1 = 5 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (7 + 2 * m) * 1 + 0 = 5 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (7 + 2 * m) * 1 = 5 + 2 * (m + 1); omega)
    (by decide)

def w11 : Bf.Solved := ⟨bf!"*<*>[<*[>]*]", .nonhalts, w11_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w12A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>>]***]")).steps 3 = some ⟨blk 0 ((h : Int) + ((1 : Nat) : Int)), bf!"[>>]***[<*[>>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>>]***[<*[>>]***]")).steps 4 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<*[>>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_0 :
    (Config.mk Tape.blank (bf!"*[<*[>>]***]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int)], bf!"***[<*[>>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_8 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int)]) (bf!"***[<*[>>]***]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!"**[<*[>>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!"**[<*[>>]***]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int)], bf!"*[<*[>>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_24 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int)]) (bf!"*[<*[>>]***]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!">>[>>]***[<*[>>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_32 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!">>[>>]***[<*[>>]***]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"*[>>]***[<*[>>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_40 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"*[>>]***[<*[>>]***]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int)], bf!"[>>]***[<*[>>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_48 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (1 : Int), (2 : Int)]) (bf!"[>>]***[<*[>>]***]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"***[<*[>>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_56 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"***[<*[>>]***]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"**[<*[>>]***]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w12S_64 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"**[<*[>>]***]")).steps 2 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>>]***]"⟩ := by
  nf_tac

theorem w12Start : (bf!"*[<*[>>]***]").init.steps 66 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>>]***]"⟩ := by
  have c := w12S_0
  have c := steps_trans c w12S_8
  have c := steps_trans c w12S_16
  have c := steps_trans c w12S_24
  have c := steps_trans c w12S_32
  have c := steps_trans c w12S_40
  have c := steps_trans c w12S_48
  have c := steps_trans c w12S_56
  have c := steps_trans c w12S_64
  exact c

def w12Shape : Wide where
  outer := bf!"[<*[>>]***]"
  inner := bf!"[>>]***[<*[>>]***]"
  tA := 3
  tB := 3
  tC := 4
  tD := 7
  d := 2
  dD := 1
  gA := 1
  r := 1
  e := 0
  L := 6
  hmin := 4
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w12A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w12C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w12_not_halts : ¬ (bf!"*[<*[>>]***]").init.Halts :=
  w12Shape.not_halts (j := 66) (b := 4) (g := 2) (fun (m : Nat) => 3 + 1 * m) (fun (m : Nat) => 6 + 2 * m)
    w12Start (by decide) (by decide)
    (fun (m : Nat) => by show (3 + 1 * m) * 2 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 + 0 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * (m + 1); omega)
    (by decide)

def w12 : Bf.Solved := ⟨bf!"*[<*[>>]***]", .nonhalts, w12_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w13A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>]*]<[[<*[>]*]<]")).steps 3 = some ⟨blk 0 ((h : Int) + ((1 : Nat) : Int)), bf!"[>]*[<*[>]*]<[[<*[>]*]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w13C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*[<*[>]*]<[[<*[>]*]<]")).steps 2 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<*[>]*]<[[<*[>]*]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w13S_0 :
    (Config.mk Tape.blank (bf!"*[[<*[>]*]<]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int)], bf!">[>]*[<*[>]*]<[[<*[>]*]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w13S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int)]) (bf!">[>]*[<*[>]*]<[[<*[>]*]<]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)], bf!"[<*[>]*]<[[<*[>]*]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w13S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int)]) (bf!"[<*[>]*]<[[<*[>]*]<]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[>]*[<*[>]*]<[[<*[>]*]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w13S_24 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[>]*[<*[>]*]<[[<*[>]*]<]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"[>]*[<*[>]*]<[[<*[>]*]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w13S_32 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"[>]*[<*[>]*]<[[<*[>]*]<]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"<*[>]*[<*[>]*]<[[<*[>]*]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w13S_40 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"<*[>]*[<*[>]*]<[[<*[>]*]<]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"*[<*[>]*]<[[<*[>]*]<]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w13S_48 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"*[<*[>]*]<[[<*[>]*]<]")).steps 6 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>]*]<[[<*[>]*]<]"⟩ := by
  nf_tac

theorem w13Start : (bf!"*[[<*[>]*]<]").init.steps 54 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[<*[>]*]<[[<*[>]*]<]"⟩ := by
  have c := w13S_0
  have c := steps_trans c w13S_8
  have c := steps_trans c w13S_16
  have c := steps_trans c w13S_24
  have c := steps_trans c w13S_32
  have c := steps_trans c w13S_40
  have c := steps_trans c w13S_48
  exact c

def w13Shape : Wide where
  outer := bf!"[<*[>]*]<[[<*[>]*]<]"
  inner := bf!"[>]*[<*[>]*]<[[<*[>]*]<]"
  tA := 3
  tB := 2
  tC := 2
  tD := 5
  d := 1
  dD := 1
  gA := 1
  r := 1
  e := 0
  L := 6
  hmin := 4
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w13A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w13C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w13_not_halts : ¬ (bf!"*[[<*[>]*]<]").init.Halts :=
  w13Shape.not_halts (j := 54) (b := 4) (g := 2) (fun (m : Nat) => 6 + 2 * m) (fun (m : Nat) => 6 + 2 * m)
    w13Start (by decide) (by decide)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 + 0 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * (m + 1); omega)
    (by decide)

def w13 : Bf.Solved := ⟨bf!"*[[<*[>]*]<]", .nonhalts, w13_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w14A_0 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<<*[>]*][[<<*[>]*]]")).steps 8 = some ⟨nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int), (0 : Int)], bf!"[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14A_8 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int), (0 : Int)]) (bf!"[<<*[>]*][[<<*[>]*]]")).steps 4 = some ⟨blk 0 ((h : Int) + ((3 : Nat) : Int)), bf!"[>]*[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14C_0 (lo : Int) (hl : lo ≤ -(12 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*[<<*[>]*][[<<*[>]*]]")).steps 2 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14S_0 :
    (Config.mk Tape.blank (bf!"*[[<<*[>]*]]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int)], bf!"[>]*[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int)]) (bf!"[>]*[<<*[>]*][[<<*[>]*]]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"[>]*[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"[>]*[<<*[>]*][[<<*[>]*]]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!"[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14S_24 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!"[<<*[>]*][[<<*[>]*]]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"<*[>]*[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14S_32 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"<*[>]*[<<*[>]*][[<<*[>]*]]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"[>]*[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14S_40 :
    (Config.mk (nf 0 (-1) [(0 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"[>]*[<<*[>]*][[<<*[>]*]]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)], bf!"[>]*[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14S_48 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)]) (bf!"[>]*[<<*[>]*][[<<*[>]*]]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[>]*[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14S_56 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[>]*[<<*[>]*][[<<*[>]*]]")).steps 8 = some ⟨nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"[>]*[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14S_64 :
    (Config.mk (nf 0 (-1) [(-8 : Int), (-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"[>]*[<<*[>]*][[<<*[>]*]]")).steps 8 = some ⟨nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14S_72 :
    (Config.mk (nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"[<<*[>]*][[<<*[>]*]]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!"<*[>]*[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14S_80 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!"<*[>]*[<<*[>]*][[<<*[>]*]]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)], bf!"[>]*[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w14S_88 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int), (8 : Int)]) (bf!"[>]*[<<*[>]*][[<<*[>]*]]")).steps 2 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[<<*[>]*][[<<*[>]*]]"⟩ := by
  nf_tac

theorem w14Start : (bf!"*[[<<*[>]*]]").init.steps 90 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[<<*[>]*][[<<*[>]*]]"⟩ := by
  have c := w14S_0
  have c := steps_trans c w14S_8
  have c := steps_trans c w14S_16
  have c := steps_trans c w14S_24
  have c := steps_trans c w14S_32
  have c := steps_trans c w14S_40
  have c := steps_trans c w14S_48
  have c := steps_trans c w14S_56
  have c := steps_trans c w14S_64
  have c := steps_trans c w14S_72
  have c := steps_trans c w14S_80
  have c := steps_trans c w14S_88
  exact c

def w14Shape : Wide where
  outer := bf!"[<<*[>]*][[<<*[>]*]]"
  inner := bf!"[>]*[<<*[>]*][[<<*[>]*]]"
  tA := 12
  tB := 2
  tC := 2
  tD := 6
  d := 1
  dD := 2
  gA := 3
  r := 1
  e := 0
  L := 12
  hmin := 8
  pos := by decide
  hA := fun (h : Nat) (hh : 8 ≤ h) => steps_trans (w14A_0 h hh) (w14A_8 h hh)
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(12 : Nat)) => w14C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(2 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w14_not_halts : ¬ (bf!"*[[<<*[>]*]]").init.Halts :=
  w14Shape.not_halts (j := 90) (b := 8) (g := 4) (fun (m : Nat) => 12 + 4 * m) (fun (m : Nat) => 6 + 2 * m)
    w14Start (by decide) (by decide)
    (fun (m : Nat) => by show (12 + 4 * m) * 1 = 8 + 4 * m + 3 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 2 + 0 = 8 + 4 * m + 3 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 2 = 8 + 4 * (m + 1); omega)
    (by decide)

def w14 : Bf.Solved := ⟨bf!"*[[<<*[>]*]]", .nonhalts, w14_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w15A_0 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<<]*[>]*[[<<]*[>]*]")).steps 8 = some ⟨nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int)], bf!"*[[<<]*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w15A_8 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int)]) (bf!"*[[<<]*[>]*]")).steps 7 = some ⟨blk 0 ((h : Int) + ((3 : Nat) : Int)), bf!"[>]*[[<<]*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w15C_0 (lo : Int) (hl : lo ≤ -(12 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*[[<<]*[>]*]")).steps 3 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<<]*[>]*[[<<]*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w15S_0 :
    (Config.mk Tape.blank (bf!"*[[<<]*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (2 : Int)], bf!">[>]*[[<<]*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w15S_8 :
    (Config.mk (nf 0 (-1) [(0 : Int), (2 : Int)]) (bf!">[>]*[[<<]*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int)], bf!"*[>]*[[<<]*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w15S_16 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int)]) (bf!"*[>]*[[<<]*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!">[>]*[[<<]*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w15S_24 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!">[>]*[[<<]*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"<<[<<]*[>]*[[<<]*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w15S_32 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"<<[<<]*[>]*[[<<]*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!">[>]*[[<<]*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w15S_40 :
    (Config.mk (nf 0 (-1) [(0 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!">[>]*[[<<]*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)], bf!"*[>]*[[<<]*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w15S_48 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int), (7 : Int)]) (bf!"*[>]*[[<<]*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!">[>]*[[<<]*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w15S_56 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!">[>]*[[<<]*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!">[>]*[[<<]*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w15S_64 :
    (Config.mk (nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!">[>]*[[<<]*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"<<[<<]*[>]*[[<<]*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w15S_72 :
    (Config.mk (nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"<<[<<]*[>]*[[<<]*[>]*]")).steps 8 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[<<]*[>]*[[<<]*[>]*]"⟩ := by
  nf_tac

theorem w15Start : (bf!"*[[<<]*[>]*]").init.steps 80 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[<<]*[>]*[[<<]*[>]*]"⟩ := by
  have c := w15S_0
  have c := steps_trans c w15S_8
  have c := steps_trans c w15S_16
  have c := steps_trans c w15S_24
  have c := steps_trans c w15S_32
  have c := steps_trans c w15S_40
  have c := steps_trans c w15S_48
  have c := steps_trans c w15S_56
  have c := steps_trans c w15S_64
  have c := steps_trans c w15S_72
  exact c

def w15Shape : Wide where
  outer := bf!"[<<]*[>]*[[<<]*[>]*]"
  inner := bf!"[>]*[[<<]*[>]*]"
  tA := 15
  tB := 2
  tC := 3
  tD := 3
  d := 1
  dD := 2
  gA := 3
  r := 1
  e := 0
  L := 12
  hmin := 8
  pos := by decide
  hA := fun (h : Nat) (hh : 8 ≤ h) => steps_trans (w15A_0 h hh) (w15A_8 h hh)
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(12 : Nat)) => w15C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(2 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w15_not_halts : ¬ (bf!"*[[<<]*[>]*]").init.Halts :=
  w15Shape.not_halts (j := 80) (b := 8) (g := 4) (fun (m : Nat) => 12 + 4 * m) (fun (m : Nat) => 6 + 2 * m)
    w15Start (by decide) (by decide)
    (fun (m : Nat) => by show (12 + 4 * m) * 1 = 8 + 4 * m + 3 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 2 + 0 = 8 + 4 * m + 3 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 2 = 8 + 4 * (m + 1); omega)
    (by decide)

def w15 : Bf.Solved := ⟨bf!"*[[<<]*[>]*]", .nonhalts, w15_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w16A_0 (h : Nat) (hh : 4 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[**<*[>>]*]")).steps 5 = some ⟨blk 0 ((h : Int) + ((1 : Nat) : Int)), bf!"[>>]*[**<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w16C_0 (lo : Int) (hl : lo ≤ -(6 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>>]*[**<*[>>]*]")).steps 2 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[**<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w16S_0 :
    (Config.mk Tape.blank (bf!"*[**<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int)], bf!">[>>]*[**<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w16S_8 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int)]) (bf!">[>>]*[**<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int)], bf!"[>>]*[**<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w16S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int)]) (bf!"[>>]*[**<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int)], bf!"*[**<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w16S_24 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int)]) (bf!"*[**<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!">[>>]*[**<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w16S_32 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!">[>>]*[**<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"*<*[>>]*[**<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w16S_40 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"*<*[>>]*[**<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"<*[>>]*[**<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w16S_48 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"<*[>>]*[**<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"*[>>]*[**<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w16S_56 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"*[>>]*[**<*[>>]*]")).steps 8 = some ⟨nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"[>>]*[**<*[>>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w16S_64 :
    (Config.mk (nf 0 (-1) [(1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"[>>]*[**<*[>>]*]")).steps 2 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[**<*[>>]*]"⟩ := by
  nf_tac

theorem w16Start : (bf!"*[**<*[>>]*]").init.steps 66 = some ⟨blk 0 ((4 : Nat) : Int), bf!"[**<*[>>]*]"⟩ := by
  have c := w16S_0
  have c := steps_trans c w16S_8
  have c := steps_trans c w16S_16
  have c := steps_trans c w16S_24
  have c := steps_trans c w16S_32
  have c := steps_trans c w16S_40
  have c := steps_trans c w16S_48
  have c := steps_trans c w16S_56
  have c := steps_trans c w16S_64
  exact c

def w16Shape : Wide where
  outer := bf!"[**<*[>>]*]"
  inner := bf!"[>>]*[**<*[>>]*]"
  tA := 5
  tB := 3
  tC := 2
  tD := 7
  d := 2
  dD := 1
  gA := 1
  r := 1
  e := 0
  L := 6
  hmin := 4
  pos := by decide
  hA := fun (h : Nat) (hh : 4 ≤ h) => w16A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(6 : Nat)) => w16C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w16_not_halts : ¬ (bf!"*[**<*[>>]*]").init.Halts :=
  w16Shape.not_halts (j := 66) (b := 4) (g := 2) (fun (m : Nat) => 3 + 1 * m) (fun (m : Nat) => 6 + 2 * m)
    w16Start (by decide) (by decide)
    (fun (m : Nat) => by show (3 + 1 * m) * 2 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 + 0 = 4 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 1 = 4 + 2 * (m + 1); omega)
    (by decide)

def w16 : Bf.Solved := ⟨bf!"*[**<*[>>]*]", .nonhalts, w16_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w17A_0 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<<*[**>]*]")).steps 8 = some ⟨nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int)], bf!"[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17A_8 (h : Nat) (hh : 8 ≤ h) :
    (Config.mk (nf (0 + (1 : Int)) ((h : Int) + (1 : Int)) [(-1 : Int)]) (bf!"[**>]*[<<*[**>]*]")).steps 6 = some ⟨blk 0 ((h : Int) + ((3 : Nat) : Int)), bf!"[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17C_0 (lo : Int) (hl : lo ≤ -(12 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[**>]*[<<*[**>]*]")).steps 2 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_0 :
    (Config.mk Tape.blank (bf!"*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (2 : Int)], bf!">[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_8 :
    (Config.mk (nf 0 (-1) [(0 : Int), (2 : Int)]) (bf!">[**>]*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"**>[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_16 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"**>[**>]*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"**>[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_24 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"**>[**>]*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_32 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"<<*[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_40 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"<<*[**>]*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"*[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_48 :
    (Config.mk (nf 0 (-1) [(2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"*[**>]*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!"<<*[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_56 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!"<<*[**>]*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"**>[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_64 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"**>[**>]*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"**>[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_72 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"**>[**>]*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"**>[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_80 :
    (Config.mk (nf 0 (-1) [(-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"**>[**>]*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)], bf!"**>[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_88 :
    (Config.mk (nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int)]) (bf!"**>[**>]*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"*[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_96 :
    (Config.mk (nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"*[**>]*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_104 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"*[<<*[**>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"<<*[**>]*[<<*[**>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w17S_112 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"<<*[**>]*[<<*[**>]*]")).steps 5 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[<<*[**>]*]"⟩ := by
  nf_tac

theorem w17Start : (bf!"*[<<*[**>]*]").init.steps 117 = some ⟨blk 0 ((8 : Nat) : Int), bf!"[<<*[**>]*]"⟩ := by
  have c := w17S_0
  have c := steps_trans c w17S_8
  have c := steps_trans c w17S_16
  have c := steps_trans c w17S_24
  have c := steps_trans c w17S_32
  have c := steps_trans c w17S_40
  have c := steps_trans c w17S_48
  have c := steps_trans c w17S_56
  have c := steps_trans c w17S_64
  have c := steps_trans c w17S_72
  have c := steps_trans c w17S_80
  have c := steps_trans c w17S_88
  have c := steps_trans c w17S_96
  have c := steps_trans c w17S_104
  have c := steps_trans c w17S_112
  exact c

def w17Shape : Wide where
  outer := bf!"[<<*[**>]*]"
  inner := bf!"[**>]*[<<*[**>]*]"
  tA := 14
  tB := 4
  tC := 2
  tD := 6
  d := 1
  dD := 2
  gA := 3
  r := 1
  e := 0
  L := 12
  hmin := 8
  pos := by decide
  hA := fun (h : Nat) (hh : 8 ≤ h) => steps_trans (w17A_0 h hh) (w17A_8 h hh)
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(12 : Nat)) => w17C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(2 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w17_not_halts : ¬ (bf!"*[<<*[**>]*]").init.Halts :=
  w17Shape.not_halts (j := 117) (b := 8) (g := 4) (fun (m : Nat) => 12 + 4 * m) (fun (m : Nat) => 6 + 2 * m)
    w17Start (by decide) (by decide)
    (fun (m : Nat) => by show (12 + 4 * m) * 1 = 8 + 4 * m + 3 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 2 + 0 = 8 + 4 * m + 3 + 1; omega)
    (fun (m : Nat) => by show (6 + 2 * m) * 2 = 8 + 4 * (m + 1); omega)
    (by decide)

def w17 : Bf.Solved := ⟨bf!"*[<<*[**>]*]", .nonhalts, w17_not_halts⟩

set_option maxHeartbeats 2000000 in
theorem w18A_0 (h : Nat) (hh : 7 ≤ h) :
    (Config.mk (blk (0) ((h : Int))) (bf!"[<*[>]*]")).steps 3 = some ⟨blk 0 ((h : Int) + ((1 : Nat) : Int)), bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18C_0 (lo : Int) (hl : lo ≤ -(9 : Nat)) :
    (Config.mk (blk (lo) ((-((1 : Nat) : Int)))) (bf!"[>]*[<*[>]*]")).steps 2 = some ⟨blk (lo + ((0 : Nat) : Int)) 0, bf!"[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_0 :
    (Config.mk Tape.blank (bf!"*<<*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (3 : Int)], bf!">[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_8 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (3 : Int)]) (bf!">[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int)], bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_16 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int)]) (bf!"[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"<*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_24 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"<*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_32 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_40 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)], bf!"[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_48 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int)]) (bf!"[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)], bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_56 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int)]) (bf!"[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!"<*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_64 :
    (Config.mk (nf 0 (-1) [(0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!"<*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_72 :
    (Config.mk (nf 0 (-1) [(-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)], bf!"[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_80 :
    (Config.mk (nf 0 (-1) [(-7 : Int), (-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int)]) (bf!"[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)], bf!"<*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_88 :
    (Config.mk (nf 0 (-1) [(-6 : Int), (-5 : Int), (-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (0 : Int), (1 : Int)]) (bf!"<*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int)], bf!"*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_96 :
    (Config.mk (nf 0 (-1) [(-4 : Int), (-3 : Int), (-2 : Int), (-1 : Int), (1 : Int), (2 : Int), (3 : Int)]) (bf!"*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)], bf!"*[>]*[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_104 :
    (Config.mk (nf 0 (-1) [(-2 : Int), (-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int)]) (bf!"*[>]*[<*[>]*]")).steps 8 = some ⟨nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)], bf!"[<*[>]*]"⟩ := by
  nf_tac

set_option maxHeartbeats 2000000 in
theorem w18S_112 :
    (Config.mk (nf 0 (-1) [(-1 : Int), (0 : Int), (1 : Int), (2 : Int), (3 : Int), (4 : Int), (5 : Int), (6 : Int)]) (bf!"[<*[>]*]")).steps 5 = some ⟨blk 0 ((7 : Nat) : Int), bf!"[<*[>]*]"⟩ := by
  nf_tac

theorem w18Start : (bf!"*<<*[<*[>]*]").init.steps 117 = some ⟨blk 0 ((7 : Nat) : Int), bf!"[<*[>]*]"⟩ := by
  have c := w18S_0
  have c := steps_trans c w18S_8
  have c := steps_trans c w18S_16
  have c := steps_trans c w18S_24
  have c := steps_trans c w18S_32
  have c := steps_trans c w18S_40
  have c := steps_trans c w18S_48
  have c := steps_trans c w18S_56
  have c := steps_trans c w18S_64
  have c := steps_trans c w18S_72
  have c := steps_trans c w18S_80
  have c := steps_trans c w18S_88
  have c := steps_trans c w18S_96
  have c := steps_trans c w18S_104
  have c := steps_trans c w18S_112
  exact c

def w18Shape : Wide where
  outer := bf!"[<*[>]*]"
  inner := bf!"[>]*[<*[>]*]"
  tA := 3
  tB := 2
  tC := 2
  tD := 5
  d := 1
  dD := 1
  gA := 1
  r := 1
  e := 0
  L := 9
  hmin := 7
  pos := by decide
  hA := fun (h : Nat) (hh : 7 ≤ h) => w18A_0 h hh
  hB := fun (lo hi : Int) (h₁ : lo ≤ 0) (h₂ : 0 ≤ hi) => by nf_tac
  hC := fun (lo : Int) (hl : lo ≤ -(9 : Nat)) => w18C_0 lo hl
  hD := fun (lo hi : Int) (h₁ : lo ≤ -(1 : Nat)) (h₂ : 0 ≤ hi) => by nf_tac

theorem w18_not_halts : ¬ (bf!"*<<*[<*[>]*]").init.Halts :=
  w18Shape.not_halts (j := 117) (b := 7) (g := 2) (fun (m : Nat) => 9 + 2 * m) (fun (m : Nat) => 9 + 2 * m)
    w18Start (by decide) (by decide)
    (fun (m : Nat) => by show (9 + 2 * m) * 1 = 7 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (9 + 2 * m) * 1 + 0 = 7 + 2 * m + 1 + 1; omega)
    (fun (m : Nat) => by show (9 + 2 * m) * 1 = 7 + 2 * (m + 1); omega)
    (by decide)

def w18 : Bf.Solved := ⟨bf!"*<<*[<*[>]*]", .nonhalts, w18_not_halts⟩

def all : List Bf.Solved :=
  [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18]

end Bf.Solved.Bouncers12

