import sys
from pathlib import Path

n, value, chain, depth, parts, champion = sys.argv[1:7]
depth, parts = int(depth), int(parts)
root = Path(__file__).resolve().parent.parent / "BBBTape" / "Results"
ns = f"BB{n}"
folder = root / ns
folder.mkdir(exist_ok=True)
for old in folder.glob("Part*.lean"):
    old.unlink()

(folder / "Frontier.lean").write_text(f"""import BBBTape.Core.Split
import BBBTape.Deciders.Chains
import BBBTape.Expanders.TNF

namespace BBBTape.{ns}

open scoped Program

def nodes : List Program := frontier Φ₁ {chain} {depth} (ω {n})

def part (j : Nat) : List Program := hashPart nodes {parts} j

end BBBTape.{ns}
""")

for j in range(parts):
    (folder / f"Part{j}.lean").write_text(f"""import BBBTape.Results.{ns}.Frontier

namespace BBBTape.{ns}

theorem part{j} : ∀ q ∈ part {j}, Bounded {value} q :=
  Bounded.of_all_within (e := Φ₁) (d := {chain}) (by native_decide)

end BBBTape.{ns}
""")

imports = "\n".join(f"import BBBTape.Results.{ns}.Part{j}" for j in range(parts))
cases = "\n".join(f"  | {j}, _ => exact part{j}" for j in range(parts))
(root / f"{ns}.lean").write_text(f"""{imports}

namespace BBBTape

open scoped Program
open {ns}

theorem {ns}.parts : ∀ j, j < {parts} → ∀ q ∈ part j, Bounded {value} q := by
  intro j hj
  match j, hj with
{cases}
  | j + {parts}, h => exact absurd h (by omega)

theorem bb{n} : IsBB {n} {value} :=
  IsBB.of_bounded (e := Φ₁) (d := {chain}) ({champion}) (by native_decide)
    (by simp [Program.Closed]) (by decide)
    (bounded_of_hashParts (e := Φ₁) (d := {chain}) {depth} (by decide) rfl {ns}.parts)

end BBBTape
""")
