import Bf.Config

namespace Bf

@[ext] structure Canon where
  f       : Program → Program
  size_eq : ∀ p : Program, (f p).size = p.size
  sound   : ∀ p : Program, p.SameTime (f p)

namespace Canon

def id : Canon where
  f := fun (p : Program) => p
  size_eq := fun (_ : Program) => rfl
  sound := Program.SameTime.refl

def comp (c₁ c₂ : Canon) : Canon where
  f := fun (p : Program) => c₂.f (c₁.f p)
  size_eq := fun (p : Program) => by rw [c₂.size_eq, c₁.size_eq]
  sound := fun (p : Program) => (c₁.sound p).trans (c₂.sound (c₁.f p))

theorem id_comp (c : Canon) : id.comp c = c := rfl

theorem comp_id (c : Canon) : c.comp id = c := rfl

theorem comp_assoc (a b c : Canon) : (a.comp b).comp c = a.comp (b.comp c) := rfl

end Canon

end Bf
