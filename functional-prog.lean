import Mathlib

namespace FunctionalProg

theorem Nat.succ_neq_self (n: ℕ):
  Nat.succ n ≠ n :=
  by
    induction n with
    | zero => simp
    | succ n' ih => simp[ih]

structure RGB where
  red   : ℕ
  green : ℕ
  blue  : ℕ

structure RGBA extends RGB where
  alpha : ℕ

def pureRed : RGB :=
  RGB.mk 0xff 0x00 0x00

def pureGreen : RGB :=
  {
    red   := 0x00
    green := 0xff
    blue  := 0x00
  }

def semitransparentGreen : RGBA :=
  {
    pureGreen with
    alpha := 0x7f
  }

class Inhabited (α: Type) : Type where
  default: α

instance Nat.Inhabited : Inhabited ℕ :=
  { default := 0 }

instance List.Inhabited {α: Type} : Inhabited (List α) :=
  { default := [] }

instance Fun.Inhabited {α β: Type} [Inhabited β] : Inhabited (α -> β) :=
  { default := fun _ ↦ Inhabited.default }

instance Prod.Inhabited {α β : Type} [Inhabited α] [Inhabited β]:
  Inhabited (α × β) :=
  { default := (Inhabited.default, Inhabited.default) }

def head {α : Type} [Inhabited α] (list: List α) : α :=
  match list with
  | [] => Inhabited.default
  | x :: _ => x

class IsCommutative {α: Type} (f : α -> α -> α) where
  comm: ∀a b, f a b = f b a

class IsAssociative {α: Type} (f : α -> α -> α) where
  assoc: ∀a b c, f (f a b) c = f a (f b c)

def add (a: ℕ) (b: ℕ) : ℕ :=
  a + b

instance IsAssociative_Add : IsAssociative add :=
  { assoc := add_assoc }

end FunctionalProg
