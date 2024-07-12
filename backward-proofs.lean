import Mathlib

inductive AExp: Type where
| num : ℤ -> AExp
| var : String -> AExp
| add : AExp -> AExp -> AExp
| sub : AExp -> AExp -> AExp
| mul : AExp -> AExp -> AExp
| div : AExp -> AExp -> AExp

def fib x :=
  match x with
| 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

def add a b :=
  match a, b with
  | m, Nat.zero => m
  | m, Nat.succ n => Nat.succ (add m n)

def mul a b :=
  match a, b with
  | _, Nat.zero => Nat.zero
  | m, Nat.succ n => add m (mul m n)

def iter (α : Type) (z : α) (f: α -> α) (a : Nat) : α :=
  match a with
  | Nat.zero => z
  | Nat.succ n => f (iter α z f n)

def appendImplicit {α : Type} (a : List α) (b : List α) : List α :=
  match a with
  | [] => b
  | x :: xs => List.cons x (appendImplicit xs b)

-- #eval appendImplicit [1, 2, 3] [4, 5, 6]

-- theorem add_comm (m n : Nat) :
--   add m n = add n m :=
--   sorry

opaque a : ℤ
opaque b : ℤ

axiom a_less_b:
  a < b

theorem fst_of_two_props:
  ∀ a b : Prop, a -> b -> a :=
  by
    intro a b
    intro ha _
    exact ha

theorem fst_of_two_props_params (a b : Prop) (ha : a) (hb : b) : a :=
  by exact ha

theorem prop_comp (a b c : Prop) (hab : a -> b) (hbc : b -> c) : a -> c :=
  by
    intro ha
    apply hbc
    apply hab
    exact ha

theorem And_swap (a b : Prop):
  a ∧ b -> b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

theorem And_swap_braces:
  ∀ a b: Prop, a ∧ b -> b ∧ a :=
  by
    intro a b hab
    apply And.intro
    { exact And.right hab }
    { exact And.left hab }

theorem Eq_trans_symm {α : Type} (a b c : α) (hab : a = b) (hcb : c = b) :
  a = c :=
  by
    apply Eq.trans
    { exact hab }
    { exact Eq.symm hcb }

theorem Eq_trans_symm_rw {α : Type} (a b c : α) (hab : a = b) (hcb : c = b) :
  a = c :=
  by
    rw [hab]
    rw [hcb]

theorem my_add_zero (n : ℕ):
  add 0 n = n :=
  by
    induction n with
    | zero => rfl
    | succ n' ih => simp [add, ih]
