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

-- Lists

theorem head_head_cases {α : Type} [Inhabited α] (xs : List α):
  head [head xs] = head xs :=
  by
    cases xs with
    | nil => rfl
    | cons x xs' => rfl

theorem head_head_match {α : Type} [Inhabited α] (xs : List α):
  head [head xs] = head xs :=
    match xs with
    | List.nil => by rfl
    | List.cons x xs' => by rfl

theorem injection_example {α: Type} (x y : α) (xs ys : List α)
    (h : x :: xs = y :: ys) :
  x = y ∧ xs = ys :=
  by
    cases h
    simp

theorem distinctness_example {α: Type} (y: α) (ys: List α) (h: [] = y :: ys) :
  false :=
  by cases h

def map {α β: Type} (f : α -> β) (xs : List α) : List β :=
  match xs with
  | [] => []
  | x :: xs => f x :: map f xs

def mapArgs {α β: Type} : (α -> β) -> List α -> List β
  | _, []       => []
  | f, x :: xs  => f x :: mapArgs f xs

theorem map_ident {α: Type} (xs : List α) :
  map (fun x ↦ x) xs = xs :=
  by
    induction xs with
    | nil => rfl
    | cons x xs' ih => simp[ih, map]

theorem map_comp {α β γ: Type} (f : α -> β) (g : β -> γ) (xs: List α) :
  map g (map f xs) = map (fun x ↦ g (f x)) xs :=
  by
    induction xs with
    | nil => rfl
    | cons x xs' ih => simp[ih, map]

theorem map_append (α β : Type) (f : α -> β) (xs ys : List α) :
  map f (xs ++ ys) = (map f xs) ++ (map f ys) :=
  by
    induction xs with
    | nil => rfl
    | cons x xs' ih => simp[ih, map]

def tail {α: Type} : List α -> List α
  | [] => []
  | _ :: xs => xs

def headOpt {α: Type} : List α -> Option α
  | [] => Option.none
  | x :: _ => Option.some x

def headPre {α: Type} : (xs : List α) -> xs ≠ [] -> α
  | [], _ => by simp at *
  | x :: _, _ => x

#eval headPre [1, 2, 3] (by simp)

def zip {α β : Type} : List α -> List β -> List (α × β)
  | x :: xs, y :: ys => (x, y) :: zip xs ys
  | []     , _       => []
  | _ :: _ , []      => []

def length {α : Type} : List α -> ℕ
  | []        => 0
  | _ :: xs   => 1 + length xs

theorem min_add_add (a b c : ℕ) :
  min (a + b) (a + c) = a + min b c :=
  by
    cases Classical.em (b ≤ c) with
    | inl h => simp[h]
    | inr h => simp[le_of_not_ge, h]

theorem length_zip {α β : Type} (xs : List α) (ys : List β) :
  length (zip xs ys) = min (length xs) (length ys) :=
  by
    induction xs generalizing ys with
    | nil          => simp[zip, length]
    | cons x xs ih =>
      cases ys with
      | nil         => simp[zip, length]
      | cons y ys'  => simp[zip, length, min_add_add, ih ys']

theorem map_zip {α α' β β' : Type} (f : α -> α') (g : β -> β') :
  ∀xs ys,
    map (fun ab : α × β ↦ (f (Prod.fst ab), g (Prod.snd ab))) (zip xs ys) =
    zip (map f xs) (map g ys)
    | x :: xs, y :: ys => by simp [zip, map, map_zip f g xs ys]
    | []     , _       => by rfl
    | _ :: _ , []      => by rfl



end FunctionalProg
