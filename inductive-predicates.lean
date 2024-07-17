import Mathlib

namespace InductivePredicates

inductive Even : ℕ -> Prop where
  | zero : Even 0
  | add_two : ∀k : ℕ, Even k -> Even (k + 2)

theorem Even_4 :
  Even 4 :=
  have Even_0 : Even 0 :=
    Even.zero
  have Even_2 : Even 2 :=
    Even.add_two _ Even_0
  show Even 4 from
    Even.add_two _ Even_2

inductive Score : Type where
  | vs        : ℕ -> ℕ -> Score
  | advServ   : Score
  | advRecv   : Score
  | gameServ  : Score
  | gameRecv  : Score

infixr:50 " − " => Score.vs

inductive Step : Score -> Score -> Prop where
  | serv_0_15     : ∀n, Step (0−n) (15−n)
  | serv_15_30    : ∀n, Step (15−n) (30−n)
  | serv_30_40    : ∀n, Step (30−n) (40−n)
  | serv_40_game  : ∀n, n < 40 → Step (40−n) Score.gameServ
  | serv_40_adv   : Step (40−40) Score.advServ
  | serv_adv_40   : Step Score.advServ (40−40)
  | serv_adv_game : Step Score.advServ Score.gameServ
  | recv_0_15     : ∀n, Step (n−0) (n−15)
  | recv_15_30    : ∀n, Step (n−15) (n−30)
  | recv_30_40    : ∀n, Step (n−30) (n−40)
  | recv_40_game  : ∀n, n < 40 → Step (n−40) Score.gameRecv
  | recv_40_adv   : Step (40−40) Score.advRecv
  | recv_adv_40   : Step Score.advRecv (40−40)
  | recv_adv_game : Step Score.advRecv Score.gameRecv

infixr:45 " ↝ " => Step

theorem no_Step_to_0_0 (s : Score) :
  ¬ s ↝ 0−0 :=
  by
    intro h
    cases h

inductive Star {α: Type} (R: α -> α -> Prop) : α -> α -> Prop where
  | base (a b : α)    : R a b -> Star R a b
  | refl (a : α)      : Star R a a
  | trans (a b c : α) : Star R a b -> Star R b c -> Star R a c

theorem mod_two_Eq_zero_of_even (n : ℕ) (h : Even n) :
  n % 2 = 0 :=
  by
    induction h with
    | zero => rfl
    | add_two _ _ ih => simp[ih]

theorem Star_Star_Iff_Star {α : Type} (R : α -> α -> Prop) (a b : α):
  Star (Star R) a b <-> Star R a b :=
  by
    apply Iff.intro
    (
      intro h
      induction h with
      | base _ _ hab => exact hab
      | refl a => apply Star.refl
      | trans a b c _ _ ihab ihbc => apply Star.trans a b c ihab ihbc
    )
    (
      intro h
      apply Star.base
      exact h
    )

@[simp] theorem Star_Star_eq_Star {α : Type} (R: α -> α -> Prop) :
  Star (Star R) = Star R :=
  by
    apply funext
    intro a
    apply funext
    intro b
    apply propext
    apply Star_Star_Iff_Star

theorem Even_Iff (n : ℕ) :
  Even n <-> n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) :=
  by
    apply Iff.intro
    {
      intro hn
      cases hn with
      | zero => simp
      | add_two k hk => {
        apply Or.intro_right
        apply Exists.intro k
        simp[hk]
      }
    }
    {
      intro hor
      cases hor with
      | inl h0 => simp[h0, Even.zero]
      | inr hm => {
        cases hm with
        | intro k hand => {
          cases hand with
          | intro heq hk => simp[hk, Even.add_two, heq]
        }
      }
    }

theorem Even_iff_struct (n : ℕ) :
  Even n <-> n = 0 ∨ (∃m : ℕ, n = m + 2 ∧ Even m) :=
  Iff.intro
    (
      fun (heven) =>
      match heven with
      | Even.zero => by simp
      | Even.add_two k heven_k => Or.inr (
        show ∃m, k + 2 = m + 2 ∧ Even m from
          Exists.intro k (by simp[*])
      )
    )
    (
      fun (hor) =>
      match hor with
      | Or.inl hn_eq_0 =>
        show Even n from
          by simp[Even.zero, hn_eq_0]
      | Or.inr hexists =>
        match hexists with
        | Exists.intro m hand =>
          match hand with
          | And.intro heq hm =>
            by simp[Even.add_two, hm, heq]
    )

-- Section 6.6.1 : Sorted lists

inductive Sorted : List ℕ -> Prop where
  | nil : Sorted []
  | single (x : ℕ) : Sorted [x]
  | two_or_more (x y : ℕ) {zs : List ℕ} (hle : x ≤ y) (hsorted : Sorted (y :: zs)) :
    Sorted (x :: y :: zs)

theorem Sorted_3_5 :
  Sorted [3, 5] :=
  by
    apply Sorted.two_or_more
    { simp }
    { exact Sorted.single _ }

theorem Sorted_3_t_raw :
  Sorted [3, 5] :=
  Sorted.two_or_more _ _ (by simp) (Sorted.single _)

theorem Sorted_7_9_9_11 :
  Sorted [7, 9, 9, 11] :=
  Sorted.two_or_more _ _ (by simp) (
    Sorted.two_or_more _ _ (by simp) (
      Sorted.two_or_more _ _ (by simp) (
        Sorted.single _
      )
    )
  )

theorem Not_Sorted_17_13 :
  ¬ Sorted [17, 13] :=
  by
    intro h
    cases h with
    | two_or_more _ _ hle hsorted =>
      simp at hle

-- Section 6.6.2 : Palindromes

inductive Palindrome {α : Type} : List α -> Prop where
  | nil : Palindrome []
  | single (x : α) : Palindrome [x]
  | sandwich (x : α) {xs : List α} (hxs : Palindrome xs) : Palindrome ([x] ++ xs ++ [x])

-- Already defined in forward-proofs.lean, but unable to figure out how to import it from there.
def reverse {α : Type} (x : List α) : List α:=
  match x with
  | []      => []
  | x :: xs => reverse xs ++ [x]

theorem reverse_append {α : Type}:
  ∀xs ys : List α,
    reverse (xs ++ ys) = reverse ys ++ reverse xs :=
  fun (xs: List α) => fun(ys: List α) =>
  match xs with
  | []      => by simp [reverse]
  | x :: xs => by simp [reverse, reverse_append xs]

theorem Palindrome_reverse {α : Type} (xs : List α) (hxs : Palindrome xs) :
  Palindrome (reverse xs) :=
  by
    induction hxs with
    | nil => exact Palindrome.nil
    | single x => exact Palindrome.single x
    | sandwich x hsx ih => {
      rw [reverse_append]
      exact Palindrome.sandwich x ih
    }

-- Section 6.6.3 : Full Binary Trees

inductive BTree (α : Type) : Type where
  | empty : BTree α
  | node  : α -> BTree α -> BTree α -> BTree α

inductive IsFull {α : Type} : BTree α -> Prop where
  | empty : IsFull BTree.empty
  | node (a : α) (l r : BTree α) (hl : IsFull l) (hr : IsFull r) (hiff : l = BTree.empty <-> r = BTree.empty) : IsFull (BTree.node a l r)

theorem IsFull_singleton {α : Type} (a : α) :
  IsFull (BTree.node a BTree.empty BTree.empty) :=
  by
    apply IsFull.node _ _ _ IsFull.empty IsFull.empty
    rfl

-- AGAIN, unnecessary copy where we should've been able to import
def mirror {α: Type} : BTree α -> BTree α
  | BTree.empty       => BTree.empty
  | BTree.node a l r  => BTree.node a (mirror r) (mirror l)

theorem mirror_Eq_empty_Iff {α: Type} :
  ∀t : BTree α, mirror t = BTree.empty ↔ t = BTree.empty
  | BTree.empty       => by rfl
  | BTree.node _ _ _  => by simp[mirror]

theorem IsFull_mirror {α : Type} (t : BTree α) (ht : IsFull t) :
  IsFull (mirror t) :=
  by
    induction ht with
    | empty => exact IsFull.empty
    | node a l r hl hr hiff ih_l ih_r => {
      rw [mirror]
      apply IsFull.node
      { exact ih_r }
      { exact ih_l }
      { simp [mirror_Eq_empty_Iff, hiff] }
    }

theorem IsFull_mirror_struct_induct {α : Type} (t : BTree α) :
  IsFull t -> IsFull (mirror t) :=
  by
    induction t with
    | empty => {
      intro ht
      exact ht
    }
    | node a l r ih_l ih_r => {
      intro ht
      cases ht with
      | node a l r hl hr hiff => {
        apply IsFull.node
        { exact ih_r hr }
        { exact ih_l hl }
        { simp[mirror_Eq_empty_Iff, hiff] }
      }
    }

-- Section 6.6.4 : First Order Terms

inductive Term (α β : Type) : Type where
  | var : β -> Term α β
  | fn  : α -> List (Term α β) -> Term α β

inductive WellFormed {α β : Type} (arity : α -> ℕ) :
  Term α β -> Prop where
  | var (x : β) : WellFormed arity (Term.var x)
  | fn (f : α) (ts : List (Term α β)) (hargs: ∀t ∈ ts, WellFormed arity t)
      (hlen: List.length ts = arity f) :
    WellFormed arity (Term.fn f ts)

-- skipped an inductive definition

end InductivePredicates
