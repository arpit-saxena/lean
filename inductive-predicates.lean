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
  | trans (a b c : α) : R a b -> R b c -> Star R a c

theorem mod_two_Eq_zero_of_even (n : ℕ) (h : Even n) :
  n % 2 = 0 :=
  by
    induction h with
    | zero => rfl
    | add_two _ _ ih => simp[ih]

end InductivePredicates
