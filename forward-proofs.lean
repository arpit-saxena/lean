import Mathlib

theorem fst_of_two_props :
  ∀ a b : Prop, a -> b -> a :=
  fun (a b : Prop) =>
  fun (ha : a) (hb : b) =>
  show a from
    ha

theorem prop_comp (a b c : Prop) (hab : a -> b) (hbc : b -> c) :
  a -> c :=
  fun (ha : a) =>
  have hb : b :=
    hab ha
  have hc : c :=
    hbc hb
  show c from hc

theorem And_swap (a b : Prop):
  a ∧ b -> b ∧ a :=
  fun (hab : a ∧ b) =>
  have ha : a :=
    And.left hab
  have hb : b :=
    And.right hab
  show b ∧ a from
    And.intro hb ha

theorem Forall.one_point {α : Type} (t: α) (P : α -> Prop) :
  (∀x, x = t -> P x) <-> P t :=
  Iff.intro
    (
      fun (hall: ∀x : α, x = t -> P x) =>
      show P t from
        by
          apply hall t
          rfl
    )
    (
      fun (ht : P t) =>
      fun (x : α) =>
      fun (hxt : x = t) =>
      show P x from
        by
          rw [hxt]
          exact ht
    )

theorem beast_666 (beast : ℕ) :
  (∀n, n = 666 -> beast ≥ n) <-> beast ≥ 666 :=
  Forall.one_point _ _

theorem Exists.one_point {α : Type} (t: α) (P : α -> Prop) :
  (∃x : α, x = t ∧ P x) <-> P t :=
  Iff.intro
    (
      fun (hexists: ∃x : α, x = t ∧ P x) =>
      show P t from
        Exists.elim hexists
          (
            fun (x : α) =>
            fun (hand: x = t ∧ P x) =>
            show P t from
            by
              rw [<- And.left hand]
              exact And.right hand
          )
    )
    (
      fun (ht : P t) =>
      show ∃x : α, x = t ∧ P x from
        Exists.intro t
          (
            have tt : t = t :=
            by
              rfl
            show t = t ∧ P t from
              And.intro tt ht
          )
    )

theorem prop_comp_tactical (a b c : Prop) (hab : a -> b) (hbc : b -> c) :
  a -> c :=
  by
    intro ha
    have hb: b :=
      hab ha
    let c' := c
    have hc : c' :=
      hbc hb
    exact hc
