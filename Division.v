(* File: Division.v *)
(* Author: Peter Urbak <peter@dragonwasrobot.com> *)
(* Version: 2012-04-12 *)

(* Implementation of euclidean division. *)

(* Fixpoints *)

Fixpoint dividend_greater_than_diviser_p
  (dividend diviser : nat) : option nat :=
  match dividend, diviser with
      | _, O => Some dividend
      | O, S _ => None
      | S dividend', S diviser'
        => dividend_greater_than_diviser_p dividend' diviser'
  end.

Fixpoint quotient_and_remainder_aux
  (dividend divisor quotient bogus_but_decreasing : nat) : option (nat * nat) :=
    match bogus_but_decreasing with
      | O => None
      | S bogus_but_decreasing' =>
        match dividend_greater_than_diviser_p dividend divisor with
          | None => Some (quotient, dividend)
          | Some dividend' =>
            quotient_and_remainder_aux
            dividend' divisor (S quotient) bogus_but_decreasing'
        end
    end.

Definition quotient_and_remainder (dividend divisor : nat) : option (nat * nat) :=
  match divisor with
    | O => None
    | S _ => quotient_and_remainder_aux dividend divisor 0 (S dividend)
  end.

Definition division (n m : nat) : option (nat * nat) :=
  quotient_and_remainder n m.

Notation "x / y" := (division x y)
  (at level 40, left associativity).

(* The correctness of the division function will not be proved. *)

(* end-of-Division.v *)