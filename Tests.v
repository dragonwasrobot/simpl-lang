(* File: Tests.v *)
(* Author: Peter Urbak <peter@dragonwasrobot.com> *)
(* Version: 2012-04-12 *)

(* Tests for the Simple CPS Interpreter project. *)

(* -*- Requirements. -*- *)
Require Export Division Arithmetic_Expression_Interpreter.

(* -*- Tests - Division.v -*- *)
Compute dividend_greater_than_diviser_p 10 3 = Some 7.
Compute dividend_greater_than_diviser_p 10 12 = None.

Compute quotient_and_remainder 11 3 = Some(3, 2).
Compute quotient_and_remainder 15 5 = Some(3 ,0).

(* -*- Tests - Arithmetic-Expression-Interpreter.v -*- *)

(* Tests - lifted_X functions *)

(* lifted_plus *)
Compute lifted_plus (Some 35) (Some 7) = Some 42.
Compute lifted_plus (Some 42) None = None.

(* lifted_minus *)
Compute lifted_minus (Some 35) (Some 7) = Some 28.
Compute lifted_minus (Some 28) None = None.

(* lifted_times *)
Compute lifted_times (Some 7) (Some 7) = Some 49.
Compute lifted_times (Some 21) None = None.

(* lifted_division *)
Compute lifted_division (Some 9) (Some 2) = Some 4. (* remainder: 1 *)
Compute lifted_plus (Some 144) None = None.

(* Composite test *)
Compute (lifted_plus (lifted_times (Some 6) (Some 7))
  (lifted_minus (Some 5) (Some 4))) = Some 43.

(* Tests - Interpret *)

(* Lit *)
Compute (interpret (Lit 42)) = Some 42.

(* Plus *)
Compute (interpret (Plus (Lit 3) (Lit 7))) = Some 10.
Compute (interpret (Plus (Lit 14) (Lit 3))) = Some 17.

(* Minus *)
Compute (interpret (Minus (Lit 10) (Lit 3))) = Some 7.
Compute (interpret (Minus (Lit 5) (Lit 6))) = Some 0.

(* Times *)
Compute (interpret (Times (Lit 5) (Lit 6))) = Some 30.
Compute (interpret (Times (Lit 7) (Lit 6))) = Some 42.

(* Divide *)
Compute (interpret (Divide (Lit 30) (Lit 5))) = Some 6.
Compute (interpret (Divide (Lit 42) (Lit 3))) = Some 14. (* remainder: 1 *)

(* Composite test *)
Compute (interpret (Plus (Times (Lit 2) (Lit 6)) (Times (Lit 6) (Lit 5)))) =
Some 42.
Compute (interpret (Minus (Divide (Lit 12) (Lit 3)) (Divide (Lit 6) (Lit 2)))) =
Some 1.

(* Tests - lifted_X_cps *)

(* lifted_plus_cps *)
Compute lifted_plus_cps (Some 35) (Some 7) (fun k => k) = Some 42.
Compute lifted_plus_cps (Some 35) (Some 7) (fun k => lifted_division k (Some 2))
= Some 21.

Compute lifted_plus_cps (Some 42) None (fun k => k) = None.
Compute lifted_plus_cps (Some 43) None (fun k => lifted_times k (Some 3)) = None.

(* lifted_minus_cps *)
Compute lifted_minus_cps (Some 42) (Some 3) (fun k => k) = Some 39.
Compute lifted_minus_cps (Some 35) (Some 7) (fun k => lifted_division k (Some 2))
= Some 14.

Compute lifted_minus_cps (Some 42) None (fun k => k) = None.
Compute lifted_minus_cps (Some 43) None (fun k => lifted_times k (Some 3)) = None.

(* lifted_times_cps *)
Compute lifted_times_cps (Some 6) (Some 7) (fun k => k) = Some 42.
Compute lifted_times_cps (Some 9) (Some 6) (fun k => lifted_division k (Some 2))
= Some 27. (* remainder: 1 *)

Compute lifted_times_cps (Some 42) None (fun k => k) = None.
Compute lifted_times_cps (Some 43) None (fun k => lifted_times k (Some 3)) = None.

(* lifted_division_cps *)
Compute lifted_division_cps (Some 35) (Some 3) (fun k => k)
= Some 11. (* remainder: 2 *)
Compute lifted_division_cps (Some 42) (Some 7) (fun k => lifted_division k (Some 2))
= Some 3.

Compute lifted_division_cps (Some 42) None (fun k => k) = None.
Compute lifted_division_cps (Some 42) None (fun k => lifted_times k (Some 3)) = None.

(* Composite test *)
Compute (lifted_plus_cps
  (lifted_times_cps (Some 6) (Some 7) (fun k => lifted_plus k (Some 1)))
  (lifted_minus_cps (Some 5) (Some 4) (fun k => lifted_times k (Some 2)))
  (fun k => k)) = Some 45.

(* Continuation test *)
Compute lifted_plus_cps (Some 42) None
= fun x : option nat -> option nat => x None.
Compute lifted_times_cps (Some 6) (Some 7)
= fun x : option nat -> option nat =>  x (Some 42).

(* Tests -  interpret_cps *)

(* Lit *)
Compute (interpret_cps (Lit 5)
  (fun k => k)) = Some 5.
Compute (interpret_cps (Lit 5)
  (fun k => lifted_times k (Some 2))) = Some 10.

(* Plus *)
Compute (interpret_cps (Plus (Lit 3) (Lit 7))
  (fun k => k)) = Some 10.
Compute (interpret_cps (Plus (Lit 3) (Lit 7))
  (fun k => lifted_minus k (Some 1))) = Some 9.

(* Minus *)
Compute (interpret_cps (Minus (Lit 7) (Lit 4)))
(fun k => k) = Some 3.
Compute (interpret_cps (Minus (Lit 7) (Lit 4)))
(fun k => lifted_times k k) = Some 9.

(* Times *)
Compute (interpret_cps (Times (Lit 7) (Lit 6)))
(fun k => k) = Some 42.
Compute (interpret_cps (Times (Lit 7) (Lit 6)))
(fun k => lifted_division k (Some 8)) = Some 5. (* remainder: 2 *)

(* Divide *)
Compute (interpret_cps (Divide (Lit 42) (Lit 4)))
(fun k => k) = Some 10. (* remainder: 2 *)
Compute (interpret_cps (Divide (Lit 42) (Lit 4)))
(fun k => lifted_plus k (Some 7)) = Some 17. (* remainder: 2 *)

Compute (interpret_cps (Divide (Lit 5) (Lit 0))
  (fun k => lifted_plus k (Some 2))) = None.

(* Composite *)
Compute (interpret_cps (Plus (Times (Lit 2) (Lit 6)) (Times (Lit 6) (Lit 5)))
(fun k => lifted_division k (Some 2))) = Some 21.

Compute (interpret_cps (Minus (Divide (Lit 12) (Lit 3)) (Divide (Lit 6) (Lit
  2))) (fun k => lifted_plus k (Some 2))) = Some 3.

Compute (interpret_cps (Divide (Lit 42) (Minus (Lit 5) (Lit 5)))
  (fun k => lifted_plus k (Some 2))) = None.

(* Continuation *)
Compute (interpret_cps (Times (Lit 6) (Plus (Lit 5) (Lit 2))))
= fun x : option nat -> option nat => x (Some 42).
Compute (interpret_cps (Divide (Lit 42) (Minus (Lit 5) (Lit 5))))
= fun x : option nat -> option nat => x None.

(* Tests -  interpret' *)

(* Lit *)
Compute (interpret' (Lit 5)) = Some 5.

(* Plus *)
Compute (interpret' (Plus (Lit 3) (Lit 7))) = Some 10.

(* Minus *)
Compute (interpret' (Plus (Lit 12) (Lit 7))) = Some 19.

(* Times *)
Compute (interpret' (Times (Lit 3) (Lit 7))) = Some 21.

(* Divide *)
Compute (interpret' (Divide (Lit 36) (Lit 3))) = Some 12.

(* Composite *)
Compute (interpret' (Plus (Times (Lit 2) (Lit 6)) (Times (Lit 6) (Lit 5)))) =
Some 42.

Compute (interpret' (Divide (Lit 5) (Lit 0))) = None.

(* Tests - Relations *)
Definition k_test (on : option nat) : option nat :=
  lifted_times on (Some 2).

Compute k_test (lifted_plus (Some 2) (Some 3)) =
lifted_plus_cps (Some 2) (Some 3) k_test.

Compute k_test (lifted_minus (Some 10) (Some 3)) =
lifted_minus_cps (Some 10) (Some 3) k_test.

Compute k_test (lifted_times (Some 2) (Some 5)) =
lifted_times_cps (Some 2) (Some 5) k_test.

Compute k_test (lifted_division (Some 9) (Some 3)) =
lifted_division_cps (Some 9) (Some 3) k_test.

(* Tests - interpret_cps_opt *)

(* Lit *)
Compute (interpret_cps_opt (Lit 5)
  (fun k => Some k)) = Some 5.
Compute (interpret_cps_opt (Lit 5)
  (fun k => Some (k * 2))) = Some 10.

(* Plus *)
Compute (interpret_cps_opt (Plus (Lit 3) (Lit 7))
  (fun k => Some k)) = Some 10.
Compute (interpret_cps_opt (Plus (Lit 3) (Lit 7))
  (fun k => Some (k - 1))) = Some 9.

(* Minus *)
Compute (interpret_cps_opt (Minus (Lit 7) (Lit 4)))
(fun k => Some k) = Some 3.
Compute (interpret_cps_opt (Minus (Lit 7) (Lit 4)))
(fun k => Some (k *k)) = Some 9.

(* Times *)
Compute (interpret_cps_opt (Times (Lit 7) (Lit 6)))
(fun k => Some k) = Some 42.
Compute (interpret_cps_opt (Times (Lit 7) (Lit 6)))
(fun k => Some (k + 8)) = Some 50.

(* Divide *)
Compute (interpret_cps_opt (Divide (Lit 42) (Lit 4)))
(fun k => Some k) = Some 10. (* remainder: 2 *)
Compute (interpret_cps_opt (Divide (Lit 42) (Lit 4))
(fun k => Some (k + 7))) = Some 17. (* remainder: 2 *)
Compute (interpret_cps_opt (Divide (Lit 5) (Lit 0))
  (fun k => Some (k + 2))) = None.

(* Composite *)
Compute (interpret_cps_opt (Plus (Times (Lit 2) (Lit 6)) (Times (Lit 6) (Lit 5)))
(fun k => Some (k - 2))) = Some 40.

Compute (interpret_cps_opt (Minus (Divide (Lit 12) (Lit 3)) (Divide (Lit 6) (Lit
  2))) (fun k => Some (k + 2))) = Some 3.

Compute (interpret_cps_opt (Divide (Lit 42) (Minus (Lit 5) (Lit 5)))
  (fun k => Some (k + 2))) = None.

(* Continuation *)
Compute (interpret_cps_opt (Times (Lit 6) (Plus (Lit 5) (Lit 2))))
= fun k : nat -> option nat => k 42.
Compute (interpret_cps_opt (Divide (Lit 42) (Minus (Lit 5) (Lit 5))))
= fun _ : nat -> option nat => None.

(* Tests - interpret'_opt *)

(* Lit *)
Compute (interpret'_opt (Lit 5)) = Some 5.

(* Plus *)
Compute (interpret'_opt (Plus (Lit 3) (Lit 7))) = Some 10.

(* Minus *)
Compute (interpret'_opt (Plus (Lit 12) (Lit 7))) = Some 19.

(* Times *)
Compute (interpret'_opt (Times (Lit 3) (Lit 7))) = Some 21.

(* Divide *)
Compute (interpret'_opt (Divide (Lit 36) (Lit 3))) = Some 12.

(* Composite *)
Compute (interpret'_opt (Plus (Times (Lit 2) (Lit 6)) (Times (Lit 6) (Lit 5)))) =
Some 42.

Compute (interpret'_opt (Divide (Lit 5) (Lit 0))) = None.

(* end-of-Tests.v *)