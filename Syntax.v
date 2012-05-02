(* File: Syntax.v *)
(* Author: Peter Urbak <peter@dragonwasrobot.com> *)
(* Version: 2012-05-02 *)

(*
   This script shows how to:
   1. Define a simple arithmetic language.
*)

(* -*- The Source Syntax. -*- *)

Inductive arithmetic_expression : Type :=
  | Lit : nat -> arithmetic_expression
  | Plus : arithmetic_expression -> arithmetic_expression ->
    arithmetic_expression
  | Minus : arithmetic_expression -> arithmetic_expression ->
    arithmetic_expression
  | Times : arithmetic_expression -> arithmetic_expression ->
    arithmetic_expression
  | Divide : arithmetic_expression -> arithmetic_expression ->
    arithmetic_expression.

(* end-of-Syntax.v *)