(* File: Interpreter.v *)
(* Author: Peter Urbak <peter@dragonwasrobot.com> *)
(* Version: 2012-05-02 *)

(*
   This script shows how to:
   1. Write a direct style interpreter for the language.
   2. Convert it to a straightforward continuation passing style interpreter.
   3. Optimize the interpreter such that it immediately halts when a division by
   zero occurs.
   4. Prove the correctness of the optimized interpreter in relation to the
   direct style interpreter.
*)

(* Note: for pedagogical reasons, there is no use of tactics like simpl, auto,
   etc. likewise, there are proofs which could be significantly shortened using
   ';' but have also been left in their more explicit versions. *)

(* -*- Requirements. -*- *)

Require Export Cases List Division Syntax.

(* -*- Functions for doing basic arithmetic on the 'option nat' type. -*- *)

Definition lifted_operator (o1 o2: option nat) (op : nat -> nat -> nat) :
  option nat :=
  match o1, o2 with
    | (Some n1), (Some n2) => Some(op n1 n2)
    | _, _ => None
  end.

Definition lifted_plus (o1 o2 : option nat) : option nat :=
  lifted_operator o1 o2 plus.

Definition lifted_minus (o1 o2 : option nat) : option nat :=
  lifted_operator o1 o2 minus.

Definition lifted_times (o1 o2 : option nat) : option nat :=
  lifted_operator o1 o2 mult.

Definition lifted_division (o1 o2 : option nat) : option nat :=
  match o1, o2 with
    | (Some n1), (Some n2) => match n1 / n2 with
                                | Some (q,r) => Some q
                                | None => None
                              end
    | _, _ => None
  end.

(* -*- The Direct Style Interpreter. -*- *)

Fixpoint interpret (ae : arithmetic_expression) : option nat :=
  match ae with
    | Lit n => Some n
    | Plus e1 e2 => lifted_plus (interpret e1) (interpret e2)
    | Minus e1 e2 => lifted_minus (interpret e1) (interpret e2)
    | Times e1 e2 => lifted_times (interpret e1) (interpret e2)
    | Divide e1 e2 => lifted_division (interpret e1) (interpret e2)
  end.

(* -*- A Straightforward CPS version of the Interpreter. -*- *)

(* Naive CPS versions of the lifted_X functions where the continuation function
   k is also applied to None. *)

Definition lifted_operator_cps (o1 o2 : option nat)
  (op: nat -> nat -> nat) (k : option nat -> option nat) : option nat :=
  match o1, o2 with
    | (Some n1), (Some n2) => k (Some (op n1 n2))
    | _, _ => k None
  end.

Definition lifted_plus_cps (o1 o2 : option nat)
  (k : option nat -> option nat) : option nat :=
  lifted_operator_cps o1 o2 plus k.

Definition lifted_minus_cps (o1 o2 : option nat)
  (k : option nat -> option nat) : option nat :=
  lifted_operator_cps o1 o2 minus k.

Definition lifted_times_cps (o1 o2 : option nat)
  (k : option nat -> option nat) : option nat :=
  lifted_operator_cps o1 o2 mult k.

Definition lifted_division_cps (o1 o2 : option nat)
  (k : option nat -> option nat) : option nat :=
  match o1, o2 with
    | (Some n1), (Some n2) => match n1 / n2 with
                                | Some (q,r) => k (Some q)
                                | None => k None
                              end
    | _, _ => k None
  end.

(* -*- The straightforward CPS version of the Interpreter. -*- *)

Fixpoint interpret_cps (ae : arithmetic_expression)
  (k : option nat -> option nat) : option nat :=
  match ae with
    | Lit n => k (Some n)
    | Plus e1 e2 => (interpret_cps e1
      (fun n1 => interpret_cps e2
        (fun n2 => (lifted_plus_cps n1 n2 k))))
    | Minus e1 e2 => (interpret_cps e1
      (fun n1 => interpret_cps e2
        (fun n2 => (lifted_minus_cps n1 n2 k))))
    | Times e1 e2 => (interpret_cps e1
      (fun n1 => interpret_cps e2
        (fun n2 => (lifted_times_cps n1 n2 k))))
    | Divide e1 e2 => (interpret_cps e1
      (fun n1 => interpret_cps e2
        (fun n2 => (lifted_division_cps n1 n2 k))))
  end.

Definition interpret' (ae : arithmetic_expression) : option nat :=
  interpret_cps ae (fun k => k).

(* -*- Equivalence between direct style Interpreter and CPS version. -*- *)

(* First we prove the relation between each lifted_X and lifted_X_cps *)

(* Proofs - Relation *)

Lemma relation_between_lifted_operator_and_lifted_operator_cps :
  forall (o1 o2 : option nat) (op : nat -> nat -> nat)
    (k: option nat -> option nat),
    k (lifted_operator o1 o2 op) = lifted_operator_cps o1 o2 op k.
Proof.
  intros o1 o2 op k.
  case o1 as [ n | ].

  Case "o1 = (Some n)".
  unfold lifted_operator_cps.
  unfold lifted_operator.
  case o2 as [ n' | ].

  SCase "o2 = (Some n')".
  reflexivity.

  SCase "o2 = None".
  reflexivity.

  Case "o1 = None".
  unfold lifted_operator.
  unfold lifted_operator_cps.
  reflexivity.
Qed.

Corollary relation_between_lifted_plus_and_lifted_plus_cps :
  forall (o1 o2 : option nat) (k: option nat -> option nat),
    k (lifted_plus o1 o2) = lifted_plus_cps o1 o2 k.
Proof.
  intros o1 o2 k.
  unfold lifted_plus_cps.
  unfold lifted_plus.
  apply relation_between_lifted_operator_and_lifted_operator_cps.
Qed.

Corollary relation_between_lifted_minus_and_lifted_minus_cps :
  forall (o1 o2 : option nat) (k: option nat -> option nat),
    k (lifted_minus o1 o2) = lifted_minus_cps o1 o2 k.
Proof.
  intros o1 o2 k.
  unfold lifted_minus_cps.
  unfold lifted_minus.
  apply relation_between_lifted_operator_and_lifted_operator_cps.
Qed.

Corollary relation_between_lifted_times_and_lifted_times_cps :
  forall (o1 o2 : option nat) (k: option nat -> option nat),
    k (lifted_times o1 o2) = lifted_times_cps o1 o2 k.
Proof.
  intros o1 o2 k.
  unfold lifted_times_cps.
  unfold lifted_times.
  apply relation_between_lifted_operator_and_lifted_operator_cps.
Qed.

Lemma relation_between_lifted_division_and_lifted_division_cps :
  forall (o1 o2 : option nat) (k : option nat -> option nat),
    k (lifted_division o1 o2) = lifted_division_cps o1 o2 k.
Proof.
  intros o1 o2 k.
  case o1 as [ n | ].

  Case "o1 = Some n".
  unfold lifted_division_cps.
  unfold lifted_division.
  case o2 as [ n' | ].

  SCase "o2 = Some n'".
  unfold division.
  case (quotient_and_remainder n n') as [S | ].

  SSCase "(quotient_and_remainder n n') = Some (q, _)".
  case S as [ n'' ].

  SSSCase "S = Some n''".
  reflexivity.

  SSCase "(quotient_and_remainder n n') = None".
  reflexivity.

  SCase "o2 = None".
  reflexivity.

  Case "o1 = None".
  unfold lifted_division.
  unfold lifted_division_cps.
  reflexivity.
Qed.

(* We now prove the relation between interpret and interpret_cps *)

(* Proof - Relation *)

Lemma relation_between_interpret_and_interpret_cps :
  forall (ae : arithmetic_expression) (k : (option nat) -> (option nat)),
    k (interpret ae) = interpret_cps ae k.
Proof.
  intro ae.
  induction ae.

  Case "ae = (Lit n)".
  intro k.
  unfold interpret_cps.
  unfold interpret.
  reflexivity.

  Case "ae = (Plus ae1 ae2)".
  intro k.
  unfold interpret_cps.
  fold interpret_cps.
  unfold interpret.
  fold interpret.
  rewrite <- IHae1.
  rewrite <- IHae2.
  rewrite relation_between_lifted_plus_and_lifted_plus_cps.
  reflexivity.

  Case "ae = (Minus ae1 ae2)".
  intro k.
  unfold interpret_cps.
  fold interpret_cps.
  unfold interpret.
  fold interpret.
  rewrite <- IHae1.
  rewrite <- IHae2.
  rewrite <- relation_between_lifted_minus_and_lifted_minus_cps.
  reflexivity.

  Case "ae = (Times ae1 ae2)".
  intro k.
  unfold interpret_cps.
  fold interpret_cps.
  unfold interpret.
  fold interpret.
  rewrite <- IHae1.
  rewrite <- IHae2.
  rewrite <- relation_between_lifted_times_and_lifted_times_cps.
  reflexivity.

  Case "ae = (Divide ae1 ae2)".
  intro k.
  unfold interpret_cps.
  fold interpret_cps.
  unfold interpret.
  fold interpret.
  rewrite <- IHae1.
  rewrite <- IHae2.
  rewrite <- relation_between_lifted_division_and_lifted_division_cps.
  reflexivity.
Qed.

Theorem equivalence_of_interpret_and_interpret' :
  forall (ae : arithmetic_expression),
    interpret ae = interpret' ae.
Proof.
  intro ae.
  unfold interpret'.
  rewrite <- relation_between_interpret_and_interpret_cps.
  reflexivity.
Qed.

(* -*- An optimized CPS Interpreter where immediate action is taken whenever a
   division by zero occurs. -*- *)

Fixpoint interpret_cps_opt (ae : arithmetic_expression)
  (k : nat -> option nat) : option nat :=
  match ae with
    | Lit n => (k n)
    | Plus e1 e2 => (interpret_cps_opt e1
      (fun n1 => interpret_cps_opt e2
        (fun n2 => (k (n1 + n2)))))
    | Minus e1 e2 => (interpret_cps_opt e1
      (fun n1 => interpret_cps_opt e2
        (fun n2 => k (n1 - n2))))
    | Times e1 e2 => (interpret_cps_opt e1
      (fun n1 => interpret_cps_opt e2
        (fun n2 => k (n1 * n2))))
    | Divide e1 e2 => (interpret_cps_opt e1
      (fun n1 => interpret_cps_opt e2
        (fun n2 => match (n1 / n2) with
                       | Some(q,r) => k q
                       | None => None
                       end)))
  end.

Definition interpret'_opt (ae : arithmetic_expression) :=
  interpret_cps_opt ae (fun k => Some (k)).

(* -*- Correctness proof of the optimized Interpreter. -*- *)

(* Proof - Relation *)
Lemma relation_between_interpret_and_interpret_cps_opt :
  forall (ae : arithmetic_expression) (k: nat -> option nat),
    interpret_cps_opt ae k = match (interpret ae) with
                               | Some n => k n
                               | None => None
                             end.
Proof.
  intro ae.
  induction ae.

  Case "ae = (Lit n)".
  intro k.
  unfold interpret_cps_opt.
  unfold interpret.
  reflexivity.

  Case "ae = (Plus ae1 ae2)".
  intro k.
  unfold interpret_cps_opt.
  fold interpret_cps_opt.
  unfold interpret.
  fold interpret.
  unfold lifted_plus.
  rewrite -> IHae1.
  case (interpret ae1) as [ n | ].

  SCase "(interpret ae1) = Some n".
  rewrite -> IHae2.
  case (interpret ae2) as [ n' | ].

  SSCase "(interpret ae2) = Some n'".
  reflexivity.

  SSCase "(interpret ae2) = None".
  reflexivity.

  SCase "(interpret ae1) = None".
  reflexivity.

  Case "ae = (Minus ae1 ae2)".
  intro k.
  unfold interpret_cps_opt.
  fold interpret_cps_opt.
  unfold interpret.
  fold interpret.
  unfold lifted_minus.
  rewrite -> IHae1.
  case (interpret ae1) as [ n | ].

  SCase "(interpret ae1) = Some n".
  rewrite -> IHae2.
  case (interpret ae2) as [ n' | ].

  SSCase "(interpret ae2) = Some n'".
  reflexivity.

  SSCase "(interpret ae2) = None".
  reflexivity.

  SCase "(interpret ae1) = None".
  reflexivity.

  Case "ae = (Times ae1 ae2)".
  intro k.
  unfold interpret_cps_opt.
  fold interpret_cps_opt.
  unfold interpret.
  fold interpret.
  unfold lifted_times.
  rewrite -> IHae1.
  case (interpret ae1) as [ n | ].

  SCase "(interpret ae1) = Some n".
  rewrite -> IHae2.
  case (interpret ae2) as [ n' | ].

  SSCase "(interpret ae2) = Some n'".
  reflexivity.

  SSCase "(interpret ae2) = None".
  reflexivity.

  SCase "(interpret ae1) = None".
  reflexivity.

  Case "ae = (Divide ae1 ae2)".
  intro k.
  unfold interpret_cps_opt.
  fold interpret_cps_opt.
  unfold interpret.
  fold interpret.
  unfold lifted_division.
  rewrite -> IHae1.
  case (interpret ae1) as [ n | ].

  SCase "(interpret ae1) = Some n".
  rewrite -> IHae2.
  case (interpret ae2) as [ n' | ].

  SSCase "(interpret ae2) = Some n'".
  unfold division.
  case (quotient_and_remainder n n') as [ S | ].

  SSSCase "(quotient_and_remainder n n') = Some (q, _)".
  case S as [ n'' ].

  SSSSCase "S = Some n''".
  reflexivity.

  SSSCase "(quotient_and_remainder n n') = None".
  reflexivity.

  SSCase "(interpret ae2) = None".
  reflexivity.

  SCase "(interpret ae1) = None".
  reflexivity.
Qed.

Theorem equivalence_of_interpret_and_interpret'_opt :
  forall (ae : arithmetic_expression),
    interpret ae = interpret'_opt ae.
Proof.
  intro ae.
  unfold interpret'_opt.
  rewrite -> relation_between_interpret_and_interpret_cps_opt.
  case (interpret ae) as [ n | ].

  Case "(interpret ae) = Some n".
  reflexivity.

  Case "(interpret ae) = None".
  reflexivity.
Qed.

(* end-of-Interpreter.v *)
