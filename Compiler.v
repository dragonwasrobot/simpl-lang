(* File: Compiler.v *)
(* Author: Peter Urbak <peter@dragonwasrobot.com> *)

(*
   This script shows how to:
   1. Define simple byte code instructions.
   2. Write a simple compiler which compiles simpl lang source code into byte
      code.
   3. Optimize the compiler and prove equivalence.
   4. Prove the equivalence between compiling and running a piece of simpl lang
      source code and directly interpreting it.

*)

Require Export Plus Cases List Syntax Interpreter.

(* Byte-code instructions: *)

Inductive byte_code_instruction : Type :=
  | PUSH : option nat -> byte_code_instruction
  | ADD : byte_code_instruction
  | SUB : byte_code_instruction
  | MUL : byte_code_instruction
  | DIV : byte_code_instruction.

(* Byte-code programs: *)

Definition byte_code_program := list byte_code_instruction.

(* Data stack: *)

Definition data_stack := list (option nat).

(* Execute Byte Code Instruction *)

(* Note: All proofs compile but pretty sure the execute_program isn't working as
   intended. *)

Fixpoint execute_byte_code_instruction
  (bc : byte_code_instruction) (s : data_stack) : list (option nat) :=
  match bc, s with
    | PUSH n, s' => n :: s'
    | ADD, nil => nil
    | ADD, n :: nil => n :: nil
    | ADD, n1 :: n2 :: s' => (lifted_plus n1 n2) :: s'
    | SUB, nil => nil
    | SUB, n :: nil => n :: nil
    | SUB, n1 :: n2 :: s' => (lifted_minus n1 n2) :: s'
    | MUL, nil => nil
    | MUL, n :: nil => n :: nil
    | MUL, n1 :: n2 :: s' => (lifted_times n1 n2) :: s'
    | DIV, nil => nil
    | DIV, n :: nil => n :: nil
    | DIV, n1 :: n2 :: s' => (lifted_division n1 n2) :: s'
  end.

Example execute_div_instruction_example: (execute_byte_code_instruction
  DIV ((Some 30) :: (Some 3) :: nil)) = (Some 10 :: nil).
Proof. reflexivity. Qed.

Compute (execute_byte_code_instruction (PUSH (Some 3)) (execute_byte_code_instruction
  (PUSH (Some 5)) nil)) = (Some 3) :: (Some 5) :: nil.
Compute (execute_byte_code_instruction ADD ((Some 2) :: (Some 3) :: nil)) =
  (Some 5) :: nil.
Compute (execute_byte_code_instruction MUL ((Some 3) :: (Some 7) :: nil)) =
  (Some 21) :: nil.
Compute (execute_byte_code_instruction MUL (execute_byte_code_instruction
  (PUSH (Some 6)) (execute_byte_code_instruction (PUSH (Some 7)) nil))) =
  ((Some 42) :: nil).
Compute (execute_byte_code_instruction MUL ((Some 3) :: nil)) = ((Some 3) :: nil).
Compute (execute_byte_code_instruction SUB ((Some 10) :: (Some 3) :: nil)) =
((Some 7) :: nil).
Compute (execute_byte_code_instruction DIV ((Some 30) :: (Some 3) :: nil)) =
((Some 10) :: nil).

(* Execute Byte Code Porgram *)

Fixpoint execute_byte_code_program
  (bcp : byte_code_program) (s : data_stack) : list (option nat) :=
  match bcp, s with
    | nil, s' => s'
    | bci :: bcp', s' =>
      execute_byte_code_program bcp' (execute_byte_code_instruction bci s')
  end.

Example  execute_example_1: (execute_byte_code_program
  ((PUSH (Some 3)) :: (PUSH (Some 30)) :: DIV :: nil) nil) = ((Some 10) :: nil).
Proof. reflexivity. Qed.

Lemma unfold_execute_byte_code_program_base_case :
  forall (s : data_stack),
  execute_byte_code_program nil s = s.
Proof.
  intro s.
  unfold execute_byte_code_program.
  reflexivity.
Qed.

Lemma unfold_execute_byte_code_program_inductive_case :
  forall (bcp : byte_code_program) (bci : byte_code_instruction)
    (s : data_stack),
  execute_byte_code_program (bci :: bcp) s =
  execute_byte_code_program bcp (execute_byte_code_instruction bci s).
Proof.
  intros bcp bci s.
  unfold execute_byte_code_program.
  fold execute_byte_code_program.
  reflexivity.
Qed.

Compute execute_byte_code_program
((PUSH (Some 5)) :: (PUSH (Some 3)) :: ADD :: nil) nil = ((Some 8):: nil).
Compute execute_byte_code_program
((PUSH (Some 3)) :: (PUSH (Some 9)) :: DIV :: nil) nil = ((Some 3):: nil).
Compute execute_byte_code_program
((PUSH (Some 4)) :: (PUSH (Some 10)) :: SUB :: nil) nil = ((Some 6):: nil).


Compute execute_byte_code_program (MUL :: nil)
(execute_byte_code_program ((PUSH (Some 5)) :: (PUSH (Some 3)) :: ADD :: nil)
  ((Some 3) :: nil))
= ((Some 24) :: nil).

Compute execute_byte_code_program (DIV :: nil)
(execute_byte_code_program ((PUSH (Some 3)) :: (PUSH (Some 30)) :: SUB :: nil)
  ((Some 4) :: nil))
= ((Some 6) :: nil).

(* Associativity *)

Lemma execute_byte_code_program_is_associative
  : forall (p1 p2 : list byte_code_instruction) (s : data_stack),
    execute_byte_code_program (p1 ++ p2) s =
    execute_byte_code_program p2 (execute_byte_code_program p1 s).
Proof.
  induction p1 as [ | p' ps].

  Case "p = nil".
  intros p2 s.
  unfold execute_byte_code_program.
  fold execute_byte_code_program.
  unfold app.
  reflexivity.

  Case "p = p' :: ps".
  intros p2 s.
  unfold execute_byte_code_program.
  fold execute_byte_code_program.
  rewrite <- IHps.
  unfold execute_byte_code_program.
  unfold app.
  fold execute_byte_code_program.
  reflexivity.
Qed.

(* ********** *)

(* A simple compiler: *)

Fixpoint compile (ae : arithmetic_expression) : byte_code_program :=
  match ae with
    | Lit n => PUSH (Some n) :: nil
    | Plus e1 e2 => (compile e2) ++ (compile e1) ++ (ADD :: nil)
    | Minus e1 e2 => (compile e2) ++ (compile e1) ++ (SUB :: nil)
    | Times e1 e2 => (compile e2) ++ (compile e1) ++ (MUL :: nil)
    | Divide e1 e2 => (compile e2) ++ (compile e1) ++ (DIV :: nil)
  end.

Compute execute_byte_code_program
(compile (Times (Plus (Lit 3) (Lit 2)) (Plus (Lit 7) (Lit 3)))) nil = ((Some 50) :: nil).

Compute execute_byte_code_program
(compile (Times (Minus (Lit 10) (Lit 3)) (Divide (Lit 15) (Lit 3)))) nil = ((Some 35) :: nil).

(* Equality of interpretation and compiling followed by running. *)

Lemma equality_of_interpreting_and_compiling_and_then_running :
  forall (ae : arithmetic_expression) (s : data_stack),
    (interpret ae) :: s = execute_byte_code_program (compile ae) s.
Proof.
  intro ae.
  induction ae.

  Case "ae = (Lit n)".
  intro s.
  unfold interpret.
  unfold compile.
  unfold execute_byte_code_program.
  unfold execute_byte_code_instruction.
  unfold app.
  reflexivity.

  Case "ae = (Plus ae1 ae2)".
  intro s.
  unfold interpret.
  fold interpret.
  unfold compile.
  fold compile.
  rewrite ->2 execute_byte_code_program_is_associative.
  rewrite <- IHae1.
  rewrite <- IHae2.
  unfold execute_byte_code_program.
  unfold execute_byte_code_instruction.
  reflexivity.

  Case "ae = (Minus ae1 ae2)".
  intro s.
  unfold interpret.
  fold interpret.
  unfold compile.
  fold compile.
  rewrite ->2 execute_byte_code_program_is_associative.
  rewrite <- IHae1.
  rewrite <- IHae2.
  unfold execute_byte_code_program.
  unfold execute_byte_code_instruction.
  reflexivity.

  Case "ae = (Times ae1 ae2)".
  intro s.
  unfold interpret.
  fold interpret.
  unfold compile.
  fold compile.
  rewrite ->2 execute_byte_code_program_is_associative.
  rewrite <- IHae1.
  rewrite <- IHae2.
  unfold execute_byte_code_program.
  unfold execute_byte_code_instruction.
  reflexivity.

  Case "ae = (Divide ae1 ae2)".
  intro s.
  unfold interpret; fold interpret.
  unfold compile; fold compile.
  rewrite ->2 execute_byte_code_program_is_associative.
  rewrite <- IHae1.
  rewrite <- IHae2.
  unfold execute_byte_code_program.
  unfold execute_byte_code_instruction.
  reflexivity.
Qed.

(* Compiler with accumulator. *)

Fixpoint compile_aux (ae : arithmetic_expression) (a : byte_code_program) : byte_code_program :=
  match ae with
    | Lit n => PUSH (Some n) :: a
    | Plus e1 e2 => (compile_aux e2 (compile_aux e1 (ADD :: a)))
    | Minus e1 e2 => (compile_aux e2 (compile_aux e1 (SUB :: a)))
    | Times e1 e2 => (compile_aux e2 (compile_aux e1 (MUL :: a)))
    | Divide e1 e2 => (compile_aux e2 (compile_aux e1 (DIV :: a)))
  end.

Definition compile' (ae : arithmetic_expression) : byte_code_program :=
  compile_aux ae nil.

Compute execute_byte_code_program
(compile' (Times (Plus (Lit 3) (Lit 2)) (Plus (Lit 7) (Lit 3)))) nil = ((Some 50) :: nil).

Compute execute_byte_code_program
(compile' (Times (Minus (Lit 10) (Lit 3)) (Divide (Lit 15) (Lit 3)))) nil = ((Some 35) :: nil).

Lemma app_is_associative : forall (xs ys zs : byte_code_program),
  (xs ++ ys) ++ zs = xs ++ (ys ++ zs).
Proof.
  intro xs.
  induction xs as [ | x xs'].

  Case "xs = nil".
  intros ys zs.
  unfold app.
  reflexivity.

  Case "xs = x :: xs'".
  intros ys zs.
  unfold app.
  rewrite -> IHxs'.
  unfold app.
  reflexivity.
Qed.

Lemma nil_is_neutral_for_app_on_the_right : forall (xs : byte_code_program),
  xs ++ nil = xs.
Proof.
  Admitted.

Lemma equality_of_compile_and_compile_aux :
  forall (ae : arithmetic_expression) (a : byte_code_program),
    compile_aux ae a = (compile ae) ++ a.
Proof.
  intro ae.
  induction ae.

  Case "ae = (Lit n)".
  intro a.
  unfold compile.
  unfold app.
  unfold compile_aux.
  reflexivity.

  Case "ae = (Plus ae1 ae2)".
  intro a.
  unfold compile_aux.
  fold compile_aux.
  unfold compile.
  fold compile.
  rewrite -> IHae1.
  rewrite -> IHae2.
  rewrite ->2 app_is_associative.
  simpl.
  reflexivity.

  Case "ae = (Minus ae1 ae2)".
  intro a.
  unfold compile_aux.
  fold compile_aux.
  unfold compile.
  fold compile.
  rewrite -> IHae1.
  rewrite -> IHae2.
  rewrite ->2 app_is_associative.
  simpl.
  reflexivity.

  Case "ae = (Times ae1 ae2)".
  intro a.
  unfold compile_aux.
  fold compile_aux.
  unfold compile.
  fold compile.
  rewrite -> IHae1.
  rewrite -> IHae2.
  rewrite ->2 app_is_associative.
  simpl.
  reflexivity.

  Case "ae = (Divide ae1 ae2)".
  intro a.
  unfold compile_aux.
  fold compile_aux.
  unfold compile.
  fold compile.
  rewrite -> IHae1.
  rewrite -> IHae2.
  rewrite ->2 app_is_associative.
  simpl.
  reflexivity.
Qed.

(* ********** *)

(* end arithmetic-expressions.v *).
