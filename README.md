Simpl Lang
======================

## What is this?
The idea behind this project is to create a small show how to:

* Language
  * Define the syntax for a simple (arithmetic) language.

* Interpreter
  * Write a direct style interpreter for the language.
  * Convert it to a straightforward continuation passing style interpreter.
  * Optimize the interpreter such that it immediately halts when a division by
     zero occurs.
  * Prove the correctness of the optimized interpreter in relation to the direct
    style interpreter.

* Compiler
  * Create simple byte code instructions for the language to be compiled to.
  * Create a function which can executes the byte code.
  * Write a simple compiler which compiles simpl lang source code into byte
    code.
  * Prove the equivalence between compiling and running a piece of simpl lang
    source code and directly interpreting it.
  * Improve the compiler and prove equality.

* Decompiler
  * Write a decompiler which converts bytecode back into source code.

## General

- **Author:** Peter Urbak, peter@dragonwasrobot.com
- **Created:** 2012-04-12
- **Last Modified:** 2012-04-12
- **URL:** https://github.com/dragonwasrobot/Simple-CPS-Interpreter
- **License:** Gnu General Public License

## Install

- Simply compile the Division.v and Cases.v files using the coqc command.
- If you don't have Coq installed you can get it here http://coq.inria.fr/ (at
- the same time I will also recommend using http://proofgeneral.inf.ed.ac.uk/
- for emacs). Coq and Proofgeneral can usually also be installed using either
- your favorite Linux repository or Homebrew for OS/X.

## To-do

* Change syntax of tests from compute to lemma (or likewise) so verification can be automated.
* Handle immediate action when A tries to subtract something greater than itself.
* Prove equivalence between the results of 'Compiler+Execute ae' and 'Interpret ae'.
* Small install script that compiles the coq files.