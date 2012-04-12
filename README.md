Simple CPS Interpreter
======================

## What is this?
The idea behind this project is to show how to:

* Define the syntax for a simple (arithmetic) language.
* Write a direct style interpreter for the language.
* Convert it to a straightforward continuation passing style interpreter.
* Optimize the interpreter such that it immediately halts when a division by zero occurs.
* Prove the correctness of the optimized interpreter in relation to the direct style interpreter.

## General

- **Author:** Peter Urbak, peter@dragonwasrobot.com
- **Created:** 2012-04-12
- **Last Modified:** 2012-04-12
- **URL:** https://github.com/dragonwasrobot/Simple-CPS-Interpreter
- **License:** Gnu General Public License

## Install

- Simply compile the Division.v and Cases.v files using the coqc command.
- If you don't have Coq installed you can get it here http://coq.inria.fr/ (at the same time I will also recommend using http://proofgeneral.inf.ed.ac.uk/ for emacs). Coq and Proofgeneral can usually also be installed using either your favorite Linux repository or Homebrew for OS/X.

## To-do

* Handle immediate action when A tries to subtract something greater than itself.
* Add a Compiler and Stack etc. (probably have to rename project then).
* Prove equivalence between the results of 'Compiler+Execute ae' and 'Interpret ae'.
* Small install script that compiles the coq files.