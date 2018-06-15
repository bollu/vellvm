(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Import Program.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.CFG.
Require Import List ListDec.
Require Import Vellvm.Pass.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Require Import Vellvm.Memory.


Fixpoint code_contains_funcall_dec (c: code): bool :=
  match c with
  | [] => false
  | (inst::cs) => match inst with
                 | (_, INSTR_Call _ _ ) => true
                 | _ => code_contains_funcall_dec cs
                 end
  end.
                                                
                                                
Lemma trace_of_bb_finite: 