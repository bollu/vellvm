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


Notation i32TY := (TYPE_I (32%Z)).
Definition i32ARRTY := (TYPE_Array 2 i32TY).
Definition i32ARRPTRTY := (TYPE_Pointer (TYPE_Array 2 i32TY)).
Definition i32PTRTY := (TYPE_Pointer i32TY).
Definition mkI32 (i: Z): texp := (i32TY, EXP_Integer i).


(* Make all constructions of IR in terms of functions *)
Definition patternMkGEPAtIx (ix: Z)  : texp :=
  ((TYPE_Array 2 i32TY), OP_GetElementPtr (TYPE_Array 2 (TYPE_I 32%Z))
                                          (TYPE_Pointer (TYPE_Array 2 (TYPE_I 32%Z)),
                                           EXP_Ident (ID_Local (Name "x")))
                                          [(i32TY, EXP_Integer ix)]).



Definition break (s: string): terminator :=
  TERM_Br_1 (Name s).

Definition bbInit: block := 
    {|
      blk_id := Name "init";
      blk_phis  := [];
      blk_code  := [];
      blk_term := (IVoid 0%Z, break "loopheader");
    |}.

                       
Definition exit : block :=
  {| blk_id := Name "exit";
     blk_phis := [];
     blk_code := [];
     blk_term := (IVoid 10%Z, TERM_Ret (i32TY, (EXP_Ident (ID_Local (Name "val")))))
  |}.

Definition codeToMatch  : code :=
     [(IId (Name "x"), INSTR_Alloca i32PTRTY (Some ((TYPE_I (32%Z)),  EXP_Integer 0)) None);
        (IVoid 0%Z, INSTR_Store  false (TYPE_I (32%Z), EXP_Integer 0)
                                 (patternMkGEPAtIx 0) None);
        (IVoid 1%Z, INSTR_Store  false (TYPE_I (32%Z), EXP_Integer 1) (patternMkGEPAtIx 1) None);
        (IId (Name "xat0"), INSTR_Load false (TYPE_I (32%Z)) (patternMkGEPAtIx 0) None)].