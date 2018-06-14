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

Notation TRIPCOUNT := 100%Z.

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

Definition branch (v: texp) (br1: string) (br2: string): terminator :=
  TERM_Br v (Name br1) (Name br2).

Definition exp_ident (s: string): exp :=
  EXP_Ident (ID_Local (Name s)).

Definition texp_ident (s: string): texp :=
  (i32TY, exp_ident s).

Definition exp_const_z(z: Z): exp := EXP_Integer z.

Definition texp_const_z (z: Z): texp :=
  (i32TY, exp_const_z z).


Definition texp_to_exp (te: texp): exp := snd te.

Definition exp_gep_at_ix (arrty: typ) (ident: string) (ix: texp) : texp :=
  (arrty, OP_GetElementPtr arrty
                   (TYPE_Pointer arrty, (texp_to_exp (texp_ident ident)))
                   [ix]).

Definition inst_store (val: texp) (ix: texp): instr :=
  INSTR_Store false val ix None.

Definition alloca_array (name: string) (nbytes: Z): instr_id * instr :=
  (IId (Name name), INSTR_Alloca i32PTRTY
                                 (Some ((TYPE_I (32%Z)), EXP_Integer nbytes))
                                 None).

Definition arr_ty := (TYPE_Array TRIPCOUNT i32TY).

Definition exp_add (v1: exp) (v2: exp): exp :=
  OP_IBinop (LLVMAst.Add false false) (i32TY) v1 v2.

Definition exp_lt (v1: exp) (v2: exp): exp :=
  OP_ICmp Ule (i32TY) v1 v2.

Definition exp_increment_ident (name: string): exp :=
  exp_add (exp_ident "name") (exp_const_z 1).

Definition bbInit: block := 
    {|
      blk_id := Name "init";
      blk_phis  := [];
      blk_code  := [alloca_array "arr" TRIPCOUNT];
      blk_term := (IVoid 0%Z, break "loop");
    |}.


Definition bbLoop :=
  {|
    blk_id := Name "loop";
    blk_phis := [(Name "iv",
                  Phi i32TY [
                        (Name "init", exp_const_z 0);
                        (Name "loop", exp_ident "iv.next")
                ])];
    blk_code := [(IVoid 100%Z, inst_store (texp_ident "iv")
                            (exp_gep_at_ix arr_ty
                                           "arr"
                                           (texp_ident "iv")));
                   (IId (Name "iv.next"), INSTR_Op (exp_increment_ident "iv"));
                   (IId (Name "cond"), INSTR_Op (exp_lt (exp_ident "iv.next")
                                                       (exp_const_z TRIPCOUNT)
                ))];
                
    blk_term := (IVoid 101%Z, branch (texp_ident "cond") "loop" "exit");
  |}.

                       
Definition bbExit : block :=
  {| blk_id := Name "exit";
     blk_phis := [];
     blk_code := [];
     blk_term := (IVoid 10%Z, TERM_Ret (texp_ident "val"));
  |}.

Instance bb_eq_decidable: eq_dec (block).
Proof.
Admitted.

Locate "&&".

Definition try_rewrite_main_blks (bbs: list block): option (list block) :=
  match bbs with
  | [x1;x2; x3] => if (x1 == bbInit)
                  then if (x2 == bbLoop)
                       then if (x3 == bbExit)
                                 then Some [bbExit]
                            else None
                       else None
                  else None
  | _ => None
  end.
                                                      
Definition try_rewrite_main_cfg (c: cfg) : option cfg :=
  option_map (fun blks' => {| init := init c;
                           blks := blks';
                           args := args c;
              |}) (try_rewrite_main_blks (blks c)).

Definition try_rewrite_main_definition (d: definition cfg):
  option (definition cfg) :=
  if dc_name (df_prototype d) == (Name "main")
  then option_map (fun cfg' =>
                  mk_definition cfg
                                (df_prototype d) 
                                (df_args d)
                                (cfg')
                  ) (try_rewrite_main_cfg (df_instrs d))
  else None.
         

  
Definition try_rewrite_mcfg (MCFG:mcfg) : option mcfg :=
  option_map (fun defn' =>
                {| m_name := m_name MCFG;
                   m_target:= m_target MCFG;
                   m_datalayout := m_datalayout MCFG;
                   m_type_defs := m_type_defs MCFG;
                   m_globals := m_globals MCFG;
                   m_declarations := m_declarations MCFG;
                   m_definitions := [defn'];
                |})
             match (m_globals MCFG,
                    m_declarations MCFG, m_definitions MCFG) with
             | ([], [], [defn]) => try_rewrite_main_definition defn
             | (_, _, _) => None
             end.

Definition rewrite_mcfg (MCFG: mcfg) : mcfg :=
  match try_rewrite_mcfg MCFG with
  | Some mcfg' => mcfg'
  | None => MCFG
  end.
                        
  