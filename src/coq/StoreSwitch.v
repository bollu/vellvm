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

(*

Definition mkGEPI32 (name: string) (idx: Z) : texp :=
  (xty, OP_GetElementPtr xty
                   (xptrty, EXP_Ident (ID_Local (Name name)))
                   ([mkI32 idx])).
Definition mkXGEP := mkGEPI32.

(* INSTR_Store (volatile:bool) (val:texp) (ptr:texp) (align:option int) *)
Definition storeXAt0: instr_id * instr :=
  (IVoid 0%Z, INSTR_Store false (mkI32 1) (mkXGEP "x" 0) None).

Definition storeXAt1: instr_id * instr :=
  (IVoid 1%Z, INSTR_Store false (mkI32 2) (mkXGEP "x" 1) None).
*)

(*

        [(IId (Name "x"), INSTR_Alloca i32PTRTY (Some ((TYPE_I (32%Z)),  EXP_Integer 0)) None);
           (IVoid 0%Z, INSTR_Store  false (TYPE_I (32%Z), EXP_Integer val1) p1 None);
           (IVoid 1%Z, INSTR_Store  false (TYPE_I (32%Z), EXP_Integer val2) p2 None);
           (IId (Name "xat0"), INSTR_Load false i32ty p3 None)]
        ,
        TERM_Ret (i32TY, (EXP_Ident (ID_Local (Name "xat0"))))
      ) => None 
 *)


  (* (xty, OP_GetElementPtr xty
                   (xptrty, EXP_Ident (ID_Local (Name name)))
                   ([mkI32 idx])) *)

Definition isGEPAtIx (e: texp) (ix: Z)  : bool :=
  match e with
  | ((TYPE_Array 2 i32TY),
     OP_GetElementPtr (TYPE_Array 2 (TYPE_I 32%Z))
                      (TYPE_Pointer (TYPE_Array 2 (TYPE_I 32%Z)),
                       EXP_Ident (ID_Local (Name "x")))
                      [(i32TY, EXP_Integer gepix)]) => if gepix =? ix
                                                      then true
                                                      else false
  | (_, _) => false
     end.
                                                           

                                 
                                             
Open Scope bool_scope.
                                             
Definition rewrite_main_bb (bb: block): option block := 
  match blk_phis bb with
  | [] => 
    match (blk_code bb, blk_term bb) with
    |  ([(IId (Name "x"), INSTR_Alloca i32PTRTY (Some ((TYPE_I (32%Z)),  EXP_Integer 0)) None) as i1;
           (IVoid 0%Z, INSTR_Store  false (TYPE_I (32%Z), EXP_Integer 0) p1 None) as i2;
           (IVoid 1%Z, INSTR_Store  false (TYPE_I (32%Z), EXP_Integer 1) p2 None) as i3;
           (IId (Name "xat0"), INSTR_Load false (TYPE_I (32%Z)) p3 None) as i4] ,
        (IVoid 2%Z, TERM_Ret (i32TY, (EXP_Ident (ID_Local (Name "xat0"))))) as iret) =>
       if isGEPAtIx p1 0 && isGEPAtIx p2 1 && isGEPAtIx p3 0
       then 
         Some (mk_block (blk_id bb)
                  (blk_phis bb)
                  ([i1; i3; i2; i4])
                   iret)
       else None
    | (_,_) => None
    end
      
  | _ => None
  end.

Close Scope bool_scope.
                                                      


Definition rewrite_main_cfg (c: cfg) : cfg :=
  {| init := init c;
     blks := match blks c with
             | [blk] => match rewrite_main_bb blk with
                       | Some blk' => [blk']
                       | None => [blk]
                       end
             | _ => blks c
             end;
     args := args c;
|}.

Definition rewrite_main_definition (d: definition cfg): definition cfg :=
  if dc_name (df_prototype d) == (Name "main")
  then
    mk_definition cfg
                  (df_prototype d) 
                  (df_args d)
                  (rewrite_main_cfg (df_instrs d))
  else d.
         

  
Definition rewrite_mcfg (MCFG:mcfg) : mcfg :=
  {| m_name := m_name MCFG;
     m_target:= m_target MCFG;
     m_datalayout := m_datalayout MCFG;
     m_type_defs := m_type_defs MCFG;
     m_globals := m_globals MCFG;
     m_declarations := m_declarations MCFG;
     m_definitions := match (m_globals MCFG , m_declarations MCFG, m_definitions MCFG) with
                      | ([], [], [defn]) => [rewrite_main_definition defn]
                      | (_, _, _) => m_definitions MCFG
                      end
  |}.
  
