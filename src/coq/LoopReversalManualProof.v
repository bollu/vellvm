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
Require Import Vellvm.AstLib Vellvm.LLVMAst.
Require Import Vellvm.Classes.
Require Import Vellvm.Util.
Require Import Vellvm.CFG.
Require Import Vellvm.LLVMIO.
Require Import Vellvm.DynamicValues.
Require Import Vellvm.StepSemantics.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.TypeUtil.
Require Import Vellvm.Memory.
Require Import Vellvm.Trace.
Require Import Setoid Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import SetoidClass.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Vellvm.StoreSwitch.
Require Import Vellvm.TopLevel.
Require FunctionalExtensionality.
Require Import Eqdep_dec.
Require Import Classical.
Require Import Vellvm.Trace.
Require Import FSets.FMapAVL.
Require Import Integers.
Require Coq.Structures.OrderedTypeEx.
Require Import ZMicromega.
Import IO.DV.
Import Trace.MonadVerif.
Require Nsatz.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

Require Import Vellvm.Memory.

Section LOOPREV.

  Variable ORIGTRIPCOUNT: nat.
  Definition TRIPCOUNT: Z := Z.of_nat ORIGTRIPCOUNT.
  
  (* 
Notation TRIPCOUNT := 100%Z.
*)

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


Definition exp_eq (v1: exp) (v2: exp): exp :=
  OP_ICmp Eq (i32TY) v1 v2.

Definition exp_increment_ident (name: string): exp :=
  exp_add (exp_ident "name") (exp_const_z 1).

Definition simpleProgramInitBBId : block_id := Name "init".
Definition bbInit: block := 
    {|
      blk_id := simpleProgramInitBBId;
      blk_phis  := [];
      blk_code  := [alloca_array "arr" TRIPCOUNT];
      blk_term := (IVoid 0%Z, break "loop");
    |}.


Definition bbInitRewrite: block := 
    {|
      blk_id := simpleProgramInitBBId;
      blk_phis  := [];
      blk_code  := [alloca_array "arr" TRIPCOUNT];
      blk_term := (IVoid (TRIPCOUNT - 1), break "loop");
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
                   (IId (Name "cond"), INSTR_Op (exp_eq (exp_ident "iv.next")
                                                       (exp_const_z TRIPCOUNT)
                ))];
                
    blk_term := (IVoid 101%Z, branch (texp_ident "cond") "exit" "loop")
  |}.


Definition bbLoopRewrite :=
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
                   (IId (Name "cond"), INSTR_Op (exp_eq (exp_ident "iv.next")
                                                       (exp_const_z (-1))
                ))];
                
    blk_term := (IVoid 101%Z, branch (texp_ident "cond") "exit" "loop")
  |}.


                       
Definition bbExit : block :=
  {| blk_id := Name "exit";
     blk_phis := [];
     blk_code := [];
     blk_term := (IVoid 10%Z, TERM_Ret (texp_ident "val"));
  |}.


Definition mainCFG : cfg := 
{|
  init := simpleProgramInitBBId;
  blks := [bbInit; bbLoop; bbExit];
  args := [];
  |}.


Definition mainCFGRewrite : cfg := 
{|
  init := simpleProgramInitBBId;
  blks := [bbInitRewrite; bbLoopRewrite; bbExit];
  args := [];
  |}.


Definition mainproto : declaration :=
  {|
    dc_name        := Name "main";
    dc_type        :=  TYPE_Function TYPE_Void [TYPE_I 32];
    dc_param_attrs := ([], []);
    dc_linkage     := None;
    dc_visibility  := None;
    dc_dll_storage := None;
    dc_cconv       := None;
    dc_attrs       := [];
    dc_section     := None;
    dc_align       := None;
    dc_gc          := None;

  |}.
Definition mainDefinition: definition cfg :=
  {|
    df_prototype   := mainproto;
    df_args        := [];
    df_instrs      := mainCFG
  |}.


Definition mainDefinition': definition cfg :=
  {|
    df_prototype   := mainproto;
    df_args        := [];
    df_instrs      := mainCFGRewrite
  |}.


Definition program: mcfg :=
  {|
    m_name := None;
    m_target := None;
    m_datalayout := None;
    m_type_defs := [];
    m_globals := [];
    m_declarations := [];
    m_definitions:= [mainDefinition]
  |}.

Definition program': mcfg :=
  {|
    m_name := None;
    m_target := None;
    m_datalayout := None;
    m_type_defs := [];
    m_globals := [];
    m_declarations := [];
    m_definitions:= [mainDefinition']
  |}.
End LOOPREV.

Definition LoopWriteSet (n: nat) : list nat := seq 1 n.

Lemma prog_prog'_equal: forall n, program n = program' n.
Proof.
  intros.
  unfold program.
  unfold program'.
  apply f_equal.
  unfold mainDefinition.
  unfold mainDefinition'.
  simpl.
  cut (mainCFG n = mainCFGRewrite n); intros; try (rewrite H; auto).
  unfold mainCFG.
  unfold mainCFGRewrite.
Abort.


Hint Transparent SS.init_state.
Hint Unfold SS.init_state.

(* Lemma I care about *)
Theorem looprev_same_semantics:
  forall (n: nat),
    run_mcfg_with_memory (program n) ≡ run_mcfg_with_memory (program' n).
Proof.
  intros.
  unfold program.
  unfold program'.
  
  unfold run_mcfg_with_memory.
  simpl.
  unfold SS.init_state.
  simpl.
  unfold SS.build_global_environment.
  simpl.
  unfold SS.allocate_globals.
  simpl.

  euttnorm.
  unfold SS.register_functions.
  simpl.
  euttnorm.
  unfold SS.register_declaration.
  euttnorm.
  Set Ltac debug.
  forcetrace.
  euttnorm.
  unfold SS.initialize_globals.

    repeat (  euttnorm ||
        M.forcememd ||
        SS.forcestepsem ||
        unfold SS.cont;simpl).

  unfold run_mcfg_with_memory.
  simpl.
  unfold SS.init_state.
  unfold SS.build_global_environment.
  unfold SS.allocate_globals.
  simpl.
  repeat progress euttnorm.
  unfold SS.register_functions.
  simpl.
  repeat progress euttnorm.
  unfold SS.register_declaration.
  repeat progress (euttnorm).
  repeat progress M.forcememd.
  euttnorm.

  unfold SS.initialize_globals.
  simpl.
  rewrite bindM_Ret.
  rewrite bindM_Ret.
  euttnorm.
Qed.