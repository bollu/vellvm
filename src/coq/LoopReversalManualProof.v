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
Require Import Vellvm.StepSemanticsTiered.
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
Require Import Vellvm.TopLevel.
Require FunctionalExtensionality.
Require Import Eqdep_dec.
Require Import Classical.
Require Import Vellvm.Trace.
Require Import FSets.FMapAVL.
Require Import Integers.
Require Coq.Structures.OrderedTypeEx.
Require Import ZMicromega.
Require Import Bool.
Import IO.DV.
Import Trace.MonadVerif.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.

(** SSReflect **)

From Coq Require Import ssreflect ssrfun ssrbool.
Set Implicit Arguments.
Unset Strict Implicit.
Import ssreflect.SsrSyntax.
Set Printing Implicit Defensive.


Require Import Vellvm.Memory.

Opaque M.add_all_index.
Opaque M.add.
Opaque M.serialize_dvalue.
Opaque M.lookup_all_index.
Opaque M.make_empty_block.

Section LOOPREV.

  Variable ORIGTRIPCOUNT: nat.
  Definition TRIPCOUNT: Z := Z.of_nat ORIGTRIPCOUNT.
  

Notation i32TY := (TYPE_I (32%Z)).
Definition i32ARRTY := (TYPE_Array 2 i32TY).
Definition i32ARRPTRTY := (TYPE_Pointer (TYPE_Array 2 i32TY)).
Definition i32PTRTY := (TYPE_Pointer i32TY).
Definition mkI32 (i: Z): texp := (i32TY, EXP_Integer i).





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
  exp_add (exp_ident name) (exp_const_z 1).

Definition bbMain: block := 
    {|
      blk_id := Name "main";
      blk_phis  := [];
      blk_code  := [alloca_array "arr" TRIPCOUNT];
      blk_term := (IVoid 0%Z, break "loop");
    |}.


Definition bbInitRewrite: block := 
    {|
      blk_id := Name "Main";
      blk_phis  := [];
      blk_code  := [alloca_array "arr" TRIPCOUNT];
      blk_term := (IVoid (TRIPCOUNT - 1), break "loop");
    |}.

Definition bbLoop :=
  {|
    blk_id := Name "loop";
    blk_phis := [(Name "iv",
                  Phi i32TY [
                        (Name "main", exp_const_z 0);
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
                        (Name "main", exp_const_z 0);
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
     blk_term := (IVoid 10%Z, TERM_Ret (texp_const_z 0))
  |}.


Definition mainCFG : cfg := 
{|
  init := Name "main";
  blks := [bbMain; bbLoop; bbExit];
  args := [];
  |}.


Definition mainCFGRewrite : cfg := 
{|
  init := Name "main";
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


Hint Transparent SS.init_state.
Hint Unfold SS.init_state.

Create HintDb evaluation.
Hint Resolve SST.lookup_env_hd: evaluation.
Hint Resolve SST.lookup_env_tl: evaluation.


Hint Rewrite @SST.lookup_env_hd: evaluation.
Hint Rewrite @SST.lookup_env_tl: evaluation.


(** *Expresssion effects *)
Lemma eval_exp_ident: forall
    (tds: typedefs)
    (ot: option dtyp)
    (ge: SST.genv)
    (e: SST.env)
    (name: string)
    (val: dvalue),
    SST.eval_exp tds ge (SST.add_env (Name name) val e) ot (exp_ident name) ≡
                 Ret val.
Proof.
  intros.
  unfold SST.eval_exp.
  simpl.
  rewrite SST.lookup_env_hd.
  simpl.
  reflexivity.
Qed.

Hint Resolve eval_exp_ident: evaluation.
Hint Rewrite @eval_exp_ident: evaluation.


Lemma eval_exp_ident': forall
    (tds: typedefs)
    (ot: option dtyp)
    (ge: SST.genv)
    (e: SST.env)
    (name: string)
    (val: dvalue)
    (EATIDENT: (SST.lookup_env e (Name name)) = mret val),
    SST.eval_exp tds ge e ot (exp_ident name) ≡
                 Ret val.
Proof.
  intros.
  unfold SST.eval_exp.
  simpl.
  rewrite EATIDENT.
  simpl.
  reflexivity.
Qed.


Hint Resolve eval_exp_ident': evaluation.
Hint Rewrite @eval_exp_ident': evaluation.

Lemma eval_exp_gep:
  forall (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (arrval ivval: dvalue)
    (LOOKUPARR: SST.lookup_env e (Name "arr") = mret arrval)
    (LOOKUPIV: SST.lookup_env e (Name "iv") = mret ivval)
    (n:nat),
    SST.eval_exp tds ge e
                 (Some (SST.eval_typ tds (arr_ty n)))
             (OP_GetElementPtr (arr_ty n) (TYPE_Pointer (arr_ty n), exp_ident "arr")
                               [texp_ident "iv"]) ≡
              Vis (IO.GEP (DTYPE_Array (Z.of_nat n) (DTYPE_I 32)) arrval [ivval])
              (fun x : dvalue => Ret x).
Proof.
  intros.
  simpl.
  rewrite LOOKUPARR.
  euttnorm.
  rewrite LOOKUPIV.
  euttnorm.
  unfold arr_ty, SST.eval_typ.
  simpl.
  repeat rewrite normalize_type_equation.
  unfold TRIPCOUNT.
  auto.
Qed.


Hint Resolve eval_exp_ident': evaluation.
Hint Rewrite @eval_exp_ident': evaluation.

Lemma eval_exp_const:  forall
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
  (z: Z),
    SST.eval_exp tds ge e (Some (DTYPE_I 32)) (exp_const_z z)  ≡
                 Ret (DVALUE_I32 (Int32.repr z)).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Hint Resolve eval_exp_const: evaluation.
Hint Rewrite @eval_exp_const: evaluation.

Lemma eval_exp_increment_ident:
  forall (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (ivval: dvalue)
    (name: string)
    (LOOKUPIV: SST.lookup_env e (Name name) = mret ivval),
  SST.eval_exp tds ge e None
               (exp_increment_ident name) ≡
               IO.lift_err_d (eval_iop (Add false false) ivval (DVALUE_I32 (Int32.repr 1)))
    [eta Ret (X:=dvalue)] .
Proof.
  intros.
  simpl.
  rewrite LOOKUPIV.
  euttnorm.
  unfold SST.eval_typ; rewrite normalize_type_equation.
  euttnorm.
Qed.



Hint Resolve eval_exp_increment_ident: evaluation.
Hint Rewrite @eval_exp_increment_ident: evaluation.

Lemma eval_exp_eq_when_neq:
  forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (val: int32)
    (name: string)
    (NEQ: Int32.eq val (Int32.repr (TRIPCOUNT n)) = false)
    (LOOKUPIV: SST.lookup_env e (Name name) = mret (DVALUE_I32 val)),
    SST.eval_exp tds ge e None
                 (exp_eq (exp_ident name) (exp_const_z (TRIPCOUNT n))) ≡
                 Ret (DVALUE_I1 Int1.zero).
Proof.
  intros.
  simpl.
  rewrite LOOKUPIV.
  euttnorm.
  unfold SST.eval_typ; rewrite normalize_type_equation.
  euttnorm.
  unfold eval_icmp.
  simpl.
  unfold eval_i32_icmp.
  simpl.
  unfold TRIPCOUNT.
  rewrite NEQ.
  euttnorm.
Qed.

Hint Resolve eval_exp_eq_when_neq: evaluation.
Hint Rewrite @eval_exp_eq_when_neq: evaluation.

Lemma eval_exp_eq_when_eq:
  forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (val: int32)
    (name: string)
    (EQ: Int32.eq val (Int32.repr (TRIPCOUNT n)) = true)
    (LOOKUPIV: SST.lookup_env e (Name name) = mret (DVALUE_I32 val)),
    SST.eval_exp tds ge e None
                 (exp_eq (exp_ident name) (exp_const_z (TRIPCOUNT n))) ≡
                 Ret (DVALUE_I1 Int1.one).
Proof.
  intros.
  simpl.
  rewrite LOOKUPIV.
  euttnorm.
  unfold SST.eval_typ; rewrite normalize_type_equation.
  euttnorm.
  unfold eval_icmp.
  simpl.
  unfold eval_i32_icmp.
  simpl.
  unfold TRIPCOUNT.
  rewrite EQ.
  euttnorm.
Qed.

Hint Resolve eval_exp_eq_when_eq: evaluation.
Hint Rewrite @eval_exp_eq_when_eq: evaluation.

Lemma eval_exp_eq:
  forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (val: int32)
    (name: string)
    (LOOKUPIV: SST.lookup_env e (Name name) = mret (DVALUE_I32 val)),
    SST.eval_exp tds ge e None
                 (exp_eq (exp_ident name) (exp_const_z (TRIPCOUNT n))) ≡
                 Ret
    (if Int32.eq val (Int32.repr (Z.of_nat n))
     then DVALUE_I1 Int1.one
     else DVALUE_I1 Int1.zero).
Proof.
  intros.
  simpl.
  unfold SST.eval_typ; rewrite normalize_type_equation.
  rewrite LOOKUPIV.
  euttnorm.
Qed.


Hint Resolve eval_exp_eq: evaluation.
Hint Rewrite @eval_exp_eq: evaluation.
Opaque SST.eval_exp.



(** *Instruction effects *)

(** Effect of alloca *)
Lemma exec_inst_alloca:  forall 
             (tds: typedefs)
             (ge:  SST.genv)
             (e: SST.env)
             (id: instr_id)
             (name: string)
             (nbytes: Z)
             (i: instr)
             (mem: M.memory)
             (ID: id = fst (alloca_array name nbytes))
             (INST: i = snd (alloca_array name nbytes)),
    M.memEffect mem (SST.execInst tds ge e id i) ≡
                 (Ret
       (M.add (M.size mem) (M.make_empty_block (SST.eval_typ tds i32PTRTY)) mem,
       SST.IREnvEffect (SST.add_env (Name name) (DVALUE_Addr (M.size mem, 0)) e))).
Proof.
  intros.
  subst.
  simpl.
  M.forcemem.
  simpl.
  M.forcemem.
  euttnorm.
Qed.


Hint Resolve exec_inst_alloca: evaluation.
Hint Rewrite @exec_inst_alloca: evaluation.
(** Effect of store *)
Lemma exec_inst_store: forall
             (tds: typedefs)
             (ge:  SST.genv)
             (e: SST.env)
             (id: instr_id)
             (mem: M.memory)
             (valt ixt: typ)
             (vale ixe: exp)
             (IDVAL: exists (i: LLVMAst.int), id = IVoid i),
    M.memEffect
      mem
      (SST.execInst tds
                    ge
                    e
                    id
                    (inst_store
                       (valt, vale)
                       
                       (ixt, ixe))) ≡
      M.memEffect mem
      (bindM
         (SST.eval_exp tds ge e
                       (Some (SST.eval_typ tds valt))
                       vale)
         (fun dv : dvalue =>
            bindM (SST.eval_exp tds ge e (Some (SST.eval_typ tds ixt)) ixe)
                  (fun v : dvalue => Vis (IO.Store v dv) (fun _ : () => Ret SST.IRNone)))).
Proof.
  intros.
  unfold inst_store.
  unfold SST.execInst.
  destruct IDVAL as [idval IDVAL].
  subst.
  unfold SST.execInst.
  simpl.
  unfold SST.execInst.
  euttnorm.
Qed.


Hint Resolve exec_inst_store: evaluation.
Hint Rewrite @exec_inst_store: evaluation.

(** ***Evaluate INSTR_OP *)
Lemma exec_inst_op: forall
             (tds: typedefs)
             (ge:  SST.genv)
             (e: SST.env)
             (vale: exp)
             (dvale: dvalue)
             (name: string)
             (VALE_VALUE: SST.eval_op tds ge e vale ≡ Ret dvale) ,
    SST.execInst tds ge e (IId (Name name)) (INSTR_Op vale) ≡
                 Ret (SST.IREnvEffect (SST.add_env (Name name) dvale e)).
Proof.
  intros.
  simpl.
  rewrite VALE_VALUE.
  euttnorm.
Qed.
  

Hint Resolve exec_inst_op: evaluation.
Hint Rewrite @exec_inst_op: evaluation.
Opaque SST.execInst.

(** *Basic block effects *)
Lemma exec_bbMain: forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (mem: M.memory),
    M.memEffect mem (SST.execBB tds ge e None (bbMain n)) ≡
                 Ret (M.add (M.size mem) (M.make_empty_block DTYPE_Pointer) mem,
                      SST.BBRBreak (SST.add_env (Name "arr") (DVALUE_Addr (M.size mem, 0)) e) (Name "loop")).
Proof.
  intros.
  unfold SST.execBB.
  unfold SST.evalPhis.
  unfold bbMain.
  
  simpl.
  euttnorm.
  M.forcemem.
  simpl.
  euttnorm.

  simpl.
  rewrite M.memEffect_commutes_with_bind.
  rewrite exec_inst_alloca; eauto.
  unfold i32PTRTY.
  euttnorm.
  euttnorm.
  M.forcemem.
  unfold SST.eval_typ.
  rewrite normalize_type_equation.
  auto.
Qed.
             

Lemma exec_bbInitRewrite: forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (mem: M.memory), 
      M.memEffect mem (SST.execBB tds ge e None (bbInitRewrite n)) ≡
                  (Ret
            (M.add (M.size mem) (M.make_empty_block DTYPE_Pointer) mem,
            SST.BBRBreak (SST.add_env (Name "arr") (DVALUE_Addr (M.size mem, 0)) e)
              (Name "loop"))).
Proof.
  intros.
  simpl.
  unfold bbInitRewrite.
  unfold SST.execBB.
  unfold SST.evalPhis.
  simpl.
  euttnorm.
  M.forcemem.
  simpl.
  euttnorm.
  unfold SST.BBResultFromTermResult.
  rewrite M.memEffect_commutes_with_bind.
  rewrite exec_inst_alloca; eauto.
  euttnorm.
  unfold SST.eval_typ.
  rewrite normalize_type_equation.
  unfold i32PTRTY.
  euttnorm.
  M.forcemem.
  euttnorm.
Qed.

(** Equivalence of init BBs *)
Lemma exec_bbMain_exec_bbInitRewrite_equiv:
   forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (mem: M.memory), 
     M.memEffect mem (SST.execBB tds ge e None (bbInitRewrite n)) ≡
                 M.memEffect mem (SST.execBB tds ge e None (bbMain n)).
Proof.
  intros.
  rewrite exec_bbMain.
  rewrite exec_bbInitRewrite.
  reflexivity.
Qed.

(** Since we can factor `memEffect`, we can reason separately about phi
    node evaluation *)
Lemma exec_bbLoop_phis_from_init:
  forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (mem: M.memory),
    M.memEffect mem (SST.evalPhis tds ge e (Some (Name "main"))
                                    (blk_phis (bbLoop n))) ≡ (Ret (mem, SST.add_env (Name "iv") (DVALUE_I32 (Int32.repr 0)) e)).
Proof.
  intros.
  unfold SST.evalPhis.
  unfold bbLoop. simpl.
  euttnorm.
  unfold SST.evalPhi.
  simpl.
  unfold SST.eval_typ.
  rewrite normalize_type_equation.
  simpl.
  euttnorm.
  M.forcemem.
  rewrite eval_exp_const.
  euttnorm.
  M.forcemem.
  auto.
Qed.


Lemma exec_bbLoop_from_init:
  forall (n: nat)
    (N_GT_1: (n >= 1)%nat)
    (N_IN_RANGE: Z.of_nat n <= Int32.max_unsigned)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (mem initmem: M.memory)
    (arrblockidx: Z)
    (EATARR: (SST.lookup_env e (Name "arr")) = mret (DVALUE_Addr (arrblockidx, 0)))
    (MEMATARR: mem = (M.add arrblockidx (M.make_empty_block DTYPE_Pointer) initmem)),
  
    M.memEffect mem (SST.execBB tds ge e (Some (Name "main")) (bbLoop n)) ≡

  M.memEffect
    (M.add arrblockidx
       (M.add_all_index (M.serialize_dvalue (DVALUE_I32 (Int32.repr 0)))
          (Int32.unsigned (Int32.repr 0) * 8) (M.make_empty_block DTYPE_Pointer))
       (M.add arrblockidx (M.make_empty_block DTYPE_Pointer) initmem))
    (mapM
       (SST.BBResultFromTermResult
          (SST.add_env (Name "cond")
             (if
               Int32.eq (Int32.add (Int32.repr 0) (Int32.repr 1))
                 (Int32.repr (Z.of_nat n))
              then DVALUE_I1 Int1.one
              else DVALUE_I1 Int1.zero)
             (SST.add_env (Name "iv.next")
                (DVALUE_I32 (Int32.add (Int32.repr 0) (Int32.repr 1)))
                (SST.add_env (Name "iv") (DVALUE_I32 (Int32.repr 0)) e))))
       (bindM
          match
            (if
              Int32.eq (Int32.add (Int32.repr 0) (Int32.repr 1))
                (Int32.repr (Z.of_nat n))
             then DVALUE_I1 Int1.one
             else DVALUE_I1 Int1.zero)
          with
          | DVALUE_Addr _ => Err "Br got non-bool value"
          | DVALUE_I1 comparison_bit =>
              if Int1.eq comparison_bit Int1.one
              then Ret (Name "exit")
              else Ret (Name "loop")
          | DVALUE_I32 _ => Err "Br got non-bool value"
          | DVALUE_I64 _ => Err "Br got non-bool value"
          | DVALUE_Double _ => Err "Br got non-bool value"
          | DVALUE_Float _ => Err "Br got non-bool value"
          | DVALUE_Undef => Err "Br got non-bool value"
          | DVALUE_Poison => Err "Br got non-bool value"
          | DVALUE_None => Err "Br got non-bool value"
          | DVALUE_Struct _ => Err "Br got non-bool value"
          | DVALUE_Packed_struct _ => Err "Br got non-bool value"
          | DVALUE_Array _ => Err "Br got non-bool value"
          | DVALUE_Vector _ => Err "Br got non-bool value"
          end (fun br : block_id => Ret (SST.TRBreak br)))).
Proof.
  Opaque SST.execBBInstrs.
  Opaque SST.execInst.
  Opaque SST.eval_exp.
  intros.
  simpl.
  
  unfold SST.execBB.
  unfold SST.evalPhis.
  rewrite M.memEffect_commutes_with_bind.

  setoid_rewrite exec_bbLoop_phis_from_init; auto.
  rewrite bindM_Ret.
  rewrite SST.force_exec_bb_instrs.
  simpl.


  rewrite M.memEffect_commutes_with_bind.
  setoid_rewrite exec_inst_store; eauto.
  simpl.
  rewrite eval_exp_ident; eauto.
  euttnorm.
  M.forcemem.
  rewrite eval_exp_gep.
  (** I shouldn't have to do this :( *)
  all: cycle -2.
  rewrite SST.lookup_env_tl; auto.
  rewrite EATARR.
  eauto.
  rewrite SST.lookup_env_hd; auto.
  euttnorm.
  M.forcemem.
  
  (** MEM is OK here **)
  simpl.
  rewrite MEMATARR.
  rewrite M.lookup_add; auto.
  euttnorm.
  M.forcemem.
  simpl.
  rewrite M.lookup_add; auto.
  euttnorm.
  (** MEM is too large here **)
  M.forcemem.

  assert (N_NOT_LEQ_0: Z.of_nat n <=? Int32.unsigned (Int32.repr 0) = false).
  (** since n >= 1, n is not <= 0 **)
  rewrite Int32.unsigned_repr; cycle 1.
  compute; split; intros; congruence.
  destruct (Z.of_nat n <=? 0) eqn:DESTRUCT; auto.
  rewrite <- Zle_is_le_bool in DESTRUCT.
  omega.

  rewrite N_NOT_LEQ_0.
  simpl.
  euttnorm.
  (** MEM is too large here **)
  simpl.
  (* TODO: fix the opening of add_all_index *)
  (* evaluate iv.next *)
  rewrite SST.force_exec_bb_instrs.
  rewrite exec_inst_op; cycle 1.
  unfold SST.eval_op.
  simpl.
  rewrite eval_exp_increment_ident.
  all: cycle 1.
  rewrite SST.lookup_env_hd.
  eauto.
  all: cycle 1.
  simpl.
  eauto.
  euttnorm.


  
  (* eval checking of iv.next *)
  rewrite SST.force_exec_bb_instrs.
  rewrite exec_inst_op.
  all: cycle 1.
  unfold SST.eval_op.
  simpl.
  rewrite eval_exp_eq; eauto.
  rewrite SST.lookup_env_hd; auto.

  euttnorm.
  M.forcemem.
  (* done with loop *)
  (* eval branch *)
  rewrite SST.force_exec_bb_instrs.
  euttnorm.
  (** Missing eutt proper instance for mapM **)
  rewrite eval_exp_ident.
  repeat progress euttnorm.
Qed.



Lemma exec_bbLoop_phis_from_loop:
  forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (ivnextval: dvalue)
    (EATIVNEXT: SST.lookup_env e (Name "iv.next") = mret ivnextval)
    (mem: M.memory),
    M.memEffect mem (SST.evalPhis tds ge e (Some (blk_id (bbLoop n))) (blk_phis (bbLoop n))) ≡ 
  Ret (mem, SST.add_env (Name "iv") ivnextval e).
Proof.
  intros.
  unfold SST.evalPhis.
  unfold bbLoop. simpl.
  euttnorm.
  unfold SST.evalPhi.
  simpl.
  unfold SST.eval_typ.
  rewrite normalize_type_equation.
  simpl.
  
  rewrite M.memEffect_commutes_with_bind.
  rewrite eval_exp_ident'; eauto.
  M.forcemem.
  euttnorm.
  M.forcemem.
  auto.
Qed.




(** The spine of the computation when evaluating from the backedge,
with the conditionals left in. This can be refined based on things that are
known about the program *)
Lemma exec_bbLoop_from_bbLoop_spine: forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (ivnextval: int32)
    (initmem mem: M.memory)
    (arrblockidx: Z)
    (arrblock: M.mem_block)
    (EATARR: (SST.lookup_env e (Name "arr")) = mret (DVALUE_Addr (arrblockidx, 0)))
    (MEMATARR: mem = (M.add arrblockidx arrblock initmem))
    (EATIVNEXT: SST.lookup_env e (Name "iv.next") = mret (DVALUE_I32 ivnextval)),
      M.memEffect mem (SST.execBB tds ge e
                                  (Some (blk_id (bbLoop n)))
                                  (bbLoop n)) ≡
  M.memEffect
    (M.add arrblockidx
       (M.add_all_index (M.serialize_dvalue (DVALUE_I32 ivnextval))
          match
            (if Z.of_nat n <=? Int32.unsigned ivnextval
             then None
             else Some (DTYPE_I 32, Int32.unsigned ivnextval * 8))
          with
          | Some (_, offset) => offset
          | None => 0
          end arrblock) (M.add arrblockidx arrblock initmem))
    (mapM
       (SST.BBResultFromTermResult
          (SST.add_env (Name "cond")
             (if
               Int32.eq (Int32.add ivnextval (Int32.repr 1))
                 (Int32.repr (Z.of_nat n))
              then DVALUE_I1 Int1.one
              else DVALUE_I1 Int1.zero)
             (SST.add_env (Name "iv.next")
                (DVALUE_I32 (Int32.add ivnextval (Int32.repr 1)))
                (SST.add_env (Name "iv") (DVALUE_I32 ivnextval) e))))
       (bindM
          match
            (if
              Int32.eq (Int32.add ivnextval (Int32.repr 1))
                (Int32.repr (Z.of_nat n))
             then DVALUE_I1 Int1.one
             else DVALUE_I1 Int1.zero)
          with
          | DVALUE_Addr _ => Err "Br got non-bool value"
          | DVALUE_I1 comparison_bit =>
              if Int1.eq comparison_bit Int1.one
              then Ret (Name "exit")
              else Ret (Name "loop")
          | DVALUE_I32 _ => Err "Br got non-bool value"
          | DVALUE_I64 _ => Err "Br got non-bool value"
          | DVALUE_Double _ => Err "Br got non-bool value"
          | DVALUE_Float _ => Err "Br got non-bool value"
          | DVALUE_Undef => Err "Br got non-bool value"
          | DVALUE_Poison => Err "Br got non-bool value"
          | DVALUE_None => Err "Br got non-bool value"
          | DVALUE_Struct _ => Err "Br got non-bool value"
          | DVALUE_Packed_struct _ => Err "Br got non-bool value"
          | DVALUE_Array _ => Err "Br got non-bool value"
          | DVALUE_Vector _ => Err "Br got non-bool value"
          end (fun br : block_id => Ret (SST.TRBreak br)))).
Proof.
  Opaque SST.execBBInstrs.
  Opaque SST.execInst.
  Opaque SST.eval_exp.
  Opaque M.lookup.

  intros.
  unfold SST.execBB.
  rewrite M.memEffect_commutes_with_bind.

  setoid_rewrite exec_bbLoop_phis_from_loop; eauto.
  euttnorm.

  (* Now we ave evaluted PHI nodes, time to evaluate instructions *)
  (** Compute store **)
  rewrite SST.force_exec_bb_instrs.
  rewrite M.memEffect_commutes_with_bind.
  rewrite exec_inst_store; eauto.
  rewrite eval_exp_ident.
  euttnorm.
  rewrite eval_exp_gep; try (eauto 2 with evaluation).
  all: cycle -1.
  (* Why did eauto not find this? *)
  rewrite SST.lookup_env_tl; eauto.
  euttnorm.
  M.forcemem.
  simpl.
  rewrite MEMATARR.
  rewrite M.lookup_add.
  simpl.
  euttnorm.
  M.forcemem.

  simpl.
  rewrite M.lookup_add.
  euttnorm.
  M.forcemem.
  euttnorm.

  
  
  (** Compute iv.next **)
  rewrite SST.force_exec_bb_instrs.
  rewrite M.memEffect_commutes_with_bind.
  rewrite exec_inst_op; cycle -1.
  unfold SST.eval_op.
  rewrite eval_exp_increment_ident; simpl; eauto with evaluation; simpl; eauto.

  euttnorm.
  M.forcemem.
  euttnorm.

  (** evaluate condition **)
  rewrite SST.force_exec_bb_instrs.
  rewrite M.memEffect_commutes_with_bind.
  rewrite exec_inst_op; cycle -1.
  unfold SST.eval_op.
  rewrite eval_exp_eq.
  eauto.
  rewrite SST.lookup_env_hd; eauto.
  euttnorm.
  M.forcemem.
  euttnorm.
  
  rewrite SST.force_exec_bb_instrs.
  simpl.
  rewrite eval_exp_ident.
  euttnorm.
Qed.


Lemma exec_bbLoop_from_bbLoop_inner_iterations:
  forall (n: nat)
    (NINRANGE: Z.of_nat n <= Int32.max_unsigned)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (ivnextval: int32)
    (IVNEXT_PLUS_1_LT_N: Int32.unsigned ivnextval + 1 < Z.of_nat n)
    (initmem mem: M.memory)
    (arrblockidx: Z)
    (arrblock: M.mem_block)
    (EATARR: (SST.lookup_env e (Name "arr")) = mret (DVALUE_Addr (arrblockidx, 0)))
    (MEMATARR: mem = (M.add arrblockidx arrblock initmem))
    (EATIVNEXT: SST.lookup_env e (Name "iv.next") = mret (DVALUE_I32 ivnextval)),
    M.memEffect mem (SST.execBB tds ge e
                                (Some (blk_id (bbLoop n)))
                                (bbLoop n)) ≡
                  Ret
    (M.add arrblockidx
       (M.add_all_index (M.serialize_dvalue (DVALUE_I32 ivnextval))
          (Int32.unsigned ivnextval * 8) arrblock)
       (M.add arrblockidx arrblock initmem),
    SST.BBRBreak
      (SST.add_env (Name "cond") (DVALUE_I1 Int1.zero)
         (SST.add_env (Name "iv.next")
            (DVALUE_I32 (Int32.add ivnextval (Int32.repr 1)))
            (SST.add_env (Name "iv") (DVALUE_I32 ivnextval) e))) 
      (Name "loop")) .
                
Proof.
  intros.
  rewrite exec_bbLoop_from_bbLoop_spine; eauto.
  
  assert (N_LEQ_IVNEXTVAL: reflect ((Z.of_nat n <= Int32.unsigned ivnextval))
                                   (Z.of_nat n <=? Int32.unsigned ivnextval)).
  apply Z.leb_spec0.
  destruct N_LEQ_IVNEXTVAL; try omega.


  assert (IVNEXTVAL_NEQ_N:Int32.eq
                            (Int32.add ivnextval (Int32.repr 1))
                            (Int32.repr (Z.of_nat n)) = false).
  unfold Int32.eq.
  repeat rewrite Int32.unsigned_repr.
  unfold Coqlib.zeq.
  destruct (Z.eq_dec (Int32.unsigned ivnextval + 1) (Z.of_nat n)); auto; try omega.
  compute; split; intros; congruence.
  admit.
  admit.
  split; omega.
  
  

  rewrite IVNEXTVAL_NEQ_N.
  simpl.
  euttnorm.
  M.forcemem.
  euttnorm.
Admitted.


Lemma exec_bbLoop_from_bbLoop_final_iteration:
  forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (ivnextval: int32)
    (IVNEXT_EQ_N: Int32.unsigned ivnextval + 1 = Z.of_nat n)
    (initmem mem: M.memory)
    (arrblockidx: Z)
    (EATARR: (SST.lookup_env e (Name "arr")) = mret (DVALUE_Addr (arrblockidx, 0)))
    (MEMATARR: mem = (M.add arrblockidx (M.make_empty_block DTYPE_Pointer) initmem))
    (EATIVNEXT: SST.lookup_env e (Name "iv.next") = mret (DVALUE_I32 ivnextval)),
    M.memEffect mem (SST.execBB tds ge e
                                (Some (blk_id (bbLoop n)))
                                (bbLoop n)) ≡
                 Ret
    (M.add arrblockidx
       (M.add_all_index (M.serialize_dvalue (DVALUE_I32 ivnextval))
          (Int32.unsigned ivnextval * 8) (M.make_empty_block DTYPE_Pointer))
       (M.add arrblockidx (M.make_empty_block DTYPE_Pointer) initmem),
    SST.BBRBreak
      (SST.add_env (Name "cond") (DVALUE_I1 Int1.one)
         (SST.add_env (Name "iv.next")
            (DVALUE_I32 (Int32.add ivnextval (Int32.repr 1)))
            (SST.add_env (Name "iv") (DVALUE_I32 ivnextval) e))) 
      (Name "exit")) .
Proof.
  intros.
  rewrite exec_bbLoop_from_bbLoop_spine; eauto.
  assert (N_LEQ_IVNEXTVAL: reflect ((Z.of_nat n <= Int32.unsigned ivnextval))
                                   (Z.of_nat n <=? Int32.unsigned ivnextval)).
  apply Z.leb_spec0.
  destruct N_LEQ_IVNEXTVAL; try omega.


  assert (IVNEXTVAL_NEQ_N: Int32.eq  (Int32.add ivnextval (Int32.repr 1))
                                     (Int32.repr (Z.of_nat n)) = true).
  rewrite <- IVNEXT_EQ_N.
  rewrite Int32.add_unsigned.
  rewrite Int32.unsigned_repr.
  apply Int32.eq_true.
  split; simpl; try omega.
  compute. intros; congruence.

  rewrite IVNEXTVAL_NEQ_N.
  simpl.
  euttnorm.
  M.forcemem.
  euttnorm.
Qed.


Lemma exec_exit:
  forall (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (prev: block_id)
    (mem: M.memory),
    M.memEffect mem (SST.execBB tds ge e (Some prev)
                                (bbExit)) ≡
                 M.memEffect mem (Ret (SST.BBRRet (DVALUE_I32 (Int32.repr 0)))).
Proof.
  intros.
  unfold SST.execBB.
  simpl.
  unfold SST.evalPhis.
  euttnorm.

  rewrite SST.force_exec_bb_instrs.
  simpl.
  unfold SST.eval_typ. rewrite normalize_type_equation.
  rewrite eval_exp_const.
  euttnorm.
Qed.


(** *Conditions for bbLoop (S n) = bbloop S n *)
Lemma exec_bbLoop_from_bbLoop_inner_iterations_decrement_tripcount:
  forall (n: nat)
    (NINRANGE: Z.of_nat (S n) <= Int32.max_unsigned)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (ivnextval: int32)
    (IVNEXT_PLUS_1_LT_N: Int32.unsigned ivnextval + 1 < Z.of_nat n)
    (initmem mem: M.memory)
    (arrblockidx: Z)
    (arrblock: M.mem_block)
    (EATARR: (SST.lookup_env e (Name "arr")) = mret (DVALUE_Addr (arrblockidx, 0)))
    (MEMATARR: mem = (M.add arrblockidx arrblock initmem))
    (EATIVNEXT: SST.lookup_env e (Name "iv.next") = mret (DVALUE_I32 ivnextval)),
    M.memEffect mem (SST.execBB tds ge e
                                (Some (blk_id (bbLoop n)))
                                (bbLoop ( S n))) ≡
    M.memEffect mem (SST.execBB tds ge e
                                (Some (blk_id (bbLoop n)))
                                (bbLoop n)).
Proof.
  intros.
  repeat rewrite exec_bbLoop_from_bbLoop_inner_iterations; eauto; zify; omega.
Qed.




(** TODO: create a function that shows what memory looks like on n iterations **)
Definition nat_to_int32 (n: nat): int32 :=
  Int32.repr (Z.of_nat n).

(** *Effect of memory by one iteration *)
Definition mem_effect_at_iteration (blockloc: Z) (i: nat) (mem: M.memory): M.memory :=
             (M.add blockloc
                    (M.add_all_index (M.serialize_dvalue (DVALUE_I32 (nat_to_int32 i)))
                                     (Int32.unsigned (nat_to_int32 i) * 8) (M.make_empty_block DTYPE_Pointer)) mem).
  


(** *Effect of memory by n iterations of the loop *)
Definition schedule := nat -> nat.
Definition VIV := nat.
Definition UB := nat.
Inductive exec_loop: Z -> schedule -> VIV -> UB -> M.memory -> M.memory -> Prop :=
| exec_loop_exit:  forall  (blockloc: Z) (s: schedule) (viv: nat) (ub: nat) (mem: M.memory),
    (viv >= ub)%nat -> exec_loop blockloc s viv ub mem mem
| exec_loop_loop : forall (blockloc: Z)
                     (s: schedule)
                     (viv: nat)
                     (ub: nat)
                     (mem1 mem2 mem3: M.memory)
                     (VIV_INRANGE: (viv < ub)%nat)
                     (ITER_EFFECT: mem_effect_at_iteration blockloc (s viv) mem1 = mem2),
    exec_loop blockloc s (viv + 1)%nat ub mem2 mem3 ->
    exec_loop blockloc s viv ub mem1 mem3.

Definition schedule_id (viv: nat): nat := viv.
Definition schedule_rev (MAXN: nat)(viv: nat): nat := MAXN - viv + 1.

Definition schedule_witness (s: schedule) : Prop := True.

Theorem all_bijective_schedules_in_range_are_equal:
  forall (s: schedule)
    (WITNESS: schedule_witness s)
    blockid viv ub mem1 mem2,
    exec_loop blockid schedule_id viv ub mem1 mem2 = 
    exec_loop blockid s viv ub mem1 mem2.
Proof.
Admitted.



(** *Relate execution of program of length (S n) to program of length n *)
(** Roughly, exec (p (S n)) === exec (P n ; loop)) *)
(** This will not work, so the correct thing to do is to do the compcert thing where we have a
    - exec n till_i = <inductive proposition like CompCert>
**)
Lemma program_sn_execution_as_program_n:
  forall (n: nat)
    (N_GE_1: (n >= 1)%nat)
    (e: SST.env)
    (ge: SST.genv)
    (mem initmem: M.memory)
    (bbprevid: block_id)
    (ivnextval: int)
    (arrblockidx: Z)
    (ENV_AT_ARR: SST.lookup_env e (Name "arr") = mret (DVALUE_Addr (arrblockidx, 0)))
    (INITMEM_ARR: mem = M.add arrblockidx (M.make_empty_block DTYPE_Pointer) initmem)
    (N_INRANGE: Z.of_nat n <= Int32.max_unsigned),
    mapM fst (M.memEffect
                mem
                (SST.execFunction [] ge e (mainCFG (S n)) (Name "main"))) ≡
         mapM (mem_effect_at_iteration arrblockidx (S n))
         (mapM fst (M.memEffect mem (SST.execFunction [] ge e (mainCFG n) (Name "main")))).
Proof.
Abort.
(** *Full effects *)

(** *For experimentation, see how to execute the main function *)
(* 
Lemma mem_effect_main_function_orig:
  forall (n: nat)
    (e: SST.env)
    (ge: SST.genv)
    (initmem: M.memory)
    (N_GE_1: (n >= 1)%nat)
    (N_INRANGE: Z.of_nat n <= Int32.max_unsigned),
               mapM fst (M.memEffect
                  initmem
                  (SST.execFunction
                     []
                     ge
                     e
                     (mainCFG n) (Name "main"))) ≡
                     Ret (create_mem_effect_of_loop 
                   (M.size initmem)
                   n
                   (M.add (M.size initmem) (M.make_empty_block DTYPE_Pointer) initmem)).
Proof.
  intros.
  unfold SST.execFunction.
  simpl.
  destruct n; try omega.

  induction n.

  +  rewrite SST.force_exec_function_at_bb_id; eauto.
     simpl.
     setoid_rewrite M.memEffect_commutes_with_bind.
     (* execute the initial BB *)
     setoid_rewrite exec_bbMain.
     euttnorm.

     
     rewrite SST.force_exec_function_at_bb_id; eauto.
     simpl.
     setoid_rewrite M.memEffect_commutes_with_bind.
     (* execute the loop bb *)
     simpl.
     rewrite exec_bbLoop_from_init; eauto.
     all: cycle 1.
     rewrite SST.lookup_env_hd.
     eauto.
     all: cycle 1.
     euttnorm.

     assert (O_PLUS_O_IS_ONE:  Int32.eq (Int32.add (Int32.repr 0) (Int32.repr 1)) (Int32.repr 1)).
     admit.
     repeat rewrite O_PLUS_O_IS_ONE.
     euttnorm.
     M.forcemem.
     euttnorm.

     

     
     rewrite SST.force_exec_function_at_bb_id; eauto.
     simpl.
     setoid_rewrite M.memEffect_commutes_with_bind.
     (* execute the initial BB *)
     rewrite exec_exit.
     M.forcemem.
     euttnorm.
     M.forcemem.
     euttnorm.

  + (** Induction hypothesis *)
Abort.



(** *Execute the loop in the main function *)
(*

    mapM fst (M.memEffect initmem (SST.execFunctionAtBBId []
                            (SST.ENV.add (Name "main") (DVALUE_Addr (M.size  M.empty, 0))
                                         (SST.ENV.empty dvalue))
                            (mainCFG n) (Name "main") (Some simpleProgramInitBBId) 
                            (Name "loop")))  ≡
                Ret (create_mem_effect_of_loop
                   (M.size initmem)
                   n
                   (M.add (M.size initmem) (M.make_empty_block DTYPE_Pointer) initmem)).
*)
Lemma mem_effect_main_function_exec_loop: 
  forall (n: nat)
    (e: SST.env)
    (ge: SST.genv)
    (mem initmem: M.memory)
    (bbprevid: block_id)
    (ivnextval: int)
    (NCASES: ((n = 1)%nat /\ bbprevid = Name "main") \/
             ((n > 1)%nat /\ bbprevid = Name "loop" /\
              SST.lookup_env e (Name "iv.next") = mret (DVALUE_I32 ivnextval) /\
              Int32.unsigned ivnextval + 1 <= Z.of_nat n))
    (arrblockidx: Z)
    (ENV_AT_ARR: SST.lookup_env e (Name "arr") = mret (DVALUE_Addr (arrblockidx, 0)))
    (INITMEM_ARR: mem = M.add arrblockidx (M.make_empty_block DTYPE_Pointer) initmem)
    (N_INRANGE: Z.of_nat n <= Int32.max_unsigned),
    mapM fst (M.memEffect
                mem
                (SST.execFunctionAtBBId [] ge e (mainCFG n) (Name "main") (Some bbprevid)
                                        (Name "loop")))  ≡
         Ret (create_mem_effect_of_loop
                arrblockidx
                   n
                   mem).
Proof.
  Opaque SST.step_sem_tiered.
  Opaque SST.execBBInstrs.
  Opaque SST.execBBAfterLoc.
  Opaque SST.execFunctionAtBBId.
  Opaque Trace.bindM.
  intro n.
  
  destruct n as [zero | n].

  - (*n = 0 *)
    intros.
  (* Is this even sensible? :P *)
    destruct NCASES; destruct H; omega.

  - induction n.

   (*n = S n *)
    intros.
    simpl.
    + (* Sn = 1 *)
      unfold create_mem_effect_of_loop.
      simpl.
      destruct NCASES as [PREV_MAIN | PREV_LOOP];
        try (destruct PREV_LOOP; omega).
      destruct PREV_MAIN as [_ PREV_MAIN]; subst.

      (* Force evaluation of BB loop from init *)
      setoid_rewrite SST.force_exec_function_at_bb_id; eauto.
      simpl.
      setoid_rewrite M.memEffect_commutes_with_bind.
      rewrite exec_bbLoop_from_init; try omega; try eauto.

      simpl.

      assert (O_PLUS_O_IS_ONE: Int32.eq (Int32.add (Int32.repr 0) (Int32.repr 1)) (Int32.repr 1)).
      unfold Int32.eq.
      unfold Coqlib.zeq.
      admit.

      rewrite O_PLUS_O_IS_ONE.
      euttnorm.
      M.forcemem.
      euttnorm.

      (** Force evaluation of exit edge *)
      setoid_rewrite SST.force_exec_function_at_bb_id; eauto.
      simpl.
      setoid_rewrite M.memEffect_commutes_with_bind.
      rewrite exec_exit.
      M.forcemem.
      euttnorm.
      M.forcemem.
      euttnorm.

    + (* induction case *)
      intros.

      
      destruct NCASES as [PREV_MAIN | PREV_LOOP];
        try (destruct PREV_MAIN; omega; fail).

      destruct PREV_LOOP as [NVAL [BBPREV [ENV_AT_IVNEXT IVNEXT_LIMITS]]].
      subst.

      
      (* Force evaluation of BB loop from init *)
      setoid_rewrite SST.force_exec_function_at_bb_id; eauto.
      simpl.
      setoid_rewrite M.memEffect_commutes_with_bind.

      assert (IVNEXTVAL_CASES: Int32.unsigned ivnextval + 1 < Z.of_nat (S (S n))\/
              Int32.unsigned ivnextval + 1 = Z.of_nat (S (S n))).
      omega.

      destruct IVNEXTVAL_CASES as [IV_INNER | IV_EXIT].

      * (* IV_INNER CASE *)
        rewrite exec_bbLoop_from_bbLoop_inner_iterations; eauto; try (zify; omega; fail).
        euttnorm.
        remember ((SST.add_env (Name "cond") (DVALUE_I1 Int1.zero)
             (SST.add_env (Name "iv.next")
                (DVALUE_I32 (Int32.add ivnextval (Int32.repr 1)))
                (SST.add_env (Name "iv") (DVALUE_I32 ivnextval) e)))) as ECUR.


        assert (EXEC_MAINCFG_SS_EQUIV_S: (SST.execFunctionAtBBId [] ge ECUR (mainCFG (S (S n))) 
                                        (Name "main") (Some (Name "loop")) (Name "loop"))
                  ≡ (SST.execFunctionAtBBId [] ge ECUR (mainCFG (S n))) 
                  (Name "main") (Some (Name "loop")) (Name "loop")).
        admit.

        rewrite EXEC_MAINCFG_SS_EQUIV_S.
        rewrite IHn; eauto; try omega.
        all: cycle 1.
        right.
        repeat split; try auto.
        admit.
        rewrite HeqECUR.
        rewrite SST.lookup_env_tl; auto.
        rewrite SST.lookup_env_hd; auto.
        simpl.
        zify.
        admit.
        rewrite HeqECUR.
        repeat rewrite SST.lookup_env_tl; auto.
        rewrite ENV_AT_ARR. eauto.
Abort.
  
  
(* Lemma I care about *)
Theorem looprev_same_semantics:
  forall (n: nat),
    run_mcfg_with_memory_tiered (program n) ≡ run_mcfg_with_memory_tiered (program' n).
Proof.
  intros.
  unfold run_mcfg_with_memory_tiered.
Abort.
*)