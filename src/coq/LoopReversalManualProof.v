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
From Coq Require ssreflect.
Import ssreflect.SsrSyntax.
Set Printing Implicit Defensive.


Require Import Vellvm.Memory.

Opaque M.add_all_index.
Opaque M.lookup_all_index.
Opaque M.make_empty_block.

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


Hint Transparent SS.init_state.
Hint Unfold SS.init_state.

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

(* 
Lemma eval_exp_const: 
    (tds: typedefs)
    (ot: option dtyp)
    (t: dtyp)
    (ge: SST.genv)
    (e: SST.env),
    (SST.eval_exp tds ge e ot  EXP_Integer (x:int)

                        
  (SST.eval_exp tds ge (SST.add_env (Name "iv") (DVALUE_I32 (Int32.repr 0)) e)
*)

Opaque SST.eval_exp.



(** *Instruction effects *)

(** Effect of alloca *)
Lemma effect_alloca:  forall 
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
(** Effect of store *)
Lemma effect_store: forall
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

(** ***Evaluate INSTR_OP *)
Lemma exec_inst_op: forall
             (tds: typedefs)
             (ge:  SST.genv)
             (e: SST.env)
             (vale: exp)
             (dvale: dvalue)
             (name: string),
    SST.execInst tds ge e (IId (Name name)) (INSTR_Op vale) ≡ Err "foo".
Proof.
  intros.
  simpl.
  constructor.
Qed.
  

Opaque SST.execInst.

(** *Basic block effects *)
Lemma exec_bbInit: forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (mem: M.memory),
    M.memEffect mem (SST.execBB tds ge e None (bbInit n)) ≡
                 Ret (M.add (M.size mem) (M.make_empty_block DTYPE_Pointer) mem,
                      SST.BBRBreak (SST.add_env (Name "arr") (DVALUE_Addr (M.size mem, 0)) e) (Name "loop")).
Proof.
  intros.
  unfold SST.execBB.
  unfold SST.evalPhis.
  unfold bbInit.
  
  simpl.
  euttnorm.
  M.forcemem.
  simpl.
  euttnorm.

  simpl.
  rewrite M.memEffect_commutes_with_bind.
  rewrite effect_alloca; eauto.
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
  rewrite effect_alloca; eauto.
  euttnorm.
  unfold SST.eval_typ.
  rewrite normalize_type_equation.
  unfold i32PTRTY.
  euttnorm.
  M.forcemem.
  euttnorm.
Qed.

(** Equivalence of init BBs *)
Lemma exec_bbInit_exec_bbInitRewrite_equiv:
   forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (mem: M.memory), 
     M.memEffect mem (SST.execBB tds ge e None (bbInitRewrite n)) ≡
                 M.memEffect mem (SST.execBB tds ge e None (bbInit n)).
Proof.
  intros.
  rewrite exec_bbInit.
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
      M.memEffect mem (SST.evalPhis tds ge e (Some simpleProgramInitBBId) (blk_phis (bbLoop n))) ≡ (Ret (mem, SST.add_env (Name "iv") (DVALUE_I32 (Int32.repr 0)) e)).
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
  (* again, why can't I rewrite with memEffect_ret? *)
  rewrite -> @Trace.matchM with (i := M.memEffect _ _).
  simpl.
  euttnorm.

  (** TODO: rewrite eval_exp_const theories **)
Admitted.

Lemma exec_bbLoop_from_init: forall (n: nat)
    (N_GEQ_1: (n >= 1)%nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (mem initmem: M.memory)
    (EATARR: (SST.lookup_env e (Name "arr")) = mret (DVALUE_Addr (M.size initmem, 0)))
    (MEMATARR: mem = (M.add (M.size initmem) (M.make_empty_block DTYPE_Pointer) initmem))
  t,
    M.memEffect mem (SST.execBB tds ge e (Some (blk_id (bbInit n))) (bbLoop n)) ≡ t.
                
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
  setoid_rewrite effect_store; eauto.
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
  simpl.
  rewrite MEMATARR.
  rewrite M.lookup_add; auto.
  euttnorm.
  M.forcemem.
  simpl.
  rewrite M.lookup_add; auto.
  euttnorm.
  M.forcemem.

  assert (N_NOT_LEQ_0: Z.of_nat n <=? Int32.unsigned (Int32.repr 0) = false).
  (** since n >= 1, n is not <= 0 **)
  admit.

  rewrite N_NOT_LEQ_0.
  simpl.
  euttnorm.
  simpl.
  (* TODO: fix the opening of add_all_index *)
  (* evaluate iv.next *)
  rewrite SST.force_exec_bb_instrs.
  
  

  
  
  
  
  unfold exp_const_z.
  rewrite eval_exp_gep.
  rewrite SST.lookup_env_hd; auto.
  simpl.
  euttnorm.
  M.forcemem.
  rewrite SST.lookup_env_tl; auto.
  rewrite EATARR.
  simpl.
  Opaque SST.execBBInstrs.
  repeat progress (autorewrite with euttnormdb).
  euttnorm.

  (* From this program:

       (Vis
          (IO.GEP (SST.eval_typ tds (arr_ty n)) (DVALUE_Addr (M.size mem, 0))
             [DVALUE_I32 (Int32.repr 0)]) *)
  M.forcemem.
  simpl.
  rewrite MEMATARR.
  rewrite M.lookup_add.
  euttnorm.
  M.forcemem.
  simpl.
  rewrite M.lookup_add.
  euttnorm.
  M.forcemem.
  unfold SST.eval_typ.
  rewrite normalize_type_equation.
  unfold arr_ty.
  simpl.

  unfold TRIPCOUNT.

  assert (NAT_LE_0: Z.of_nat n <=? Int32.unsigned (Int32.repr 0) = true).
  simpl.
  admit.

  destruct (Z.of_nat n <=? Int32.unsigned (Int32.repr 0)); try (inversion NAT_LE_0; fail).
  simpl.
  M.forcemem.
  euttnorm.
  

  (* From the whole program:

        M.lookup (M.size initmem)
          (M.add (M.size initmem) (M.make_empty_block DTYPE_Pointer) initmem)
  *)

  rewrite MEMATARR.
Abort.

Lemma exec_bbLoop_from_bbLoop: forall (n: nat)
    (tds: typedefs)
    (ge: SST.genv)
    (e: SST.env)
    (mem: M.memory),
    exists t,
      M.memEffect mem (SST.execBB tds ge e
                                  (Some (blk_id (bbLoop n)))
                                  (bbLoop n)) ≡ t.
Proof.
Abort.
              

(** *Full effects *)



(** tiered semantics is already paying off, I can look at what happens
when I execute a function **)
Lemma mem_effect_main_function_orig: forall (n: nat) (initmem: M.memory) eff,
  M.memEffect initmem (SST.execFunction []
              (SST.ENV.add (Name "main") (DVALUE_Addr (M.size  (a:=Z) M.empty, 0))
                 (SST.ENV.empty dvalue)) (SST.env_of_assoc []) 
              (mainCFG n) (Name "main")) ≡ eff.
Proof.
  Opaque SST.step_sem_tiered.
  Opaque SST.execBBInstrs.
  Opaque SST.execBBAfterLoc.
  Opaque SST.execFunctionAtBBId.
  Opaque Trace.bindM.
  intros.
  unfold SST.execFunction.
  simpl.

  (* Force function evaluation *)
  unfold simpleProgramInitBBId.
  setoid_rewrite SST.force_exec_function_at_bb_id; eauto.
  simpl.
  setoid_rewrite M.memEffect_commutes_with_bind.

  (* Nice, proof composition! *)
  setoid_rewrite exec_bbInit.

  euttnorm.
  setoid_rewrite SST.force_exec_function_at_bb_id; eauto.
  simpl.
  rewrite M.memEffect_commutes_with_bind; eauto.


  assert (EVAL_LOOP_FROM_INIT: forall eff,
         (M.memEffect (M.add (M.size  (a:= M.mem_block) initmem) (M.make_empty_block DTYPE_Pointer) initmem)
       (SST.execBB []
          (SST.ENV.add (Name "main") (DVALUE_Addr (M.size  (a:= M.mem_block) M.empty, 0))
             (SST.ENV.empty dvalue))
          (SST.add_env (Name "arr") (DVALUE_Addr (M.size initmem, 0))
                       (SST.env_of_assoc [])) (Some (Name "init")) (bbLoop n)))
           ≡ eff).
  intros.
  unfold SST.execBB.
  rewrite M.memEffect_commutes_with_bind; eauto.
  rewrite  exec_bbLoop_phis_from_init.
  euttnorm.
  rewrite SST.force_exec_bb_instrs.
  simpl.
  rewrite M.memEffect_commutes_with_bind; eauto.
  setoid_rewrite effect_store; eauto.
  simpl.
  euttnorm.

  (* (Vis
          (IO.GEP (SST.eval_typ [] (arr_ty n)) (DVALUE_Addr (M.size initmem, 0))
* )
  (* We now have the Vis node for the GEP *)
  M.forcemem.

  (** we are now evaluating the GEP **)
  simpl.
  rewrite M.lookup_add; auto.
  euttnorm.
  M.forcemem.
  unfold SST.eval_typ. simpl. rewrite normalize_type_equation. simpl.
  rewrite M.lookup_add; auto.
  euttnorm.
  M.forcemem.

  

  (* force BB evaluation *)
Abort.
  

                                              

(** Show this spurious proof to experiment with unfolding our new
definition of program semantics **)
Lemma run_mcfg_with_memory_orig:
  forall (n: nat),
    run_mcfg_with_memory_tiered (program n) ≡ 
                                Ret (DVALUE_I32  (Int32.repr 1%Z)).
Proof.
  intros.
  unfold run_mcfg_with_memory_tiered.
  unfold SST.init_state_tiered.
  unfold SST.build_global_environment_tiered.
  unfold SST.allocate_globals_tiered.
  simpl.
  euttnorm.

  unfold SST.register_functions_tiered.
  simpl.
  euttnorm.

  unfold SST.register_declaration_tiered.
  simpl.
  euttnorm.

  M.forcemem.
  euttnorm.
  
  unfold SST.initialize_globals_tiered. simpl.
  euttnorm.

  rewrite SST.force_step_sem_tiered.
  simpl.
  
  (** Need the opacity to make sure that Coq does not "unfold" too much **)
  Opaque SST.execBB.
  Opaque SST.step_sem_tiered.
  Opaque SST.execFunction.
  Opaque Trace.bindM.

  
  simpl.
  rewrite @Trace.matchM with (i := SST.execInterpreter _ _ _ _ _ ).
  simpl.
  rewrite M.rewrite_memD_as_memEffect.
  M.forcemem.
  euttnorm.
Abort.
  
(* Lemma I care about *)
Theorem looprev_same_semantics:
  forall (n: nat),
    run_mcfg_with_memory_tiered (program n) ≡ run_mcfg_with_memory_tiered (program' n).
Proof.
  intros.
  unfold run_mcfg_with_memory_tiered.
Abort.
  