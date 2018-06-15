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
Require Import Vellvm.MulAdd.
Require Import Vellvm.CFG.
Require Import Vellvm.LLVMIO.
Require Import Vellvm.DynamicValues.
Require Import Vellvm.StepSemantics.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.TypeUtil.
Require Import Vellvm.Trace.
Require Import Setoid.
Require Import Coq.Setoids.Setoid.
Require Import SetoidClass.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require Import Vellvm.Pass.
Require Import FunctionalExtensionality.
Require Import Eqdep_dec.
Require Import Program Classical.



Open Scope Z_scope.
Open Scope string_scope.


Module MULADDPROOF (A:MemoryAddress.ADDRESS) (LLVMIO:LLVM_INTERACTIONS(A)).


(* 
Module SS := StepSemantics A LLVMIO.
Import SS.
*)

Import LLVMIO.
Import Trace.MonadVerif.

Module PT := PASSTHEOREMS A LLVMIO.
Import PT.

Import PT.SS.

(* Since
1. Trace X := M IO X
2. M is a free monad-style construction
3. IO is a functor,

M should lift the IO instance of function into a monad instance of (M IO).

However, Coq typeclass syntax is.. difficult to someone who's never used it,
so I'm going to Admit the monad laws for Trace (which will hold, asuming the M construction
is correct)
 *)


Check (@bindM).
Check (@mbind).

(* Clearly, I'm able to use monads in the abstract. I'm just not able to convince coq that
Trace is actually a Monad, even though
 Definition Trace X := M IO X. 
*)
Example bind_of_ret: 
  (mbind (F := M IO)) (mret (DVALUE_I64 (Int64.repr 2)))  (fun v => mret v)  ≡ mret (DVALUE_I64 (Int64.repr 2)).
Proof.
  apply mret_mbind.
Qed.


Lemma  eval_type_I64: forall (cfg: mcfg),
    eval_typ cfg (TYPE_I 64) = DTYPE_I 64.
Proof.
  intros.
  unfold eval_typ.
  rewrite normalize_type_equation.
  auto.
Qed.

Lemma eval_typ_rewrite_mcfg: forall (mcfg: mcfg) (t: typ),
    eval_typ (rewrite_mcfg mcfg) t = eval_typ mcfg t.
Proof.
  intros.
  repeat (unfold eval_typ).
  repeat (rewrite normalize_type_equation).

  destruct t; auto.
Admitted.

Lemma transform_correct:
  forall (i: Z),
 (Int64.mul (Int64.repr i) (Int64.repr 2))
  = (Int64.add (Int64.repr i) (Int64.repr i)).
Proof.
  intros.
  unfold Int64.mul.
  unfold Int64.add.
  auto with ints.

  assert (UNSIGNED_REPR_2: Int64.unsigned (Int64.repr 2) = 2).
  rewrite Int64.unsigned_repr; auto with ints.
  unfold Int64.max_unsigned. unfold Int64.modulus.
  simpl. omega.

  rewrite UNSIGNED_REPR_2.

  assert (MUL2: forall x: Z, x * 2 = x + x).
  intros. omega.

  specialize (MUL2 (Int64.unsigned (Int64.repr i))).
  rewrite MUL2.

  reflexivity.
Qed.


Lemma is_exp_equal_ints_inv: forall (o1 o2: exp),
    is_exp_equal_ints o1 o2 = true -> o1 = o2 /\
                                     exists (x: int),  o1 = (EXP_Integer x) .
Proof.
  intros.
  destruct o1; inversion H; destruct o2; inversion H; auto.
  rewrite Z.eqb_eq in H1.
  subst.
  split; auto.
  exists x0. auto.
Qed.

    
      
        


Lemma map_monad_trace_cons: forall {A B}
                        (f: A -> Trace  B)
                        (x: A)
                        (xs: list A),
    map_monad f (x :: xs) ≡
    'mx <- f x;
    'mxs <- map_monad f xs;
    mret (mx ::mxs).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.
    
  
  



Ltac unfold_fail :=  simpl; unfold failwith; unfold raise; unfold exn_trace; eauto.

Lemma eval_exp_is_ret_or_err:
  forall (expr: exp)
    (MCFG: mcfg)
    (ge: genv)
    (e: env)
    (top: option dtyp),
    (exists x, eval_exp MCFG ge e top expr ≡ Ret x) \/
    (exists err, eval_exp MCFG ge e top expr ≡ Err err).
Proof.
  intros expr.
  induction expr; intros; simpl;
    try (destruct top; try unfold_fail;
         destruct d; try unfold_fail).
  - destruct (lookup_id ge e id); eauto;
      simpl; unfold raise. unfold exn_trace. eauto.
    eauto.
  - destruct (coerce_integer_to_int sz x); eauto.
    (* ERROR, EAUTO DOES NOT WORK OVER EQUIVALENCE RELATIONS! *)
    right. unfold_fail.
    simpl.
    unfold raise, exn_trace. eauto.
    
  - destruct b; eauto.
  - (* Where is the induction principle? *)
    simpl.
    induction fields.
    + simpl.
      left.
      exists (DVALUE_Struct []).
      rewrite bindM_Ret.
      auto.
    + destruct IHfields.
      * destruct H as [X XWITNESS].
        simpl in *.
        left.
        exists (DVALUE_Struct [X]).
        destruct a.
        simpl.
        admit.
      * admit.
                
    
  - admit.
  - admit.
  - admit .
  - edestruct IHexpr1.
    admit.
Abort.
    
  

(* OP_IBinop (Add nuw_disabled nsw_disabled) (TYPE_I 64) v1 v2 *)
(*
Fixpoint eval_exp_equal (mcfg : mcfg)
                        (ge: genv)
                        (e: env)
                        (top: option dtyp)
                        (o: exp)
                        {struct o}:
    eval_exp (rewrite_mcfg mcfg) ge e top (rewrite_exp o) ≡
    eval_exp mcfg ge e top o.
Proof.
  intros.
  induction o; try reflexivity;
  repeat (apply eval_exp_equal).
Qed.
*)


(* 
Lemma lifted_instruction_pass_preserves_block_term_id:
  forall (b : LLVMAst.block),
  blk_term_id (liftInstrPassToBlockPass rewrite_instr b) =
  blk_term_id b.
Proof.
  auto.
Qed.

Hint Resolve (lifted_instruction_pass_preserves_block_term_id).
Hint Rewrite (lifted_instruction_pass_preserves_block_term_id).
  


Lemma bindm_eval_exp_equal: forall CFG g e op fn bk a s id,
  bindM
    (eval_exp (liftCFGDefinitionPassToMCFGPass rewrite_cfg_definition CFG) g e
       None (rewrite_exp op))
    (fun dv : dvalue =>
     cont (g, {| fn := fn; bk := bk; pt := a |}, add_env id dv e, s))
  ≡ bindM (eval_exp CFG g e None op)
      (fun dv : dvalue =>
         cont (g, {| fn := fn; bk := bk; pt := a |}, add_env id dv e, s)).
Proof.
  intros until CFG.
  cofix.

  intros.

  (* I do it this way because somehow, applying `symmetry` breaks
  the guardedness condition. TODO: Figure this out, the correct way *)
  rewrite (@Trace.matchM) with (i := bindM (eval_exp CFG g e None op)
                                           (fun dv : dvalue =>
                                              cont (g, {| fn := fn; bk := bk; pt := a |}, add_env id dv e, s))).
  rewrite Trace.matchM.

  simpl.

  assert (EVAL_EXP_EQ: eval_exp
            (liftCFGDefinitionPassToMCFGPass rewrite_cfg_definition CFG) g e
            None (rewrite_exp op) ≡
            eval_exp CFG g e None op).
  auto.

  remember (eval_exp CFG g e None (rewrite_exp op)) as EVAL_EXP_ORIG.

  destruct (EVAL_EXP_ORIG); simpl; auto.
Abort.

  
  
Lemma muladd_step: forall (CFG: mcfg) (s: state),
    step (rewrite_mcfg CFG) s ≡ step CFG s.
Proof.
  intros.
  unfold step.
  
  destruct s.
  
  destruct p.
  destruct p.

  
  unfold fetch.
  destruct p.

  unfold rewrite_mcfg.
  rewrite find_function_lifted_definition_pass.
  simpl.

  remember (find_function CFG fn) as CURFN.
  destruct CURFN; simpl; try reflexivity.

  rewrite find_block.

  remember (CFG.find_block (blks (df_instrs d)) bk) as CURBLOCK.
  destruct CURBLOCK; simpl; try reflexivity.


  unfold rewrite_block.
  rewrite InstrPassPreservesBlockToCmd.
  simpl.

  remember (block_to_cmd b pt) as CURCMD.
  destruct CURCMD; auto.
  destruct p.
  simpl.
  

  assert (FNEQ:
            find_function
              (liftCFGDefinitionPassToMCFGPass rewrite_cfg_definition CFG) =
            fun fnid => option_map rewrite_cfg_definition (find_function CFG fnid)).
  extensionality fid_ext.
  apply find_function_lifted_definition_pass.
  auto.

  assert (EVAL_TYP_EQ:
            (eval_typ
               (liftCFGDefinitionPassToMCFGPass rewrite_cfg_definition CFG) =
             eval_typ CFG)).
  unfold eval_typ.
  extensionality typ_ext.
  apply preserves_types_implies_preserves_eval_typ.
  unfold preserves_types.
  auto.

  assert (EVAL_EXP_EQ:
            eval_exp
              ((liftCFGDefinitionPassToMCFGPass rewrite_cfg_definition) CFG) =
            eval_exp CFG).
  extensionality g_ext.
  extensionality e_ext.
  extensionality t_ext.
  extensionality expr_ext.
  apply preserves_types_implies_preserves_eval_expr.
  unfold preserves_types.
  auto.

  assert (EVAL_JUMP_EQ:
            jump (liftCFGDefinitionPassToMCFGPass rewrite_cfg_definition CFG) =
            jump CFG).
  intros.
  
  unfold jump.
  extensionality fid_ext.
  extensionality bid_src_ext.
  extensionality bid_tgt_ext.
  extensionality g_ext.
  extensionality e_ext.
  extensionality k_ext.
  apply eq_jump; auto.
  unfold preserves_types; auto.
  apply lifted_instr_pass_to_MCFG_pass_preserves_block_entry.
  


  assert (EVAL_FIND_FUNCTION_EQ:
            find_function_entry
              (liftCFGDefinitionPassToMCFGPass rewrite_cfg_definition CFG)
            = find_function_entry CFG).
  intros.
  extensionality fid.
  apply lifted_instr_pass_preserves_function_entry.

  (* 
  assert (EVAL_OP_EQ:
          eval_op
             (liftCFGDefinitionPassToMCFGPass rewrite_cfg_definition CFG) ≡
          eval_op CFG).
  unfold eval_op.
  extensionality g_ext.
  extensionality e_ext.
  extensionality o_ext.
  apply eval_exp_equal.
  *)

  destruct c; auto; simpl.
  
  - simpl.
    repeat (rewrite EVAL_TYP_EQ).
    repeat (rewrite EVAL_EXP_EQ).
    repeat (rewrite FNEQ).
    repeat (rewrite EVAL_JUMP_EQ).
    repeat (rewrite EVAL_FIND_FUNCTION_EQ).

    destruct (find_function CFG fn); auto; simpl.
    rewrite find_block; auto.
    destruct (CFG.find_block (blks (df_instrs d0)) bk); auto; simpl.

    unfold rewrite_block; auto.
    rewrite (InstrPassPreservesBlockToCmd).
    destruct (block_to_cmd b0 pt); auto; simpl.

    
    induction p; simpl; auto.
    induction a; simpl; auto.
    ++ induction b1; simpl; auto.
       induction pt; simpl; auto.
       *** induction i; simpl; auto.
           unfold eval_op.

           assert (CUR_REWRITE: eval_exp
                     (liftCFGDefinitionPassToMCFGPass rewrite_cfg_definition CFG)
                     g
                     e
                     None
                     (rewrite_exp op) ≡ eval_exp CFG g e None op).
           rewrite eval_exp_equal.
           reflexivity.
           (* Why can't I rewrite here? Because it's inside a cofix? *)
           admit.

       *** induction i; simpl; auto.
    ++ induction b1; simpl; auto.
       induction pt; simpl; auto.
       *** induction i; simpl; auto.
           unfold eval_op.
           (* Again, why can't I rewrite? *)
           admit.
       *** induction i; simpl; auto.
       

      
  - simpl.
    repeat (rewrite EVAL_TYP_EQ).
    repeat (rewrite EVAL_EXP_EQ).
    repeat (rewrite FNEQ).
    repeat (rewrite EVAL_JUMP_EQ).
    reflexivity.

  -  auto.
  -  auto. 

Admitted.

(* 
CoFixpoint step_sem (r:result) : Trace dvalue :=
  match r with
  | Done v => mret v
  | Step s => 'x <- step s ; step_sem x
  end.
 *)

  

          
 
(* How do I force one step of step_sem? *)
Lemma step_sem_unfold_once: forall (CFG: mcfg) (s: state),
    step_sem CFG (Step s) ≡ ('x <- (step CFG s); (step_sem CFG x)).
Proof.
  intros.
  unfold step_sem.
  rewrite Trace.matchM.
  simpl.

  destruct (step CFG s).
  - rewrite bindM_Ret.
Abort.

Lemma muladd_step_sem : forall (CFG:mcfg) (r:result),
    (step_sem (rewrite_mcfg CFG) r) ≡ (step_sem CFG r).
Proof.
Abort.
*)
  
End MULADDPROOF.
