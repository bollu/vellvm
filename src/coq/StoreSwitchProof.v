
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
Require Import Vellvm.Memory.
Require FunctionalExtensionality.
Require Import Eqdep_dec.
Require Import Classical.
Import Trace.MonadVerif.


From mathcomp Require ssreflect ssrbool ssrfun bigop.
Import ssreflect.SsrSyntax.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Open Scope Z_scope.
Open Scope string_scope.

Locate "==".

Import SS.
    

  (* Need this to simplify proofs, otherwise I need to painfully destruct
  execution chains. *)
Import FunctionalExtensionality.


Lemma bindM_Raise: forall {A B: Type}
                     (s: string) (f: A -> IO.Trace B), bindM (raise s) f ≡ Err s.
Proof.
  intros.
  unfold raise.
  unfold IO.exn_trace.
  euttnorm.
Qed.

Hint Resolve bindM_Raise.
Hint Rewrite @bindM_Raise:euttnormdb.
    

Lemma  eval_type_I64: forall (cfg: mcfg),
    eval_typ cfg (TYPE_I 64) = DTYPE_I 64.
Proof.
  intros.
  unfold eval_typ.
  rewrite normalize_type_equation.
  auto.
Qed.


Hint Resolve eval_type_I64.


Lemma  eval_type_I32: forall (cfg: mcfg),
    eval_typ cfg (TYPE_I 32) = DTYPE_I 32.
Proof.
  intros.
  unfold eval_typ.
  rewrite normalize_type_equation.
  auto.
Qed.

Hint Resolve eval_type_I32.

Lemma eval_type_array_i32: forall (CFG: mcfg),
    (SS.eval_typ CFG (TYPE_Array 2 (TYPE_I 32))) =
    DTYPE_Array 2 (DTYPE_I 32).
Proof.
  intros.
  unfold SS.eval_typ.
  repeat (rewrite normalize_type_equation; simpl).
  auto.
Qed.

Hint Resolve eval_type_array_i32.

Lemma eval_typ_equals: forall (mcfg: mcfg) (t: typ),
    eval_typ (rewrite_mcfg mcfg) t = eval_typ mcfg t.
Proof.
  intros.
  repeat (unfold eval_typ).
  repeat (rewrite normalize_type_equation).

  destruct t; auto.
Qed.

Hint Resolve eval_typ_equals.
Hint Rewrite eval_typ_equals.

Definition patternMkGEPAtIx (ix: Z)  : texp :=
  ((TYPE_Array 2 i32TY), OP_GetElementPtr (TYPE_Array 2 (TYPE_I 32%Z))
                                          (TYPE_Pointer (TYPE_Array 2 (TYPE_I 32%Z)),
                                           EXP_Ident (ID_Local (Name "x")))
                                          [(i32TY, EXP_Integer ix)]).

Definition codeToMatch  : code :=
     [(IId (Name "x"), INSTR_Alloca i32PTRTY (Some ((TYPE_I (32%Z)),  EXP_Integer 0)) None);
        (IVoid 0%Z, INSTR_Store  false (TYPE_I (32%Z), EXP_Integer 0)
                                 (patternMkGEPAtIx 0) None);
        (IVoid 1%Z, INSTR_Store  false (TYPE_I (32%Z), EXP_Integer 1) (patternMkGEPAtIx 1) None);
        (IId (Name "xat0"), INSTR_Load false (TYPE_I (32%Z)) (patternMkGEPAtIx 0) None)].


Definition codeAfterRewrite : code :=
     [(IId (Name "x"), INSTR_Alloca i32PTRTY (Some ((TYPE_I (32%Z)),  EXP_Integer 0)) None);
        (IVoid 1%Z, INSTR_Store  false (TYPE_I (32%Z), EXP_Integer 1)
                                 (patternMkGEPAtIx 1) None);
        (IVoid 0%Z, INSTR_Store  false (TYPE_I (32%Z), EXP_Integer 0) (patternMkGEPAtIx 0) None);
        (IId (Name "xat0"), INSTR_Load false (TYPE_I (32%Z)) (patternMkGEPAtIx 0) None)].


Lemma no_code_match_pattern_implies_no_rewrite:
  forall (c: code)
    (NOMATCH: c <> codeToMatch)
    (bb: block)
    (C_IS_CODE_BB: blk_code bb = c),
    rewrite_main_bb  bb = None.
Proof.
  intros.
  destruct bb; subst.
  unfold rewrite_main_bb.
  simpl.
  destruct (blk_phis); try reflexivity.
  destruct (blk_code); try reflexivity.
  destruct p; try reflexivity.
Admitted.

Definition termToMatch : instr_id * terminator :=
  (IVoid 2%Z, TERM_Ret (i32TY, (EXP_Ident (ID_Local (Name "xat0"))))).

Lemma no_term_match_pattern_implies_no_rewrite:
  forall (t: instr_id *terminator)
    (NOMATCH: t <> termToMatch)
    (bb: block)
    (C_IS_CODE_BB: blk_term bb = t),
    rewrite_main_bb  bb = None.
Proof.
  intros.
  unfold rewrite_main_bb.
Admitted.
  

Lemma m_globals_equals: forall (CFG: mcfg),
    m_globals (rewrite_mcfg CFG) = m_globals CFG.
Proof.
  intros.
  destruct CFG.
  reflexivity.
Qed.

Hint Resolve m_globals_equals.
Hint Rewrite m_globals_equals.

Lemma m_declaration_equals: forall (CFG: mcfg),
    m_declarations (rewrite_mcfg CFG)  = m_declarations CFG.
Proof.
  intros.
  destruct CFG.
  reflexivity.
Qed.

Hint Resolve m_declaration_equals.
Hint Rewrite m_declaration_equals.

Lemma preserves_prototypes: forall (CFG: mcfg),
    map df_prototype (m_definitions (rewrite_mcfg CFG)) = map df_prototype (m_definitions CFG).
Proof.
  intros.
  destruct CFG.
  simpl.
  destruct m_globals; try reflexivity.
  destruct m_declarations; try reflexivity.
  destruct m_definitions; try reflexivity.
  destruct m_definitions; try reflexivity.
  unfold rewrite_main_definition.
  simpl.
  destruct (dc_name (df_prototype d) == Name "main"); try reflexivity.
Qed.



Hint Resolve m_declaration_equals.
Hint Rewrite m_declaration_equals.

Lemma allocate_globals_equals: forall (CFG: mcfg),
    TopLevel.SS.allocate_globals (rewrite_mcfg CFG) (m_globals (rewrite_mcfg CFG)) =
    TopLevel.SS.allocate_globals CFG (m_globals CFG).
Proof.
  intros.
  unfold TopLevel.SS.allocate_globals.
  rewrite m_globals_equals.
  destruct (m_globals CFG); try reflexivity.
Qed.


Hint Resolve allocate_globals_equals.
Hint Rewrite allocate_globals_equals.


Lemma find_function_equals:
  forall (CFG: mcfg)
    (globals : m_globals CFG = [])
    (declarations : m_declarations CFG = [])
    (d : definition cfg)
    (definitions : m_definitions CFG = [d]),
    find_function (rewrite_mcfg CFG) (Name "main") =
    option_map (fun d =>
                  {|
                    df_prototype := df_prototype d;
                    df_args := df_args d;
                    df_instrs := rewrite_main_cfg (df_instrs d) 
                  |})
               (find_function CFG (Name "main")) /\
    (forall d0, find_function CFG (Name "main") = Some d0 -> d0 = d).
Proof.
  intros.
  unfold find_function.
  rewrite definitions.
  unfold rewrite_mcfg.

  destruct m_globals; try discriminate.
  destruct m_declarations; try discriminate.
  destruct m_definitions; try discriminate.
  inversion definitions.
  subst.
  simpl.

  unfold find_defn.
  unfold ident_of.
  unfold ident_of_definition.
  unfold ident_of.
  unfold rewrite_main_definition.
  unfold ident_of_declaration.
  split.

  - destruct (dc_name (df_prototype d) == Name "main") eqn:name.
    simpl.
    rewrite e in *.
    destruct (ID_Global (Name "main") == ID_Global (Name "main")) eqn:eqrefl;
      try reflexivity.
    destruct (ID_Global (dc_name (df_prototype d)) == ID_Global (Name "main"));
      try reflexivity.
    inversion e.
    contradiction.
  - intros.
    destruct (ID_Global (dc_name (df_prototype d)) == ID_Global (Name "main"));
      inversion H; auto.
Qed.
Hint Resolve find_function_equals.
Hint Rewrite find_function_equals.


Lemma find_function_entry_equals:
  forall (CFG: mcfg)
    (globals : m_globals CFG = [])
    (declarations : m_declarations CFG = [])
    (d : definition cfg)
    (definitions : m_definitions CFG = [d]),
    (find_function_entry (rewrite_mcfg CFG) (Name "main") =
    find_function_entry CFG (Name "main")).
Proof.
  intros.
  unfold find_function_entry.

  assert (FIND_FN: find_function (rewrite_mcfg CFG) (Name "main") =
          option_map (fun d =>
                        {|
                          df_prototype := df_prototype d;
                          df_args := df_args d;
                          df_instrs := rewrite_main_cfg (df_instrs d) 
                        |})
                     (find_function CFG (Name "main")) /\
    (forall d0, find_function CFG (Name "main") = Some d0 -> d0 = d)).
  eauto.

  destruct FIND_FN as [REWRITE_FN  ORIGINAL_FN].

  destruct (find_function CFG (Name "main")) eqn:FINDFN;
    rewrite REWRITE_FN; auto.

  (** We want a winess of d0 = d **)
  specialize (ORIGINAL_FN d0 eq_refl).
  subst.
  simpl.
  
  destruct (blks (df_instrs d)); auto.
  destruct l; auto.

  simpl.
  unfold rewrite_main_bb.
  destruct (blk_phis b); auto.
  assert (CODE_CASES:
            {blk_code b = codeToMatch} + {blk_code b <> codeToMatch}); auto.
  destruct CODE_CASES as [CODE_MATCH | CODE_NOMATCH]; auto.
  - unfold codeToMatch in CODE_MATCH. inversion CODE_MATCH as [BB_CODE].
    rewrite BB_CODE.

    assert (TERM_CASES: {blk_term b = termToMatch} +
                        {blk_term b <> termToMatch}); auto.
    
Abort.

Lemma register_functions_equal: forall (CFG: mcfg) (ge: TopLevel.SS.genv),
    TopLevel.SS.register_functions (rewrite_mcfg CFG) ge ≡
    TopLevel.SS.register_functions (CFG) ge.
Proof.
  intros.
  unfold TopLevel.SS.register_functions.
  simpl.
  destruct m_globals; try reflexivity.
  destruct m_declarations; try reflexivity.
  destruct m_definitions; try reflexivity.
  simpl.
  destruct l; try reflexivity.
  simpl.
  intros.
  euttnorm.
  destruct d. simpl. unfold rewrite_main_definition. simpl.
  destruct (dc_name df_prototype == Name "main"); try reflexivity.
Qed.


Hint Resolve register_functions_equal.
Hint Rewrite register_functions_equal.

(* 
Lemma find_blocks:

  (CFG : mcfg)
  (globals : m_globals CFG = [])
  (declarations : m_declarations CFG = [])
  (d : definition cfg)
  (definitions : m_definitions CFG = [d])
  find_block (blks (df_instrs d)) (init (df_instrs d)) = Some x \/
  find_block blk
 *)

Lemma rewrite_main_cfg_cases: forall c,
    rewrite_main_cfg c = c \/
    exists b bnew,
      rewrite_main_bb b = Some bnew /\
      blks c = [b] /\
      rewrite_main_cfg c =  {| init := init c; blks := [bnew]; args := args c |} /\
      blk_code b = codeToMatch /\
      blk_term b = termToMatch /\
      blk_phis b = [].
Proof.
  intros.
  unfold rewrite_main_cfg.
  simpl.
  destruct c eqn:CVAL; simpl.
  destruct blks; auto.
  destruct blks; auto.

  assert (CODE_CASES:
            {blk_code b = codeToMatch} + {blk_code b <> codeToMatch}); auto.

  assert (TERM_CASES:
            {blk_term b = termToMatch} + {blk_term b <> termToMatch}); auto.
  (* need terminator decidable equality *)
  admit.

  destruct CODE_CASES as [CODE_MATCH | CODE_NOMATCH].
  - (** CODE MATCHED **)

    destruct TERM_CASES as [TERM_MATCH | TERM_NOMATCH].
    + (** TERM MATCHED **)
      unfold rewrite_main_bb.
      destruct (blk_phis b) eqn:PHIS; auto.
      rewrite CODE_MATCH. unfold codeToMatch.
      rewrite TERM_MATCH. unfold termToMatch.
      unfold isGEPAtIx, patternMkGEPAtIx. simpl.
      right.
      exists b.
      repeat esplit; auto.
      rewrite PHIS.
      rewrite CODE_MATCH.
      rewrite TERM_MATCH.
      unfold codeToMatch, termToMatch.
      unfold patternMkGEPAtIx.
      simpl.
      auto.

    +  assert (REWRITE_BB: rewrite_main_bb b = None).
       eapply no_term_match_pattern_implies_no_rewrite with (t := blk_term b);
         auto.
       rewrite REWRITE_BB; auto.
       

    
  - assert (REWRITE_BB: rewrite_main_bb b = None).
    eapply no_code_match_pattern_implies_no_rewrite; eauto.
    rewrite REWRITE_BB.
    auto.
    (** Admitted because I need decidable equality on terminators **)
Admitted.

Lemma exec_new_program: forall 
  (CFG : mcfg)
  (globals : m_globals CFG = [])
  (declarations : m_declarations CFG = [])
  (df_prototype : declaration)
  (df_args : list local_id)
  (df_instrs : cfg)
  (definitions : m_definitions CFG =
                [{|
                 df_prototype := df_prototype;
                 df_args := df_args;
                 df_instrs := df_instrs |}])
  (FINDFN_REWRITE : find_function (rewrite_mcfg CFG) (Name "main") =
                   Some
                     {|
                     df_prototype := LLVMAst.df_prototype
                                       {|
                                       df_prototype := df_prototype;
                                       df_args := df_args;
                                       df_instrs := df_instrs |};
                     df_args := LLVMAst.df_args
                                  {|
                                  df_prototype := df_prototype;
                                  df_args := df_args;
                                  df_instrs := df_instrs |};
                     df_instrs := rewrite_main_cfg
                                    (LLVMAst.df_instrs
                                       {|
                                       df_prototype := df_prototype;
                                       df_args := df_args;
                                       df_instrs := df_instrs |}) |})
  (bold bnew : block)
  (REWRITE_WITNESS : rewrite_main_bb bold = Some bnew)
  (BBS : blks df_instrs = [bold])
  (REWRITE_MAIN_CFG : rewrite_main_cfg df_instrs =
                     {|
                     init := init df_instrs;
                     blks := [bnew];
                     args := args df_instrs |})
  (CODE_OLD : blk_code bold = codeToMatch)
  (TERM_OLD : blk_term bold = termToMatch)
  (PHIS_OLD : blk_phis bold = [])
  (BLK_ID_SAME : blk_id bnew = blk_id bold)
  (BLKID_INIT : blk_id bold = init df_instrs),
  M.memD (M.add (M.size (a:=Z)(M.empty)) (M.make_empty_block DTYPE_Pointer) M.empty)
    (step_sem (rewrite_mcfg CFG)
       (Step
          (ENV.add (dc_name df_prototype)
             (IO.DV.DVALUE_Addr (M.size (a:=Z)M.empty, 0)) 
             (ENV.empty IO.DV.dvalue),
          {|
          fn := Name "main";
          bk := init df_instrs;
          pt := blk_entry_id bnew |}, ENV.empty IO.DV.dvalue, []))) ≡
    Ret (IO.DV.DVALUE_I32  (Int32.repr 0%Z)).
Proof.
  Opaque M.add_all_index.
  Opaque M.lookup_all_index.
  Opaque rewrite_main_cfg.
  intros.
  repeat forcestepsem.
  rewrite FINDFN_REWRITE; simpl.
  rewrite REWRITE_MAIN_CFG; simpl.
  rewrite BLK_ID_SAME.
  rewrite BLKID_INIT.
  destruct (init df_instrs == init df_instrs); try contradiction.

  assert (BNEW_VAL: bnew =
            {|
              
              blk_id  := blk_id bold;
              blk_phis := [];
              blk_code  := codeAfterRewrite;
              blk_term := termToMatch;
            |}).

  assert (BLK_ID_NEW_IS_INIT: blk_id bnew = init df_instrs).
  congruence.
  
  unfold rewrite_main_bb in REWRITE_WITNESS.
  rewrite PHIS_OLD, CODE_OLD, TERM_OLD in REWRITE_WITNESS.
  unfold codeToMatch, termToMatch in REWRITE_WITNESS.
  simpl in REWRITE_WITNESS.
  inversion REWRITE_WITNESS.
  unfold codeAfterRewrite.
  unfold termToMatch.
  simpl.
  reflexivity.

  do 100? [rewrite BNEW_VAL; simpl | rewrite FINDFN_REWRITE; simpl |
         rewrite REWRITE_MAIN_CFG; simpl |
         replace ( if blk_id bold == init df_instrs then true else false)
           with true; try (destruct (blk_id bold == init df_instrs);
                           try contradiction; auto) |
         progress (unfold block_to_cmd; simpl) |
         progress euttnorm |
         progress (unfold cont; simpl; M.forcememd; euttnorm; forcestepsem) |
         rewrite eval_type_I32 |
         rewrite eval_type_array_i32 |
         progress M.forcememd].

  
  replace (2 <=? Int32.unsigned (Int32.repr 0)) with false; auto.
  replace (2 <=? Int32.unsigned (Int32.repr 1)) with false; auto.
  simpl.
  replace (Int32.unsigned (Int32.repr 0)) with 0;auto.
  replace (Int32.unsigned (Int32.repr 1)) with 1; auto.
  cbn.

  euttnorm.
  forcestepsem.
  euttnorm.
  rewrite @Trace.matchM with (i := M.memD _ _).
  simpl.
  rewrite (M.lookup_all_index_of_add_all_index_full_alias); auto.
Qed.

Lemma exec_old_program: forall
  (CFG : mcfg)
  (globals : m_globals CFG = [])
  (declarations : m_declarations CFG = [])
  (df_prototype : declaration)
  (df_args : list local_id)
  (df_instrs : cfg)
  (definitions : m_definitions CFG =
                [{|
                 df_prototype := df_prototype;
                 df_args := df_args;
                 df_instrs := df_instrs |}])

  (FINDMAIN : find_function CFG (Name "main") =
             Some
               {|
               df_prototype := df_prototype;
               df_args := df_args;
               df_instrs := df_instrs |})
  (FINDFN_REWRITE : find_function (rewrite_mcfg CFG) (Name "main") =
                   Some
                     {|
                     df_prototype := LLVMAst.df_prototype
                                       {|
                                       df_prototype := df_prototype;
                                       df_args := df_args;
                                       df_instrs := df_instrs |};
                     df_args := LLVMAst.df_args
                                  {|
                                  df_prototype := df_prototype;
                                  df_args := df_args;
                                  df_instrs := df_instrs |};
                     df_instrs := rewrite_main_cfg
                                    (LLVMAst.df_instrs
                                       {|
                                       df_prototype := df_prototype;
                                       df_args := df_args;
                                       df_instrs := df_instrs |}) |})
  (bold bnew : block)
  (REWRITE_WITNESS : rewrite_main_bb bold = Some bnew)
  (BBS : blks df_instrs = [bold])
  (REWRITE_MAIN_CFG : rewrite_main_cfg df_instrs =
                     {|
                     init := init df_instrs;
                     blks := [bnew];
                     args := args df_instrs |})
  (CODE_OLD : blk_code bold = codeToMatch)
  (TERM_OLD : blk_term bold = termToMatch)
  (PHIS_OLD : blk_phis bold = [])
  (BLK_ID_SAME : blk_id bnew = blk_id bold)
  (BLKID_INIT : blk_id bold = init df_instrs),
  M.memD (M.add (M.size (a:=Z)M.empty) (M.make_empty_block DTYPE_Pointer) M.empty)
      (step_sem CFG
         (Step
            (ENV.add (dc_name df_prototype) (DVALUE_Addr (M.size (a:=Z) M.empty, 0))
               (ENV.empty dvalue),
            {|
            fn := Name "main";
            bk := init df_instrs;
            pt := blk_entry_id bold |}, ENV.empty dvalue, []))) ≡
      Ret (IO.DV.DVALUE_I32  (Int32.repr 0%Z)).
Proof.
  intros.
  forcestepsem.
  rewrite FINDMAIN; simpl.
  unfold find_block; simpl.
  rewrite BBS; simpl.
  replace ( if blk_id bold == init df_instrs then true else false)
    with true; try (destruct (blk_id bold == init df_instrs);
                    try contradiction; auto).
  unfold block_to_cmd.

  assert (TERM_ID_NEQ_ENTRY_ID: blk_term_id bold <> blk_entry_id bold ).
  unfold blk_term_id, blk_entry_id.
  rewrite TERM_OLD, CODE_OLD.
  unfold termToMatch, codeToMatch. simpl.
  auto.

  assert (ENTRY_ID_VAL: blk_entry_id bold = IId (Name "x")).
  unfold blk_entry_id.
  rewrite CODE_OLD.
  unfold fallthrough.
  unfold codeToMatch.
  reflexivity.

  assert (TERM_ID_VAL: blk_term_id bold = IVoid 2).
  unfold blk_term_id.
  rewrite TERM_OLD.
  unfold termToMatch.
  reflexivity.
  
  destruct (blk_term_id bold == blk_entry_id bold); try contradiction.
  rewrite CODE_OLD. simpl.

  destruct (blk_entry_id bold == IId (Name "x")); try contradiction.
  simpl.

  rewrite FINDMAIN; simpl.

  progress unfold find_block; simpl; rewrite BBS; simpl.

  
  replace ( if blk_id bold == init df_instrs then true else false)
    with true; try (destruct (blk_id bold == init df_instrs);
                    try contradiction; auto).

  unfold block_to_cmd.
  destruct (blk_term_id bold == blk_entry_id bold); try contradiction.
  rewrite CODE_OLD. simpl.

  destruct (blk_entry_id bold == IId (Name "x")); try contradiction.
  simpl.
  unfold blk_entry_id.
  rewrite CODE_OLD. simpl.

  euttnorm.
  
  (*

Error:
Anomaly
"File "plugins/ltac/tacinterp.ml", line 1157, characters 35-41: Assertion failed."
Please report at http://coq.inria.fr/bugs/.
   *)
  do 100? [progress (unfold cont; simpl; M.forcememd; euttnorm; forcestepsem) |
          rewrite FINDMAIN; simpl |
          progress unfold find_block; simpl; rewrite BBS; simpl |
          replace ( if blk_id bold == init df_instrs then true else false)
            with true; try (destruct (blk_id bold == init df_instrs);
                            try contradiction; auto) |
          
          
          progress (unfold block_to_cmd;
                    match goal with
                    | [ |- context [blk_term_id bold == blk_term_id bold]] =>
                      destruct (blk_term_id bold == blk_term_id bold);
                      try contradiction
                    | _ => fail
                    end) |
          rewrite TERM_OLD; simpl |
          
          progress (unfold block_to_cmd;
                    match goal with
                    | [ |- context [blk_term_id bold == blk_entry_id bold]] =>
                      destruct (blk_term_id bold == blk_entry_id bold);
                      try contradiction;
                      try (rewrite CODE_OLD; simpl)
                    | _ => fail "no match"
                    end) | 

          (* This will not work, use context pattern matches to get to the
         part of the proof which matters
         http://adam.chlipala.net/cpdt/html/Cpdt.Match.html
           *)
          progress (unfold block_to_cmd;
                    match goal with
                    | [ |- context[(blk_term_id bold ==  ?X)]] =>
                      destruct (blk_term_id bold ==  X)
                        as [TERM_ID_VAL' | ];
                      try (simpl;
                           rewrite TERM_ID_VAL' in TERM_ID_VAL;
                           inversion TERM_ID_VAL;
                           fail 10)
                    | _ => fail "no matching goal"
                    end) |

          rewrite eval_type_I32 |
          rewrite eval_type_array_i32 |
          rewrite CODE_OLD; simpl |
          progress euttnorm |
          progress M.forcememd |
          progress forcestepsem |
          progress (unfold cont)].

  
  
  replace (2 <=? Int32.unsigned (Int32.repr 0)) with false; auto.
  replace (2 <=? Int32.unsigned (Int32.repr 1)) with false; auto.
  simpl.
  replace (Int32.unsigned (Int32.repr 0)) with 0;auto.
  replace (Int32.unsigned (Int32.repr 1)) with 1; auto.
  cbn.

  euttnorm.
  forcestepsem.
  euttnorm.
  rewrite @Trace.matchM with (i := M.memD _ _).
  simpl.
  rewrite (M.lookup_all_index_of_add_all_index_no_alias); auto; try omega.
  rewrite (M.lookup_all_index_of_add_all_index_full_alias); auto.
Qed.
  

    
  

Theorem preserves_semantics:
  forall (CFG: mcfg),
    (run_mcfg_with_memory (rewrite_mcfg CFG)) ≡ (run_mcfg_with_memory CFG).
Proof.
  intros.
  unfold run_mcfg_with_memory.
  unfold TopLevel.SS.init_state.
  unfold TopLevel.SS.build_global_environment.
  rewrite m_globals_equals.
  rewrite allocate_globals_equals.
  (** Discard one choice of globals since we do nothing **)
  destruct (m_globals CFG) eqn:globals;  try (unfold rewrite_mcfg; destruct CFG; simpl in *; rewrite globals; reflexivity).
  simpl.
  euttnorm.
  unfold TopLevel.SS.allocate_globals; simpl.
  euttnorm.

  rewrite register_functions_equal.
  unfold TopLevel.SS.register_functions.
  simpl.

  (** Show for both choices of declarations *)
  destruct (m_declarations CFG) eqn:declarations;
    try (unfold rewrite_mcfg; simpl in *; rewrite globals, declarations; simpl; reflexivity).

  simpl.
  (** Discard the case where definitions is empty **)
  destruct (m_definitions CFG) eqn:definitions;
    try (unfold rewrite_mcfg; destruct CFG; simpl in *; rewrite globals, declarations, definitions; simpl; reflexivity).

  
  (** Discard the case where definitions is too large **)
  destruct l;
    try (unfold rewrite_mcfg; destruct CFG; simpl in *; rewrite globals, declarations, definitions; simpl; reflexivity).

  simpl.
  euttnorm.
  unfold register_declaration.
  euttnorm.

  repeat M.forcememd.
  repeat euttnorm.
  simpl.

  unfold initialize_globals. simpl.
  repeat euttnorm.

  (** Find function entry **)
  unfold find_function_entry.

  assert (FINDFN:
    find_function (rewrite_mcfg CFG) (Name "main") =
    option_map (fun d =>
                  {|
                    df_prototype := df_prototype d;
                    df_args := df_args d;
                    df_instrs := rewrite_main_cfg (df_instrs d) 
                  |})
               (find_function CFG (Name "main")) /\
    (forall d0, find_function CFG (Name "main") = Some d0 -> d0 = d)); auto.
  destruct FINDFN as [FINDFN_REWRITE FINDFN_VALUE].

  destruct (find_function CFG (Name "main")) as [mainfn | ] eqn:FINDMAIN.
  - (** FOUND FUNCTION **)
    assert (mainfn = d).
    apply FINDFN_VALUE; auto.
    subst.
    (** CAREFUL HERE **)
    clear FINDFN_VALUE.
    simpl in FINDFN_REWRITE.
    rewrite FINDFN_REWRITE.
    Opaque rewrite_main_cfg.
    simpl.
    destruct d.
    simpl.

    assert (REWRITE_CASES: rewrite_main_cfg df_instrs = df_instrs \/
                           exists b bnew,
                             rewrite_main_bb b = Some bnew /\
                             blks df_instrs = [b] /\
                             rewrite_main_cfg df_instrs =
                             {| init := init df_instrs;
                                blks := [bnew];
                                args := args df_instrs |} /\
                             blk_code b = codeToMatch /\
                             blk_term b = termToMatch /\
                             blk_phis b = []
           ).
    apply rewrite_main_cfg_cases; auto.

    destruct REWRITE_CASES as [NOREWRITE_CFG |
                               [bold [bnew
                                       [REWRITE_WITNESS
                                          [BBS
                                             [REWRITE_MAIN_CFG
                                                [CODE_OLD [TERM_OLD
                                                             PHIS_OLD]]]]]]]].

    + (** NO REWRITE OF CFG **)
      rewrite NOREWRITE_CFG.
      
      assert (NOREWRITE_MCFG: rewrite_mcfg CFG = CFG).
      unfold rewrite_mcfg.
      simpl.
      destruct CFG. simpl in *.
      rewrite globals, declarations, definitions.
      unfold rewrite_main_definition.
      simpl.
      destruct (dc_name (df_prototype) == Name "main"); auto.
      rewrite NOREWRITE_CFG; auto.
      rewrite NOREWRITE_MCFG.
      reflexivity.

    + (** REWRITE OF CFG **)
      rewrite BBS, REWRITE_MAIN_CFG. simpl.

      assert (BLK_ID_SAME: blk_id bnew = blk_id bold).
      unfold rewrite_main_bb in REWRITE_WITNESS.
      rewrite CODE_OLD, TERM_OLD, PHIS_OLD in REWRITE_WITNESS.
      unfold codeToMatch, termToMatch in REWRITE_WITNESS.
      unfold isGEPAtIx in REWRITE_WITNESS.
      simpl in REWRITE_WITNESS.
      inversion REWRITE_WITNESS.
      auto.

      rewrite BLK_ID_SAME.
      destruct (blk_id bold == init df_instrs) as [BLKID_INIT |BLKID_NOINIT].
      (** block id matches INIT **)
      * subst.
        euttnorm.
        
        rewrite  exec_new_program; eauto.
        rewrite exec_old_program; eauto.
        
      * (** block id does not match INIT **)
        euttnorm.

    
  - (** NO FUNCTION **)
    simpl in FINDFN_REWRITE.
    rewrite FINDFN_REWRITE in *.
    simpl in *.
    euttnorm.
Qed.

End STORESWITCHPROOF.