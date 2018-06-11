
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

    


Module STORESWITCHPROOF (A:MemoryAddress.ADDRESS) (LLVMIO:LLVM_INTERACTIONS(A)).
  (* Need this to simplify proofs, otherwise I need to painfully destruct
  execution chains. *)
Import FunctionalExtensionality.

Import SS.
Import LLVMIO.


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

  destruct (find_function CFG (Name "main")) as [mainfn | _].
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

    destruct (blks (df_instrs d)) eqn:BLKS; simpl; try euttnorm.
    destruct l; simpl.
    + (** HAVE ONLY ONE BB **)
      admit.
    + (** HAVE MULTIPLE BBS **)
      inversion BLKS.
      simpl.
      destruct (blk_id b == init (df_instrs d)); simpl.
      



    
    
  - (** NO FUNCTION **)
    simpl in FINDFN_REWRITE.
    rewrite FINDFN_REWRITE in *.
    simpl in *.
    euttnorm.

End STORESWITCHPROOF.