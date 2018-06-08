
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

Lemma bindM_Raise: forall {X Y : Type} (e : string) (f: X -> M IO Y),
    bindM (raise e) f ≡ raise e.
Proof.
  intros.
  unfold raise.
  unfold exn_trace.
  euttnorm.
Qed.
Hint Rewrite (@bindM_Raise) : euttnormdb.
    

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

Lemma find_function_entry_equals: forall (CFG: mcfg),
    find_function_entry (rewrite_mcfg CFG) (Name "main") =
    find_function_entry CFG (Name "main").
Proof.
  intros.
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

Lemma ident_of_prototype_equal: forall (d: definition cfg),
    ident_of (df_prototype (rewrite_main_definition d)) =
    ident_of (df_prototype d).
Proof.
  intros.
  destruct d. unfold rewrite_main_definition. simpl.
  destruct (dc_name df_prototype == Name "main"); try reflexivity.
Qed.

                                   

Hint Resolve ident_of_prototype_equal.
Hint Rewrite ident_of_prototype_equal.

Lemma find_block_of_rewritten_defn: forall (CFG: mcfg)
                                  (GLOBALS_EMPTY: m_globals CFG = [])
                                  (DECLARATIONS_EMPTY : m_declarations CFG = [])
                                  (d : definition cfg)
                                  (DEFINITIONS_VALUE : m_definitions CFG = [d])
                                  (D_IS_MAIN : ident_of (df_prototype d) = ID_Global (Name "main")),
    find_block (blks (df_instrs (rewrite_main_definition d)))
               (init (df_instrs (rewrite_main_definition d))) =
    find_block (blks (df_instrs (d)))
               (init (df_instrs (d))).
Proof.
  intros.
  unfold find_block.
  unfold rewrite_main_definition.
  simpl.
  destruct (dc_name (df_prototype d) == Name "main"); try contradiction.
  simpl.
Abort.
    
            

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

  unfold initialize_globals; simpl.
  repeat euttnorm.

  
  destruct (dc_name (df_prototype d) == Name "main").
  + (** main function **)
    assert (find_function_entry (rewrite_mcfg CFG) (Name "main") =
            find_function_entry CFG (Name "main")).

  (* find function entry *)
  unfold find_function_entry.
  simpl.

  unfold find_function.
  simpl.

  unfold find_defn.
  simpl.

  rewrite globals, declarations, definitions.
  simpl.

  destruct (ident_of ((rewrite_main_definition d)) ==
            ID_Global (Name "main")) as [DEF_REWRITE_MAIN | DEF_REWRITE_NOT_MAIN].
  destruct (ident_of   d == ID_Global (Name "main")) as [DEF_MAIN | DEF_NOT_MAIN].

  + (* We have both mains, the case we care about *)

    
    intros.
    unfold find_block.
    intros.
    unfold rewrite_main_definition.
    destruct (dc_name (df_prototype d) == Name "main") as [_ | CONTRA]; try contradiction.
    simpl.
    destruct (blks (df_instrs d)) eqn:BLKS; try auto.
    destruct l; auto.


    assert (CODE_MATCHES_DECIDABLE: {blk_code b = codeToMatch} + {blk_code b <> codeToMatch}).
    apply code_eq_dec.
    destruct CODE_MATCHES_DECIDABLE as [CODE_MATCHES  | CODE_DOES_NOT_MATCH];
      try (erewrite no_code_match_pattern_implies_no_rewrite; eauto; fail).

    
    assert (TERM_MATCHES_DECIDABLE: {blk_term b = termToMatch} + {blk_term b <> termToMatch}).
    decide equality; auto.
    apply terminator_eq_dec.
    destruct TERM_MATCHES_DECIDABLE as [TERM_MATCHES  | TERM_DOES_NOT_MATCH];
      try (erewrite no_term_match_pattern_implies_no_rewrite; eauto; fail).



              

      unfold rewrite_main_definition. simpl.
      assert (DEF_NAME_MAIN': dc_name (df_prototype d) = Name "main").
      simpl.
      unfold ident_of in DEF_MAIN.
      unfold ident_of_declaration in DEF_MAIN.
      inversion DEF_MAIN.
      auto.
      
      destruct (dc_name (df_prototype d) == Name "main"); try contradiction.
    * admit.
    * admit.
      
    
  + (** not main **)
    destruct (ident_of (df_prototype (rewrite_main_definition d)) ==
              ID_Global (Name "main")) as [DEF_REWRITE_MAIN | DEF_REWRITE_NOT_MAIN].
    * (** rewrite has main, this is contradiction since we do not change names *)
      cut (ident_of (df_prototype d) = ident_of (df_prototype (rewrite_main_definition d)));
        try apply preserves_prototypes; auto.
      intros IDENT_EQUAL.
      rewrite IDENT_EQUAL, DEF_REWRITE_MAIN in DEF_NOT_MAIN.
      contradiction.
      simpl.
      euttnorm.
      unfold raise.
      unfold IO.exn_trace.
      euttnorm.
Abort.
  

End STORESWITCHPROOF.