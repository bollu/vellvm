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

(** Enable SSReflect for better rewrite **)
From mathcomp Require ssreflect ssrbool ssrfun bigop.
Import ssreflect.SsrSyntax.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** MEMORY **)          
(** MEMORY **)          
(** MEMORY **)          
(** MEMORY **)          
(** MEMORY **)          
(** MEMORY **)          
(** MEMORY **)          
(** MEMORY **)          
(** MEMORY **)          
(** MEMORY **)          
(** MEMORY **)          


Check (M.memD).
Check (M.memD M.empty).

    

(** PROGRAM **)
(** PROGRAM **)
(** PROGRAM **)
(** PROGRAM **)
(** PROGRAM **)
(** PROGRAM **)
(** PROGRAM **)
(** PROGRAM **)
(** PROGRAM **)
(** PROGRAM **)
(** PROGRAM **)
  
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

Definition simpleProgramInitBBId : block_id := Name "entry".
                                

Notation i32ty := (TYPE_I (32%Z)).
Notation i8ty := (TYPE_I (8%Z)).
Notation i32ptrty :=  (TYPE_Pointer i32ty).
Notation i8ptrty :=  (TYPE_Pointer i8ty).
Definition mkI32 (i: Z): texp :=
  (i32ty, EXP_Integer i).


Definition mkI8 (i: Z): texp :=
  (i8ty, EXP_Integer i).

Definition xty := TYPE_Array 2 i32ty.
Definition xptrty := TYPE_Pointer xty.
Definition mkLLVMInt (i: Z): texp := mkI32 i.




 (*INSTR_Alloca (t:typ) (nb: option texp) (align:option int)  *)
Definition allocaX : instr_id * instr :=
  (IId (Name "x"),
   INSTR_Alloca (xptrty) (Some (mkLLVMInt 0)) None).

Definition xexpr: texp := (xptrty, EXP_Ident (ID_Local (Name "x"))).

(* OP_GetElementPtr    (t:typ) (ptrval:(typ * exp)) (idxs:list (typ * exp)) *)
Definition mkGEPI32 (name: string) (idx: Z) : texp :=
  (xty, OP_GetElementPtr xty
                   (xptrty, EXP_Ident (ID_Local (Name name)))
                   ([mkI32 idx])).


Definition mkGEPI8 (name: string) (idx: Z) : texp :=
  (i8ptrty, OP_GetElementPtr i8ty
                   (i8ptrty, EXP_Ident (ID_Local (Name name)))
                   ([mkI32 idx])).

Definition mkXGEP := mkGEPI32.

(* INSTR_Store (volatile:bool) (val:texp) (ptr:texp) (align:option int) *)
Definition storeXAt0: instr_id * instr :=
  (IVoid 0%Z, INSTR_Store false (mkLLVMInt 1) (mkXGEP "x" 0) None).

Definition storeXAt1: instr_id * instr :=
  (IVoid 1%Z, INSTR_Store false (mkLLVMInt 2) (mkXGEP "x" 1) None).

(* INSTR_Load  (volatile:bool) (t:typ) (ptr:texp) (align:option int)  *)
Definition loadXAt0: instr_id * instr :=
  (IId (Name "xat0"), INSTR_Load false i32ty (mkXGEP "x" 0) None).
  
Definition pcfg : cfg := 
{|
  init := simpleProgramInitBBId;
  blks := [{|
      blk_id     := simpleProgramInitBBId;
      blk_phis  := [];
      blk_code  := [ allocaX; storeXAt0; storeXAt1; loadXAt0 ];
      blk_term  := ((IVoid 2%Z),
                    TERM_Ret (i32ty, (EXP_Ident (ID_Local (Name "xat0")))))
    |}];
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


Definition pmain : definition cfg  :=
  {|
    df_prototype   := mainproto;
    df_args        := [];
    df_instrs      := pcfg;
  |}.

Definition program : mcfg :=
  {|
    m_name := None;
    m_target := None;
    m_datalayout := None;
    m_type_defs := [];
    m_globals := [];
    m_declarations := [];
    m_definitions:= [pmain];
  |}.


(** Modified program **)

  
Definition pcfg' : cfg := 
{|
  init := simpleProgramInitBBId;
  blks := [{|
      blk_id     := simpleProgramInitBBId;
      blk_phis  := [];
      blk_code  := [ allocaX; storeXAt1; storeXAt0; loadXAt0 ];
      blk_term  := ((IVoid 2%Z),
                    TERM_Ret (i32ty, (EXP_Ident (ID_Local (Name "xat0")))))
    |}];
  args := [];
|}.
  
Definition pmain' : definition cfg  :=
  {|
    df_prototype   := mainproto;
    df_args        := [];
    df_instrs      := pcfg';
  |}.
Definition program': mcfg := 
  {|
    m_name := None;
    m_target := None;
    m_datalayout := None;
    m_type_defs := [];
    m_globals := [];
    m_declarations := [];
    m_definitions:= [pmain'];
  |}.
Close Scope list_scope.



Lemma program_program'_register_fn_eq:
  TopLevel.SS.register_functions
    program
    (TopLevel.SS.ENV.empty IO.DV.dvalue) ≡
    TopLevel.SS.register_functions
    program'
    (TopLevel.SS.ENV.empty IO.DV.dvalue) /\
  TopLevel.SS.register_functions program
                                 (TopLevel.SS.ENV.empty IO.DV.dvalue) =
Trace.Tau
    (TopLevel.SS.register_declaration (TopLevel.SS.ENV.empty IO.DV.dvalue)
                                      mainproto).
Proof.
  
  unfold TopLevel.SS.register_functions.
  simpl.
  split.
  + rewrite bindM_Ret.
    unfold TopLevel.SS.register_declaration.
    simpl.
    auto.

  +  rewrite Trace.matchM. simpl.  auto.
Qed.
  
  

Lemma program_program'_build_global_environment_eq:
   TopLevel.SS.build_global_environment program ≡
                                        TopLevel.SS.build_global_environment program'.
Proof.
  unfold TopLevel.SS.build_global_environment.
  simpl.

  unfold TopLevel.SS.allocate_globals.
  simpl.
  
  repeat (rewrite bindM_Ret).

  destruct program_program'_register_fn_eq as [FN_EQ FN_VAL].

  unfold TopLevel.SS.initialize_globals. simpl.
  euttnorm.
Qed.


Lemma build_global_env_program_value:
  TopLevel.SS.build_global_environment program ≡ Ret (TopLevel.SS.ENV.empty dvalue).
Proof.
  unfold TopLevel.SS.build_global_environment.
  simpl.
  unfold TopLevel.SS.allocate_globals.
  simpl.
  rewrite bindM_Ret.

  
  unfold TopLevel.SS.register_functions.
  simpl.

  assert ((bindM (Ret (TopLevel.SS.ENV.empty dvalue))
       (fun y : TopLevel.SS.genv =>
          TopLevel.SS.register_declaration y mainproto)) ≡
                                                         (fun y => TopLevel.SS.register_declaration y mainproto) (TopLevel.SS.ENV.empty dvalue)).
  rewrite bindM_Ret.
  auto.
Abort.

Lemma eval_typ_i32: forall (CFG:mcfg), SS.eval_typ (CFG )i32ty = DTYPE_I 32.
Proof.
  intros.
  unfold SS.eval_typ.
  rewrite normalize_type_equation.
  auto.
Qed.


Lemma eval_typ_i8: forall (CFG: mcfg), SS.eval_typ (CFG) i8ty = DTYPE_I 8.
Proof.
  intros.
  unfold SS.eval_typ.
  rewrite normalize_type_equation.
  auto.
Qed.

Lemma eval_typ_array_i32: forall (CFG: mcfg),
    (SS.eval_typ CFG (TYPE_Array 2 i32ty)) =
    DTYPE_Array 2 (DTYPE_I 32).
Proof.
  intros.
  unfold SS.eval_typ.
  repeat (rewrite normalize_type_equation; simpl).
  auto.
Qed.

Hint Resolve eval_typ_i32 : euttnormdb.
Hint Resolve eval_typ_i8 : euttnormdb.
Hint Resolve eval_typ_array_i32 : euttnormdb.
Hint Rewrite eval_typ_i32 : euttnormdb.
Hint Rewrite eval_typ_i8 : euttnormdb.
Hint Rewrite eval_typ_array_i32 : euttnormdb.

Hint Transparent SS.init_state.
Hint Unfold SS.init_state.



(** ALL HELL BREAKS LOOSE OTHERWISE **)
Opaque M.add_all_index.
Opaque M.lookup_all_index.
         
(** Show what the original program produces **)
Open Scope list_scope.
Theorem original_program_execution:
   M.memD M.empty
    (bindM (TopLevel.SS.init_state program "main")
       (fun s : TopLevel.SS.state =>
          TopLevel.SS.step_sem program (TopLevel.SS.Step s))) ≡
    Ret (DVALUE_I32  (Int32.repr 1%Z)).
Proof.
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

    rewrite @Trace.matchM with (i := bindM _ _).
    simpl.
    euttnorm.
    repeat (rewrite <- tauN_eutt_1).
    simpl.
    (* TODO: Why does the tactic rewrite not work?! WTF *)
    (* rewrite force_memD_ret. *)
    SS.forcestepsem.
    simpl.
    rewrite @Trace.matchM with (i := M.memD _ _).
    simpl.
    unfold xty.
    simpl.
    replace (Int32.unsigned (Int32.repr 0)) with 0.
    replace (Int32.unsigned (Int32.repr 1)) with 1.
    simpl.
    rewrite (M.lookup_all_index_of_add_all_index_no_alias).
    rewrite (M.lookup_all_index_of_add_all_index_full_alias).
    unfold M.sbyte_list_to_Z.
    simpl.
    simpl.
    simpl.
    auto.
    auto.
    simpl.
    omega.
    rewrite Int.unsigned_repr; try omega; auto.
    unfold Int.max_unsigned.
    unfold Int.modulus.
    simpl.
    omega.
    rewrite Int.unsigned_repr; try omega; auto.
    unfold Int.max_unsigned.
    unfold Int.modulus.
    simpl.
    omega.
Qed.

    
Close Scope list_scope.



Theorem new_program_execution:
   M.memD M.empty
    (bindM (TopLevel.SS.init_state program' "main")
       (fun s : TopLevel.SS.state =>
          TopLevel.SS.step_sem program' (TopLevel.SS.Step s))) ≡
    Ret (DVALUE_I32 (Int32.repr 1%Z)).
Proof.
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
  forcetrace.
  euttnorm.
  unfold SS.initialize_globals.

    repeat (  euttnorm ||
        M.forcememd ||
        SS.forcestepsem ||
        unfold SS.cont;simpl).

    rewrite @Trace.matchM with (i := bindM _ _).
    simpl.
    euttnorm.
    repeat (rewrite <- tauN_eutt_1).
    simpl.
    (* TODO: Why does the tactic rewrite not work?! WTF *)
    (* rewrite force_memD_ret. *)
    SS.forcestepsem.
    simpl.
    rewrite @Trace.matchM with (i := M.memD _ _).
    simpl.
    unfold xty.
    simpl.
    replace (Int32.unsigned (Int32.repr 0)) with 0; auto.
    replace (Int32.unsigned (Int32.repr 1)) with 1; auto.
    simpl.
    rewrite M.lookup_all_index_of_add_all_index_full_alias; auto.
    
Qed.

(** State what we want to prove **)
Definition program_program'_have_same_semantics:
    run_mcfg_with_memory program ≡ run_mcfg_with_memory program'.
Proof.
  unfold run_mcfg_with_memory.
  rewrite original_program_execution.
  rewrite new_program_execution.
  reflexivity.
Qed.
      
