(* Infrastructure for writing passes and lemmas about passes *)
Require Import ZArith List String Omega.
Require Import Program.
Require Import  Vellvm.Classes Vellvm.Util.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.CFG.
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
Require Import Vellvm.Trace.
Require Import Setoid Morphisms.
Require Import Coq.Setoids.Setoid.
Require Import SetoidClass.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Equivalence.
Require FunctionalExtensionality.
Require Import Vellvm.Memory.

Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

Set Implicit Arguments.
Set Contextual Implicit.



(* We can create fancy typeclass based machinery to lift passes to
their correct embedding, similar to the way in which effect handlers
get resolved (At least, I think this is possible), but let's not, for now *)
(** Fancy typeclass machinery **)

(** a pass P is anything that can act on Unit **)
Definition Pass (U: Type) := U -> U.

Notation InstrPass := (Pass instr).
Notation CodePass := (Pass code).
Notation BlockPass := (Pass block).
Notation CFGPass := (Pass cfg).
Notation DefinitionCFGPass := (Pass (definition cfg)).
Notation MCFGPass := (Pass mcfg).
(** Define a functorial structure that can transform a small transformation into a
    larger one **)
Class MonoFunctor (Out: Type) (In: Type) : Type :=
  {
    monomap: (In -> In) -> (Out -> Out);
    (** Note that on having functional extensionality,
     we have equality at the function level **)
    monomap_functorial: forall f g i, (monomap f ∘ monomap g) i = monomap (f ∘ g) i;
                           
  }.


Instance instrToIdInstrFunctor: MonoFunctor (instr_id * instr) instr :=
  {
    monomap (p: instr -> instr) (iid: instr_id * instr) := (fst iid, p (snd iid));
  }.
Proof.
  intros.
  auto.
Defined.

Check (instrToIdInstrFunctor).


Instance instrToBlockFunctor: MonoFunctor block instr :=
  {
    monomap (pass: instr -> instr) (b: block) :=
      mk_block (blk_id b)
               (blk_phis b)
               (List.map (monomap pass) (blk_code b))
               (blk_term b);
  }.
Proof.
  intros.
  
  Opaque monomap.
  simpl.
  destruct i; simpl.
  assert (MAP_EQ: map (monomap f) (map (monomap g) blk_code) =
          map (monomap (f ∘ g)) blk_code).
  induction blk_code; auto.
  repeat rewrite map_cons.
  
  replace (monomap (f ∘ g) a) with ((monomap f ∘ monomap g) a ).
  simpl.
  rewrite IHblk_code.
  reflexivity.
  apply monomap_functorial.

  rewrite MAP_EQ.
  reflexivity.
  Transparent monomap.
Defined.

Lemma map_map': forall {A B C: Type} (f: B -> C) (g: A -> B) (x: list A),
    map f ((map g) x) = map (f ∘ g) x.
Proof.
  intros until x.
  induction x; auto.
  repeat rewrite map_cons.
  rewrite IHx.
  simpl.
  reflexivity.
Defined.
Hint Resolve map_map'.

Instance blockToCFGFunctor : MonoFunctor cfg block :=
  {
    monomap (pass: block -> block) (c: cfg) :=
    {|
      init := init c;
      blks := map pass (blks c);
      args := args c;
    |}

  }.
Proof.
  intros.
  simpl.
  rewrite map_map'.
  reflexivity.
Defined.


Instance CFGToDefinitionCFGFunctor:
  MonoFunctor (definition cfg) cfg :=
  {
    monomap (pass: cfg -> cfg) (defn: definition cfg) :=
      
     mk_definition cfg
                   (df_prototype defn) 
                   (df_args defn)
                   (pass (df_instrs defn));

  }.
Proof.
  intros.
  simpl.
  constructor.
Defined.


Instance DefinitionCFGPassToMCFGFunctor:
  MonoFunctor  mcfg  (definition cfg) :=
  {
    monomap (pass: definition cfg -> definition cfg) (m: mcfg) :=
      {| m_name := m_name m;
         m_target:= m_target m;
         m_datalayout := m_datalayout m;
         m_type_defs := m_type_defs m;
         m_globals := m_globals m;
         m_declarations := m_declarations m;
         m_definitions := map pass (m_definitions m);
      |};
  }.
Proof.
  intros.
  simpl.
  rewrite map_map'; auto.
Defined.



(** NOTE: I needed funext **)
Instance monofunctor_chain (A: Type) (B: Type) (C: Type) `{MonoFunctor B A} `{MonoFunctor C B}:
  MonoFunctor C A :=
  {
    monomap (pass: A -> A) (c: C) := monomap (monomap pass) c;
  }.
Proof.
  intros.
  simpl.
  Check (monomap_functorial).
  assert (MONO_EQ: monomap (f ∘ g) = (monomap f ∘ monomap g)).
  extensionality x.
  rewrite monomap_functorial.
  reflexivity.
  rewrite MONO_EQ.
  
  rewrite <- monomap_functorial with (f0 := monomap f) (g0 := monomap g) (i0 := i).
  simpl.
  auto.
Defined.
  

Definition f_instr (i: instr): instr := id i.
Check (f_instr).

(** NICE! I can automatically lift instances using monomap **)
Definition map_f_instr_on_block (b: block): block :=  monomap (f_instr) b.
(** This just hangs because of from the looks of it, instance resolution **)

Definition map_f_instr_on_cfg (c: cfg): cfg :=
  monomap (f_instr) c.

Definition map_f_instr_on_definion_cfg (d: definition cfg):
  definition cfg :=  monomap (f_instr) d.

Definition map_f_instr_on_mcfg (m: mcfg): mcfg :=  monomap (f_instr) m.



Open Scope Z_scope.
Open Scope string_scope.


Module PASSTHEOREMS (A:MemoryAddress.ADDRESS) (LLVMIO:LLVM_INTERACTIONS(A)).
  (* Need this to simplify proofs, otherwise I need to painfully destruct
  execution chains. *)
Import FunctionalExtensionality.


Module SST := StepSemanticsTiered A LLVMIO.
Import SST.
Import LLVMIO.

(* Since
1. Trace X := M IO X
2. M is a free monad-style construction
3. IO is a functor,

M should lift the IO instance of function into a monad instance of (M IO).

However, Coq typeclass syntax is.. difficult to someone who's never used it,
so I'm going to Admit the monad laws for Trace (which will hold, asuming the M construction
is correct)
 *)

Lemma bindM_Ret: forall (A B: Type) (a: A) (f: A -> Trace B),
    bindM (Ret a) f ≡  f a.
Proof.
Admitted.

Check (@bindM).
Check (@mbind).

(* Clearly, I'm able to use monads in the abstract. I'm just not able to convince coq that
Trace is actually a Monad, even though
 Definition Trace X := M IO X. 
*)
Example bind_of_ret: 
  (mbind (F := M IO)) (mret (DVALUE_I64 (Int64.repr 2)))  (fun v => mret v)  ≡  mret (DVALUE_I64 (Int64.repr 2)).
Proof.
  apply mret_mbind.
Qed.

Hint Resolve bind_of_ret.
Hint Rewrite -> bind_of_ret.

Lemma  eval_type_I64: forall (tds: typedefs),
    eval_typ tds (TYPE_I 64) = DTYPE_I 64.
Proof.
  intros.
  unfold eval_typ.
  rewrite normalize_type_equation.
  auto.
Qed.


Hint Resolve eval_type_I64.

(* 
Class PreservesType (P: Type) (MCFP: MCFGPass P) {
        preserves_type: forall (CFG: mcfg), m_type_defs (runPass P CFG) = m_type_defs CFG;
      }.
*)

Definition preserves_types (p: MCFGPass): Prop :=
  forall (CFG: mcfg), m_type_defs (p CFG) = m_type_defs CFG.

Definition preserves_eval_typ (p: MCFGPass) (t: typ): Prop :=
  forall (CFG: mcfg), eval_typ (m_type_defs (p CFG)) t = eval_typ (m_type_defs CFG) t.

Create HintDb passes.


Lemma preserves_types_implies_preserves_eval_typ:
  forall (p: MCFGPass) (CFG: mcfg) (t: typ),
    preserves_types p ->
    preserves_eval_typ p t.
Proof.
  intros.
  repeat (unfold eval_typ).
  repeat (unfold preserves_eval_typ).

  unfold preserves_types in H.
  intros.
  rewrite H.
  repeat (rewrite normalize_type_equation).
  destruct t; auto.
Qed.

Hint Resolve preserves_types_implies_preserves_eval_typ : passes.


Definition preserves_ident_definition (p: DefinitionCFGPass) : Prop :=
  forall (fn: definition cfg), ident_of (p fn) = ident_of fn.

Hint Unfold preserves_ident_definition: pass.
                                         

(** TODO: Phrase `monomap` in terms of lifting `Pass`, not just lifting
functions of the form A -> A **)
Lemma lifted_cfg_pass_preserves_ident_definition:
   forall (p: CFGPass), preserves_ident_definition (monomap p).
Proof.
  unfold monomap.
  unfold CFGToDefinitionCFGFunctor.
  simpl.
  
  unfold preserves_ident_definition.
  reflexivity.
Qed.

Hint Resolve lifted_cfg_pass_preserves_ident_definition.

Lemma preserves_ident_definition_commutes_with_find_defn:
  forall (fnid: function_id)
    (g: DefinitionCFGPass),
    preserves_ident_definition g ->
    agress_on_filter (find_defn fnid) g.
Proof.
  intros until g.
  intros PRESERVES_IDENT.
  
  unfold agress_on_filter.
  intros.
  split.

  - intros.
    unfold find_defn in *.
    destruct (ident_of a == ID_Global fnid); try discriminate.
    inversion H. subst.
    exists (g b).

    assert (IDENT_PRESERVED: ident_of (g b) = ID_Global fnid).
    unfold preserves_ident_definition in PRESERVES_IDENT.
    specialize (PRESERVES_IDENT b).
    rewrite PRESERVES_IDENT.
    rewrite e.
    auto.


    rewrite IDENT_PRESERVED.
    destruct (ID_Global fnid == ID_Global fnid); auto; congruence.

  - intros.
    unfold preserves_ident_definition in PRESERVES_IDENT.
    unfold find_defn in *.
    destruct (ident_of a == ID_Global fnid); try discriminate.
    assert (IDENT_GA: ident_of (g a) = ident_of a).
    auto.

    rewrite IDENT_GA.
    destruct (ident_of a == ID_Global fnid); try contradiction; auto.
Qed.
Hint Resolve preserves_ident_definition_commutes_with_find_defn.
   



Lemma find_definition_some:
  forall (CFG: mcfg)
    (fnid: function_id)
    (oldfn: definition cfg)
    (g: DefinitionCFGPass),

  preserves_ident_definition g ->
  find_function CFG fnid = Some oldfn ->
  find_map (find_defn fnid) (map g (m_definitions CFG)) =
  Some (g oldfn).
Proof.
  intros until g.
  intros PRESERVES_IDENT FINDOLD.
  assert (FIND_ON_MAP: exists old_old_fn, Some oldfn = (find_defn fnid old_old_fn) /\
                        find_map (find_defn fnid) (map g (m_definitions CFG)) = (find_defn fnid (g old_old_fn))).
  apply find_map_mapped_some_1; try assumption.
  auto.

  destruct FIND_ON_MAP as [OLD_OLD_FN [OLD_FN_AS_OLD_OLD_FN FIND_WITNESS]].
  unfold find_defn in OLD_FN_AS_OLD_OLD_FN.
  destruct (ident_of OLD_OLD_FN == ID_Global fnid); try discriminate.
  inversion OLD_FN_AS_OLD_OLD_FN.
  subst.

  rewrite FIND_WITNESS.
  unfold find_defn.

  assert (ID_G_OLD_OLD_FN: ident_of (g OLD_OLD_FN) = ID_Global fnid).
  unfold preserves_ident_definition in PRESERVES_IDENT.
  rewrite <- e.
  apply PRESERVES_IDENT.

  rewrite ID_G_OLD_OLD_FN.
  destruct (ID_Global fnid == ID_Global fnid); auto; try congruence.
Qed.
Hint Resolve find_definition_some.

Lemma find_function_some: forall
    (CFG: mcfg)
    (fnid: function_id)
    (oldfn: definition cfg)
    (g: DefinitionCFGPass)
    (PRESERVES_DEFN_IDENT: preserves_ident_definition g),
    find_function CFG fnid = Some oldfn ->
    find_function ((monomap g) CFG) fnid = Some (g oldfn).
Proof.
  intros.
  unfold monomap.
  unfold DefinitionCFGPassToMCFGFunctor.
  unfold find_function in *.
  simpl.
  apply find_definition_some; auto.
Qed.
Hint Resolve find_function_some.

Lemma find_function_none:
  forall (CFG: mcfg)
    (fnid: function_id)
    (g: DefinitionCFGPass)
    (PRESERVES_DEFN_IDENT: preserves_ident_definition g), 
    find_function CFG fnid = None ->
    find_function ((monomap g) CFG) fnid = None.
Proof.
  intros.
  unfold find_function in *.
  simpl.
  apply find_map_mapped_none;
  auto.
Qed.

Hint Resolve  (find_function_none).

Lemma find_function_lifted_definition_pass:
  forall (CFG: mcfg)
    (fnid: function_id)
    (g: DefinitionCFGPass)
    (PRESERVES_DEFN_IDENT: preserves_ident_definition g),
    find_function  ((monomap g) CFG) fnid =
    option_map g (find_function CFG fnid).
Proof.
  intros.
  Opaque monomap.
  simpl.
  remember (find_function CFG fnid) as FIND_F.
  destruct FIND_F; simpl; auto.
  Transparent monomap.
Qed.
                                                        
Hint Resolve(find_function_lifted_definition_pass).
Hint Rewrite(find_function_lifted_definition_pass).


Definition preserves_ident_block (g: BlockPass) : Prop :=
  forall (b: block), blk_id (g b) = blk_id b.
Hint Unfold preserves_ident_block.


Lemma find_block: forall blks blkid (g: BlockPass) ,
    preserves_ident_block g ->
    find_block (map g blks) blkid = option_map  g (find_block blks blkid).
Proof.
  intros until g.
  intros PRESERVES_IDENT.

  induction blks.
  - auto.
  - simpl.
    remember (blk_id a == blkid) as COND.

    destruct COND.

    + assert (BLKID_GA: blk_id (g a ) = blkid).
      unfold preserves_ident_block in PRESERVES_IDENT.
      rewrite <- e.
      apply PRESERVES_IDENT.

      destruct (blk_id (g a) == blkid); try contradiction; auto.

    + assert (BLKID_GA: blk_id (g a ) <> blkid).
      assert (BLK_ID_DEC: {blk_id (g a) = blkid} + {blk_id (g a) <> blkid}); auto.
      destruct BLK_ID_DEC; subst; try contradiction; auto.

      destruct (blk_id (g a) == blkid); subst; try contradiction.
      apply IHblks.
Qed.

Hint Resolve find_block.

  
(* If the pass preserves the terminator *)
Definition preserves_block_terminator  (g: BlockPass): Prop :=
  forall  (b: block), blk_term (g b) = blk_term b.


Hint Unfold preserves_block_terminator.


Lemma lifted_instr_pass_to_block_pass_preserves_block_terminator:
  forall (pass: InstrPass),
    preserves_block_terminator (monomap pass).
Proof.
  unfold preserves_block_terminator.
  intros.
  auto.
Qed.
Hint Resolve (lifted_instr_pass_to_block_pass_preserves_block_terminator).

  

Lemma rewrite_block_to_cmd_on_fetch_term: forall (g: block -> block) (b: block) pt,
    blk_term_id b = pt -> 
    preserves_block_terminator g ->
    block_to_cmd (g b) pt = block_to_cmd b pt.
Proof.
  intros until  pt.
  intros ACCESSING_TERMINATOR PRESERVES_TERMINATOR.
  unfold preserves_block_terminator in PRESERVES_TERMINATOR.
  
  unfold block_to_cmd.
  unfold blk_term_id.
  rewrite PRESERVES_TERMINATOR.
  subst.
  unfold blk_term_id.

  destruct (fst (blk_term b) == fst (blk_term b)); try contradiction.
  auto.
Qed.


Hint Resolve (rewrite_block_to_cmd_on_fetch_term).

Lemma rewrite_block_to_cmd_on_fetch_instr: forall (g: block -> block) (b: block) pt,
    blk_term_id b <> pt -> 
    preserves_block_terminator g ->
    block_to_cmd (g b) pt = find_instr (blk_code (g b)) pt (fst (blk_term b)).
Proof.
  intros until  pt.
  intros NOT_ACCESSING_TERMINATOR PRESERVES_TERMINATOR.
  unfold preserves_block_terminator in PRESERVES_TERMINATOR.
  
  unfold block_to_cmd.
  unfold blk_term_id in *.
  rewrite PRESERVES_TERMINATOR.


  destruct (fst (blk_term b) == pt); try contradiction.
  auto.
Qed.
    
Hint Resolve (rewrite_block_to_cmd_on_fetch_instr).

  
(* 
Lemma eq_jump: forall CFG fn  bk br g e s pass,
    preserves_types pass ->
    preserves_block_entry pass ->
    jump (pass CFG) fn bk br g e s =
    jump (CFG) fn bk br g e s.
Proof.
  intros until pass.
  intros PRESRVES_TYPES.
  intros PRESERVES_ENTRY.
  unfold jump.

  assert (EQ_EVAL_TYP: eval_typ (pass CFG) = eval_typ CFG).
  unfold eval_typ.
  extensionality typ.
  apply preserves_types_implies_preserves_eval_typ; auto.
  repeat (rewrite EQ_EVAL_TYP).

  assert(EQ_EVAL_EXPR: eval_exp (pass CFG) = eval_exp (CFG)).
  extensionality g_ext.
  extensionality e_ext.
  extensionality typ_ext.
  extensionality expr_ext.
  auto.

  repeat(rewrite EQ_EVAL_EXPR).
  
  repeat (rewrite PRESERVES_ENTRY).
  reflexivity.
Qed.
*)

(* Helper function to run an InstrPass on the result of a find_instr. This
is super kludgy.

1. VE-LLVM's stuff is somewhat annoying to use, regarding the whole `cmd`.
2. Coq could really use lenses :)
*)
Definition runInstrPassOnFindInstr
           (pass: InstrPass)
           (optin: option (cmd * option instr_id)) :
  option (cmd * option instr_id) :=
  let go (inp: cmd * option instr_id) :=
      match inp with
      | (Inst i, id) => (Inst (pass i), id)
      | _ => inp
      end
  in option_map go optin.

(* Characterise how find_instr behaves when we have an instruction pass.
Since an instruction pass is not allowed to touch instruction IDs
(this is the job of a `code` pass), intuitively, what we have is
that we can find the instruction and then run the pass.

This is slightly complicated by the fact that `find_instr` is used
to find both instructions and terminators.

Currently, our instruction pass does not allow modification of
terminators. TODO, I guess...
*)
Lemma findOverInstrPassLiftedToIdInstrPass:
  forall (pass: InstrPass)
    (c: code)
    (p: instr_id)
    (termid: instr_id),
    find_instr (map (monomap pass) c) p termid =
    runInstrPassOnFindInstr pass (find_instr c p termid).
Proof.
  intros until c.
  induction c; intros; unfold find_instr;
    simpl; auto.

  destruct a; simpl.
  destruct (p == i); simpl.
  (* 
  - unfold liftInstrPassToIdInstrPass. unfold fallthrough.
    destruct c; auto.

  - fold find_instr. apply IHc.
   *)
Admitted.

Hint Resolve findOverInstrPassLiftedToIdInstrPass.

Lemma InstrPassPreservesBlockToCmd: forall (pass: InstrPass)
                                      (b: block)
                                      pt,
    block_to_cmd ((monomap pass) b) pt  =
    runInstrPassOnFindInstr pass (block_to_cmd b pt).
Proof.
  intros.
  unfold block_to_cmd.
  simpl.

  assert (PRESERVES_TERM: blk_term ((monomap pass) b) =
                          blk_term b).
  auto.

  unfold blk_term_id.
  (* 
  rewrite PRESERVES_TERM.

  destruct (fst (blk_term b) == pt); auto.
Qed.
   *)
Admitted.
  

Definition preserves_function_entry (pass: MCFGPass): Prop :=
  forall (MCFG: mcfg) (fnid: function_id),
    find_function_entry (pass MCFG) fnid = find_function_entry MCFG fnid.

(* We need a  lifted instruction pass because the function entry
is defined in terms of the entry of the first basic block. This is
defined in terms of the ID OF THE FIRST INSTRUCTION.
*)
Lemma  lifted_instr_pass_preserves_function_entry:
  forall (pass: InstrPass),
    preserves_function_entry (monomap pass).
Proof.
  unfold preserves_function_entry.
  intros.
  unfold find_function_entry.
  simpl.
  (*
  rewrite find_function_lifted_definition_pass; auto.
  destruct (find_function MCFG fnid); auto.

  simpl.
  rewrite find_block; auto.
  destruct (CFG.find_block (blks (df_instrs d)) (init (df_instrs d))); auto.
  simpl.

  unfold blk_entry_id.
  simpl.

  destruct (blk_code b); simpl; auto.
Qed.
   *)
Admitted.

End PASSTHEOREMS.


Require Import Vellvm.TopLevel.
(* 
Module IO := LLVMIO.Make(Memory.A).
Module M := Memory.Make(IO).
Module SST := StepSemanticsTiered(Memory.A)(IO).


Import SST.
Import Vellvm.Trace.MonadVerif.
*)
Import SST.
Import Trace.MonadVerif.

Check (SST.eval_exp).
Ltac unfolder_for_exp := unfold SST.eval_exp,
                         IO.lift_err_d,
                         lookup_id,
                         raise,
                         mret,
                         IO.exn_trace.

Ltac destruct_finite_trace_match :=
  try unfolder_for_exp; try constructor;
  match goal with
  | [ |- TraceFinite (match ?X with _ => _ end) ] =>
    destruct X;
    try unfolder_for_exp;
    first [constructor | destruct_finite_trace_match]
  end.

Fixpoint eval_exp_has_finite_trace
  (tds: typedefs)
    (ge: genv)
    (e: env)
    (odtyp: option dtyp)
    (ex: exp):
    Trace.TraceFinite(SST.eval_exp tds ge e odtyp ex).
Proof.
  induction ex; try destruct_finite_trace_match.
Admitted.



(** *Instruction to Basic block preservation *)

Lemma preserve_inst_trace_implies_preserve_bb_mem_effect:
  forall (ip: InstrPass)
    (PRESERVE_INST_TRACE: forall (tds: typedefs)(ge: genv) (e: env)
                 (i: instr) (id: instr_id),
                 execInst tds ge e id i = execInst tds ge e id (ip i))
    (ge: genv)
    (tds: typedefs)
    (e: env)
    (bb1 bb2: block)
    (BBMODIFIED: bb2 = monomap ip bb1)
    (pt: instr_pt)
    (minit: M.memory),
    M.memD minit (execBBInstrs tds ge e (blk_id bb1) (blk_code bb1) (snd (blk_term bb1))  pt) ≡
    M.memD minit (execBBInstrs tds ge e (blk_id bb2) (blk_code bb2) (snd (blk_term bb2)) pt).
Proof.
  intros.
  unfold monomap in BBMODIFIED.
  unfold instrToBlockFunctor in BBMODIFIED.
  
  
  destruct bb1; simpl in *.
  generalize dependent blk_id.
  generalize dependent blk_phis.
  generalize dependent bb2.
  generalize dependent ge.
  generalize dependent e.
  generalize dependent minit.
  generalize dependent pt.
  induction blk_code.
  
  - intros.
    simpl in BBMODIFIED.
    destruct bb2.
    inversion BBMODIFIED.
    simpl.
    reflexivity.
    
  - intros.
    simpl.
    destruct bb2.
    simpl in *.

    destruct a as [NAME  INST].
    simpl in *.
    inversion BBMODIFIED.
    simpl in *.
    repeat rewrite M.memD_commutes_with_bind_memEffect.

    assert (MEM_EFFECT_SAME: M.memEffect minit (execInst tds ge e NAME INST) =
                             M.memEffect minit (execInst tds ge e NAME (ip INST))).
    rewrite PRESERVE_INST_TRACE.
    reflexivity.

    rewrite MEM_EFFECT_SAME.
    clear MEM_EFFECT_SAME.
    clear H0 H1 H2 H3.


    assert (MEMD_INNER_EQ: forall m' x,
           M.memD m'
       (bindM (Ret x)
          (fun iresult : InstResult =>
           match iresult with
           | IRCall fnid args retinstid _ => Ret (BBRCall fnid args retinstid pt blk_id)
           | IRCallVoid fnid args _ => Ret (BBRCallVoid fnid args pt blk_id)
           | IREnvEffect _ => execBBInstrs tds ge e blk_id blk_code (snd blk_term) (pt + 1)%nat
           | IRNone => execBBInstrs tds ge e blk_id blk_code (snd blk_term) (pt + 1)%nat
           end)) ≡
           M.memD m'
         (bindM (Ret x)
            (fun iresult : InstResult =>
             match iresult with
             | IRCall fnid args retinstid _ => Ret (BBRCall fnid args retinstid pt blk_id)
             | IRCallVoid fnid args _ => Ret (BBRCallVoid fnid args pt blk_id)
             | IREnvEffect _ =>
                 execBBInstrs tds ge e blk_id
                   (map (fun iid : instr_id * instr => (fst iid, ip (snd iid))) blk_code)
                   (snd blk_term) (pt + 1)%nat
             | IRNone =>
                 execBBInstrs tds ge e blk_id
                   (map (fun iid : instr_id * instr => (fst iid, ip (snd iid))) blk_code)
                   (snd blk_term) (pt + 1)%nat
             end))).
    intros.
    euttnorm.
    destruct x; euttnorm.
    
    rewrite IHblk_code with (pt := (pt + 1)%nat) (minit := m') (e :=e) (ge := ge) (bb2 :={|
               blk_id := blk_id;
               blk_phis := blk_phis;
               blk_code := (map (fun iid : instr_id * instr => (fst iid, ip (snd iid))) blk_code);
               blk_term := blk_term |}) (blk_phis := blk_phis) (blk_id0 := blk_id); reflexivity.
    rewrite IHblk_code with (pt := (pt + 1)%nat) (minit := m') (e :=e) (ge := ge) (bb2 :={|
               blk_id := blk_id;
               blk_phis := blk_phis;
               blk_code := (map (fun iid : instr_id * instr => (fst iid, ip (snd iid))) blk_code);
               blk_term := blk_term |}) (blk_phis := blk_phis) (blk_id0 := blk_id); reflexivity.


    assert (OUTER_EQ: Trace.MonadVerif.PointwiseEUTT
              (fun out : M.memory * InstResult =>
     let (m', x) := out in
     M.memD m'
       (bindM (Ret x)
          (fun iresult : InstResult =>
           match iresult with
           | IRCall fnid args retinstid _ => Ret (BBRCall fnid args retinstid pt blk_id)
           | IRCallVoid fnid args _ => Ret (BBRCallVoid fnid args pt blk_id)
           | IREnvEffect _ => execBBInstrs tds ge e blk_id blk_code (snd blk_term) (pt + 1)%nat
           | IRNone => execBBInstrs tds ge e blk_id blk_code (snd blk_term) (pt + 1)%nat
           end))) (fun out : M.memory * InstResult =>
       let (m', x) := out in
       M.memD m'
         (bindM (Ret x)
            (fun iresult : InstResult =>
             match iresult with
             | IRCall fnid args retinstid _ => Ret (BBRCall fnid args retinstid pt blk_id)
             | IRCallVoid fnid args _ => Ret (BBRCallVoid fnid args pt blk_id)
             | IREnvEffect _ =>
                 execBBInstrs tds ge e blk_id
                   (map (fun iid : instr_id * instr => (fst iid, ip (snd iid))) blk_code)
                   (snd blk_term) (pt + 1)%nat
             | IRNone =>
                 execBBInstrs tds ge e blk_id
                   (map (fun iid : instr_id * instr => (fst iid, ip (snd iid))) blk_code)
                   (snd blk_term) (pt + 1)%nat
             end)))) .
    unfold PointwiseEUTT.
    intros.
    destruct x.
    rewrite MEMD_INNER_EQ.
    reflexivity.

    setoid_rewrite OUTER_EQ.
    reflexivity.
Qed.



Lemma preserve_inst_effect_implies_preserve_bb_mem_effect:
  forall (ip: InstrPass)
    (PRESERVE_INST_EFFECT: forall (tds: typedefs)(ge: genv) (e: env)
                            (i: instr) (id: instr_id) (m: M.memory),
        M.memEffect m (execInst tds ge e id i) ≡
        M.memEffect m (execInst tds ge e id (ip i)))
    (ge: genv)
    (tds: typedefs)
    (e: env)
    (bb1 bb2: block)
    (BBMODIFIED: bb2 = monomap ip bb1)
    (pt: instr_pt)
    (minit: M.memory),
    M.memD minit (execBBInstrs tds ge e (blk_id bb1) (blk_code bb1) (snd (blk_term bb1))  pt) ≡
    M.memD minit (execBBInstrs tds ge e (blk_id bb2) (blk_code bb2) (snd (blk_term bb2)) pt).
Proof.
  intros.
  unfold monomap in BBMODIFIED.
  unfold instrToBlockFunctor in BBMODIFIED.
  
  
  destruct bb1; simpl in *.
  generalize dependent blk_id.
  generalize dependent blk_phis.
  generalize dependent bb2.
  generalize dependent ge.
  generalize dependent e.
  generalize dependent minit.
  generalize dependent pt.
  induction blk_code.
  
  - intros.
    simpl in BBMODIFIED.
    destruct bb2.
    inversion BBMODIFIED.
    simpl.
    reflexivity.
    
  - intros.
    simpl.
    destruct bb2.
    simpl in *.

    destruct a as [NAME  INST].
    simpl in *.
    inversion BBMODIFIED.
    simpl in *.
    repeat rewrite M.memD_commutes_with_bind_memEffect.

    assert (MEM_EFFECT_SAME: M.memEffect minit (execInst tds ge e NAME INST) ≡
                             M.memEffect minit (execInst tds ge e NAME (ip INST))).
    rewrite PRESERVE_INST_EFFECT.
    reflexivity.

    rewrite MEM_EFFECT_SAME.
    clear MEM_EFFECT_SAME.
    clear H0 H1 H2 H3.


    assert (MEMD_INNER_EQ: forall m' x,
           M.memD m'
       (bindM (Ret x)
          (fun iresult : InstResult =>
           match iresult with
           | IRCall fnid args retinstid _ => Ret (BBRCall fnid args retinstid pt blk_id)
           | IRCallVoid fnid args _ => Ret (BBRCallVoid fnid args pt blk_id)
           | IREnvEffect _ => execBBInstrs tds ge e blk_id blk_code (snd blk_term) (pt + 1)%nat
           | IRNone => execBBInstrs tds ge e blk_id blk_code (snd blk_term) (pt + 1)%nat
           end)) ≡
           M.memD m'
         (bindM (Ret x)
            (fun iresult : InstResult =>
             match iresult with
             | IRCall fnid args retinstid _ => Ret (BBRCall fnid args retinstid pt blk_id)
             | IRCallVoid fnid args _ => Ret (BBRCallVoid fnid args pt blk_id)
             | IREnvEffect _ =>
                 execBBInstrs tds ge e blk_id
                   (map (fun iid : instr_id * instr => (fst iid, ip (snd iid))) blk_code)
                   (snd blk_term) (pt + 1)%nat
             | IRNone =>
                 execBBInstrs tds ge e blk_id
                   (map (fun iid : instr_id * instr => (fst iid, ip (snd iid))) blk_code)
                   (snd blk_term) (pt + 1)%nat
             end))).
    intros.
    euttnorm.
    destruct x; euttnorm.
    
    rewrite IHblk_code with (pt := (pt + 1)%nat) (minit := m') (e :=e) (ge := ge) (bb2 :={|
               blk_id := blk_id;
               blk_phis := blk_phis;
               blk_code := (map (fun iid : instr_id * instr => (fst iid, ip (snd iid))) blk_code);
               blk_term := blk_term |}) (blk_phis := blk_phis) (blk_id0 := blk_id); reflexivity.
    rewrite IHblk_code with (pt := (pt + 1)%nat) (minit := m') (e :=e) (ge := ge) (bb2 :={|
               blk_id := blk_id;
               blk_phis := blk_phis;
               blk_code := (map (fun iid : instr_id * instr => (fst iid, ip (snd iid))) blk_code);
               blk_term := blk_term |}) (blk_phis := blk_phis) (blk_id0 := blk_id); reflexivity.


    assert (OUTER_EQ: Trace.MonadVerif.PointwiseEUTT
              (fun out : M.memory * InstResult =>
     let (m', x) := out in
     M.memD m'
       (bindM (Ret x)
          (fun iresult : InstResult =>
           match iresult with
           | IRCall fnid args retinstid _ => Ret (BBRCall fnid args retinstid pt blk_id)
           | IRCallVoid fnid args _ => Ret (BBRCallVoid fnid args pt blk_id)
           | IREnvEffect _ => execBBInstrs tds ge e blk_id blk_code (snd blk_term) (pt + 1)%nat
           | IRNone => execBBInstrs tds ge e blk_id blk_code (snd blk_term) (pt + 1)%nat
           end))) (fun out : M.memory * InstResult =>
       let (m', x) := out in
       M.memD m'
         (bindM (Ret x)
            (fun iresult : InstResult =>
             match iresult with
             | IRCall fnid args retinstid _ => Ret (BBRCall fnid args retinstid pt blk_id)
             | IRCallVoid fnid args _ => Ret (BBRCallVoid fnid args pt blk_id)
             | IREnvEffect _ =>
                 execBBInstrs tds ge e blk_id
                   (map (fun iid : instr_id * instr => (fst iid, ip (snd iid))) blk_code)
                   (snd blk_term) (pt + 1)%nat
             | IRNone =>
                 execBBInstrs tds ge e blk_id
                   (map (fun iid : instr_id * instr => (fst iid, ip (snd iid))) blk_code)
                   (snd blk_term) (pt + 1)%nat
             end)))) .
    unfold PointwiseEUTT.
    intros.
    destruct x.
    rewrite MEMD_INNER_EQ.
    reflexivity.

    setoid_rewrite OUTER_EQ.
    reflexivity.
Qed.
(** *CFG (Function) to whole program preservation *)

(** declarations in module returns the same value on a CFG pass **)
Lemma declarations_in_module_after_cfg_pass_eq: forall (MCFG: mcfg) (cfgp: CFGPass),
  (declarations_in_module_tiered (monomap cfgp MCFG)) = 
  (declarations_in_module_tiered MCFG).
Proof.
  intros.
  unfold declarations_in_module_tiered.
  simpl.

  assert (PROTOS_EQ: map df_prototype (m_definitions MCFG) =
                     map df_prototype (m_definitions (monomap cfgp MCFG))).
  destruct MCFG; simpl.
  induction m_definitions; simpl in *; auto.
  rewrite IHm_definitions; auto.
  
  rewrite PROTOS_EQ.
  destruct MCFG; simpl; auto.
Qed.

  

(** init_state returns the same value after cfg pass **)
Lemma init_state_tiered_after_cfg_pass_eq: forall (MCFG: mcfg) (cfgp: CFGPass),
    (init_state_tiered (monomap cfgp MCFG) "main") =
    (init_state_tiered MCFG "main").
Proof.
  intros.
  unfold init_state_tiered.
  rewrite declarations_in_module_after_cfg_pass_eq with (cfgp := cfgp).
  reflexivity.
Qed.

(*

       (fun '(ir, ge) => step_sem_tiered ge (ENV.empty dvalue) [] MCFG ir))
  ≡ M.memD M.empty
      (bindM (init_state_tiered MCFG "main")
         (fun '(ir, ge) => step_sem_tiered ge (ENV.empty dvalue) [] (monomap cfgp MCFG) ir))
*)
Lemma cfg_preservation_implies_step_sem_preservation:
  forall (cfgp: CFGPass)
    (PRESERVE_CFG_EFFECT: forall
             (tds: typedefs)
             (ge: genv)
             (e: env)
             (CFG: cfg)
             (fnid: function_id)
             (m: M.memory),
        M.memEffect m (execFunction tds ge e CFG fnid) ≡
        M.memEffect m (execFunction tds ge e (cfgp CFG) fnid))
    (ge: genv)
    (e: env)
    (s: stack)
    (MCFG: mcfg)
    (r:InterpreterResult)
    (m: M.memory),
    M.memEffect m (step_sem_tiered ge e s MCFG r) ≡
                M.memEffect m (step_sem_tiered ge e s (monomap cfgp MCFG) r).
Proof.
  intros.
Admitted.


Lemma cfg_preservation_implies_program_preservation:
  forall (cfgp: CFGPass)
    (PRESERVE_CFG_EFFECT: forall
             (tds: typedefs)
             (ge: genv)
             (e: env)
             (CFG: cfg)
             (fnid: function_id)
             (m: M.memory),
        M.memEffect m (execFunction tds ge e CFG fnid) ≡
        M.memEffect m (execFunction tds ge e (cfgp CFG) fnid))
    (MCFG: CFG.mcfg),
    TopLevel.run_mcfg_with_memory_tiered MCFG ≡ run_mcfg_with_memory_tiered (monomap cfgp MCFG).
Proof.
  intros.
  unfold run_mcfg_with_memory_tiered.
  rewrite init_state_tiered_after_cfg_pass_eq with (cfgp := cfgp).
  (** TODO: change this to something rewriteable, once I figure out the
      correct Proper instance **)
  apply M.MemD_proper_wrt_PointwiseMemEffectEUTT.

  unfold M.PointwiseMemEffectEUTT.
  intros.
  destruct x.
  apply cfg_preservation_implies_step_sem_preservation; auto.
Qed.





