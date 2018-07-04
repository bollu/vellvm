Require Import Omega.
Require Import Nat.
Require Import ZArith.
Require Import Ring.
Require Import List.
Require Import Ncring.
Require Import Ring_tac.
Require Import FunctionalExtensionality.
Require Import Maps.
Require Import Vellvm.polyir.PolyIRUtil.

(** Import VPL for polyhedral goodness **)
From Vpl Require Import PedraQ DomainInterfaces.
Require Import VplTactic.Tactic.
Add Field Qcfield: Qcft (decidable Qc_eq_bool_correct, constants [vpl_cte]).

Import PedraQ.FullDom.


(* Equalities stuff *)
Require Import EquivDec.
Require Import Equalities.

Locate "=?".

(** Cool, VPLTactic works **)
Example demo1 (A:Type) (f: Qc -> A) (v1: Qc):
  v1 <= 1 -> (f v1) <> (f 1) -> v1 < 1.
Proof.
  vpl_auto.
Qed.


(* 
From mathcomp Require ssreflect ssrbool ssrfun bigop.
Import ssreflect.SsrSyntax.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
 *)

Local Notation "a ## b" := (ZMap.get b a) (at level 1).

(** We will follow the development from this paper:
http://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.43.8188&rep=rep1&type=pdf*)


Open Scope list_scope.
Import ListNotations.


Inductive BinopType :=
| Add : BinopType
| Sub: BinopType.



(* Value that expressions can take *)
Notation Value := Z.


(* Identifiers *)
Definition Ident := Z.

(** Syntax of PolyIR **)
Definition Indvar := Z.
Inductive AffineExpr :=
| Aindvar:  Indvar -> AffineExpr
| Abinop: BinopType -> AffineExpr -> AffineExpr -> AffineExpr
| Amul: Z -> AffineExpr -> AffineExpr
| Aconst: Z -> AffineExpr
.
Inductive PolyExpr :=
| Eaffine: AffineExpr -> PolyExpr
| Eload: Ident
         -> PolyExpr (* Load Ix *)
         -> PolyExpr
.


Inductive PolyStmt :=
| Sstore: Ident
          -> PolyExpr (* Ix *)
          -> PolyExpr (* Store val *)
          -> PolyStmt
| Sseq: PolyStmt
        -> PolyStmt
        -> PolyStmt
| Sskip: PolyStmt
| Sloop: Indvar  (* Current loop induction variable index *)
         -> PolyExpr (* expression for upper bound *)
         -> PolyStmt (* loop body *)
         -> PolyStmt
.




(** Memory chunk: allows multidimensional reads and writes **)
Definition ChunkNum := Z.

Lemma chunk_num_eq_dec: forall (c1 c2: ChunkNum), {c1 = c2} + {c1 <> c2}.
Proof.
  intros.
  apply Z.eq_dec.
Qed.
Hint Resolve chunk_num_eq_dec.

Record MemoryChunk :=
  mkMemoryChunk {
      memoryChunkDim: nat;
      memoryChunkModel: list Z -> option Value
    }.

Definition const {A B : Type} (a: A) (_: B) : A := a.

Definition initMemoryChunk (n: nat): MemoryChunk :=
  mkMemoryChunk n (const None).

(* Need this to perform == on list of Z *)
Program Instance Z_eq_eqdec : EqDec Z eq := Z.eq_dec.

(** Only allows legal stores, so the length of six "store index"
must be equal to the dimension of the memory chunk *)
Definition storeMemoryChunk (six: list Z)
           (v: Value) (mc: MemoryChunk): MemoryChunk :=
  let dim := memoryChunkDim mc in
  {| memoryChunkDim := dim;
     memoryChunkModel := if  Nat.eqb (List.length six)  dim
                         then (fun ix => if ix  == six
                                      then Some v
                                      else (memoryChunkModel mc) ix)
                         else memoryChunkModel mc
                                               
                                               
  |}.

Definition loadMemoryChunk (lix: list Z)(mc: MemoryChunk): option Value :=
  if Nat.eqb (List.length lix) (memoryChunkDim mc)
  then (memoryChunkModel mc lix)
  else None.

(* Memory is a map indexed by naturals to disjoint memory chunks *)
Notation Memory := (ZMap.t (option MemoryChunk)).


Check (PMap.set).
Definition storeMemory (chunknum: Z)
           (chunkix: list Z)
           (val: Value)
           (mem: Memory) : Memory :=
  let memchunk := mem ## chunknum in
  let memchunk' := option_map (fun chk => storeMemoryChunk chunkix val chk )
                              memchunk
  in ZMap.set chunknum memchunk' mem.



Definition loadMemory (chunknum: Z)
           (chunkix: list Z)
           (mem: Memory) : option Value :=
  (mem ## chunknum) >>= (fun chk => loadMemoryChunk chunkix chk).


(** **Reading from a different chunk allows to read the old value *)
Definition memory_chunk_gso: forall (needle_chunk: Z)
                               (needle_ix: list Z)
                               (haystack_chunk: Z)
                               (haystack_ix: list Z)
                               (val: Value)
                               (NOALIAS: needle_chunk <> haystack_chunk)
                               (mem: Memory),
    loadMemory needle_chunk needle_ix
               (storeMemory haystack_chunk haystack_ix val mem) = 
    loadMemory needle_chunk needle_ix mem.
Proof.
Admitted.

Hint Resolve memory_chunk_gso.
(** **Reading from a different index at the same chunk allows to read the old value *)
Definition memory_ix_gso: forall (needle_chunk: Z)
                            (needle_ix: list Z)
                            (haystack_ix: list Z)
                            (val: Value)
                            (NOALIAS: needle_ix <> haystack_ix)
                            (mem: Memory),
    loadMemory needle_chunk needle_ix
               (storeMemory needle_chunk haystack_ix val mem) =
    loadMemory needle_chunk needle_ix mem.
Proof.
  intros.
  unfold loadMemory.
  unfold storeMemory.
Admitted.
Hint Resolve memory_ix_gso.


Hint Resolve memory_chunk_gso.

(** **Reading from a the same index and chunk as the store allows to read the stored value *)
Definition memory_ix_gss: forall (needle_chunk: Z)
                            (needle_ix: list Z)
                            (val: Value)
                            (mem: Memory),
    loadMemory needle_chunk needle_ix
               (storeMemory needle_chunk needle_ix val mem) = Some val.
Proof.
  intros.
Admitted.
Hint Resolve memory_ix_gss.



Definition liftoption3 {a b c d: Type} (f: a -> b -> c -> d)
           (oa: option a) (ob: option b) (oc: option c): option d :=
  oa >>= (fun a => ob >>= (fun b => oc >>= (fun c => Some (f a b c)))).


Record PolyLoop :=
  mkPolyLoop {
      loopLowerBound: PolyExpr;
      loopUpperBound: PolyExpr;
      loopBody: PolyStmt;
    }.

(* Mapping from indexing expressions to environments *)
(* Called environment because it is shared between poly an scop*)
Record Environment :=
  mkEnvironment {
      envIndvarToValue: ZMap.t (option Value);
      envIdentToChunkNum: ZMap.t (option ChunkNum);
      envLoopDepth: Z;
    }.

(** Get the induction variable of the "current" loop **)
Definition evalLoopIndvar (env: Environment)
           (indvar: Indvar): option Value :=
  (envIndvarToValue env) ## indvar.

(** Increase the induction variable by 1 **)
Definition bumpLoopIndvar (env: Environment)
           (indvar: Indvar) : Environment :=
  let ivToValue : ZMap.t (option Value) := envIndvarToValue env in
  let option_oldiv := ivToValue ## indvar in
  match option_oldiv with
  | None => env
  | Some oldiv => let newIvToValue := ZMap.set indvar (Some (1 + oldiv)%Z) ivToValue in
                  {|
                    envIndvarToValue := newIvToValue; 
                    envIdentToChunkNum := envIdentToChunkNum env;
                    envLoopDepth := envLoopDepth env;
                  |}
  end.



Definition addLoopToEnv (env: Environment)
           (indvar: Indvar): Environment :=
  let oldLoopDepth := envLoopDepth env in
  let newLoopDepth := (oldLoopDepth + 1)%Z in
  let ivToValue : ZMap.t (option Value) := envIndvarToValue env in
  let newIvToValue := ZMap.set indvar (Some (0%Z)) ivToValue in
  {|
    envIndvarToValue := newIvToValue; 
    envIdentToChunkNum := envIdentToChunkNum env;
    envLoopDepth := newLoopDepth
  |}.

Definition removeLoopFromEnv (env: Environment)
           (indvar: Indvar): Environment :=
  let oldLoopDepth := envLoopDepth env in
  let newLoopDepth := (oldLoopDepth + 1)%Z in
  let ivToValue : ZMap.t (option Value) := envIndvarToValue env in
  let newIvToValue := ZMap.set indvar (None) ivToValue in
  {|
    envIndvarToValue := newIvToValue; 
    envIdentToChunkNum := envIdentToChunkNum env;
    envLoopDepth := newLoopDepth
  |}.



Fixpoint evalAffineExprFn (env: Environment) 
         (ae: AffineExpr) : option Value :=
  match ae with
  | Aindvar i => ((envIndvarToValue env) ## i)
  | Aconst c => Some c
  | _ => None
  end .

Fixpoint evalExprFn (pe: PolyExpr)
         (env: Environment)
         (mem: Memory): option Value :=
  match pe with
  | Eaffine ae => evalAffineExprFn env ae
  | Eload id ixe => let ochunknum := (envIdentToChunkNum env) ## id in
                    let oix := evalExprFn ixe env mem in
                    ochunknum >>=
                              (fun chunknum => oix >>=
                                                   fun ix =>
                                                     loadMemory chunknum [ix] mem)
  end.


Inductive exec_stmt : Environment -> Memory 
                      -> PolyStmt
                      -> Memory -> Environment -> Prop:=
| exec_Sstore: forall (chunknum ix: Z)
                      (storeval: Z)
                      (storevale ixe: PolyExpr)
                      (env: Environment)
                      (mem mem': Memory)
                      (ident: Ident),
    evalExprFn storevale env mem = Some storeval ->
    evalExprFn ixe env mem = Some ix ->
    ((envIdentToChunkNum env) ## ident = Some chunknum) ->
    storeMemory chunknum [ix] storeval mem = mem' ->
    exec_stmt env mem (Sstore ident ixe storevale) mem' env
| exec_SSeq: forall (env env' env'': Environment)
                    (mem mem' mem'': Memory)
                    (s1 s2: PolyStmt),
    exec_stmt env mem s1 mem' env' ->
    exec_stmt env' mem' s2 mem'' env'' ->
    exec_stmt env mem (Sseq s1 s2) mem'' env''
| exec_Sskip: forall (mem : Memory) (env: Environment),
    exec_stmt env mem Sskip mem env
| exec_Sloop_start: forall (mem: Memory)
                           (indvar: Indvar)
                           (ube: PolyExpr)
                           (env: Environment)
                           (inner: PolyStmt),
    evalLoopIndvar env indvar = None (* We don't have the indvar *)
    -> exec_stmt env mem (Sloop indvar ube inner) mem (addLoopToEnv env indvar)
| exec_Sloop_loop: forall (mem mem': Memory)
                          (env env': Environment)
                          (indvar: Indvar)
                          (ube: PolyExpr)
                          (ub ivval: Value)
                          (inner: PolyStmt),
    evalExprFn ube env mem = Some ub ->
    evalLoopIndvar env indvar = Some ivval ->
    (ivval < ub)%Z ->
    exec_stmt env mem inner mem' env' ->
    exec_stmt env mem (Sloop indvar ube inner) mem' (bumpLoopIndvar env' indvar)
| exec_Sloop_end: forall (mem: Memory)
                         (env: Environment)
                         (indvar: Indvar)
                         (ube: PolyExpr)
                         (ub ivval: Value)
                         (inner: PolyStmt),
    evalExprFn ube env mem = Some ub ->
    evalLoopIndvar env indvar = Some ivval ->
    (ivval >= ub)%Z ->
    exec_stmt env mem (Sloop indvar ube inner) mem (removeLoopFromEnv env indvar)
.



Lemma exec_stmt_deterministic: forall (mem mem1 mem2: Memory)
                                      (env env1 env2: Environment)
                                      (s: PolyStmt),
    exec_stmt env mem s mem1 env1 ->
    exec_stmt env mem s mem2 env2 ->
    mem1 = mem2 /\
    env1 = env2.
Proof.
  intros until s.
  intros EXECS1.
  generalize dependent env2.
  generalize dependent mem2.
  induction EXECS1;
    intros mem2 env2 EXECS2;
    inversion EXECS2; subst; auto;
      (* Dispatch cases which require simple rewrites *)
      repeat (match goal with
              | [H1: ?X = ?Y, H2: ?X = ?Z |- _ ] =>  rewrite H1 in H2;
                                                     inversion H2;
                                                     clear H1; clear H2
              end); auto;
        (* dispatch cases that are resolved by indvar mutual exclusion *)
        try omega.


  
  - assert (S1_EQ: mem' = mem'0 /\ env' = env'0).
    apply IHEXECS1_1; auto.
    destruct S1_EQ as [MEMEQ ENVEQ].
    subst.
    apply IHEXECS1_2; auto.

  - assert (EQ: mem' = mem2 /\ env' = env'0).
    apply IHEXECS1. auto.

    destruct EQ as [MEMEQ ENVEQ]. subst.
    auto.
Qed.

