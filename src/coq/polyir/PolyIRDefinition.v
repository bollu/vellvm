Require Import Omega.
Require Import Nat.
Require Import ZArith.
Require Import Ring.
Require Import List.
Require Import Ncring.
Require Import Ring_tac.
Require Import FunctionalExtensionality.
Require Import Maps.
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
Notation ChunkNum := Z.
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



Definition option_bind
           {A B: Type}
           (oa: option A)
           (f: A -> option B) : option B :=
  match oa with
  | None => None
  | Some a => f a
  end.

Infix ">>=" := option_bind (at level 100).



Definition loadMemory (chunknum: Z)
           (chunkix: list Z)
           (mem: Memory) : option Value :=
  (mem ## chunknum) >>= (fun chk => loadMemoryChunk chunkix chk).


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

(* A schedule is a multi-dimensional timepoint that is a function of
its inputs *)
Notation MultidimAffineExpr := (list AffineExpr).

Fixpoint option_traverse {A: Type} (lo: list (option A)): option (list A) :=
  match lo with
  | [] => Some []
  | oa::lo' => oa >>= (fun a => option_map (cons a) (option_traverse lo'))
  end.



Fixpoint option_traverse_fold_left {ACCUM A: Type}
         (accum: ACCUM)
         (f: ACCUM -> A -> option ACCUM)
         (l: list A): option (ACCUM) :=
  match l with
  | [] => Some accum
  | a::l' => (f accum a) >>= (fun accum2 => option_traverse_fold_left accum2 f l')
  end.

Module Type POLYHEDRAL_THEORY.
  Parameter PointT: Type.
  Parameter PolyT: Type.
  Parameter AffineFnT: Type.
  Parameter AffineRelT: Type.
  Parameter ParamsT: Type.
  (** Some way to specify a dimension *)
  Parameter DimensionT: Type.
  (** Some way to map a point with an affine function *)
  Parameter mapPoint: AffineFnT -> PointT -> option (PointT).
  (** Has some way to fill in the free variables *)
  Parameter evalPoint: ParamsT -> PointT -> option (list Z).
  (** Have some way to compose affine functions *)
  Parameter composeAffineFunction: AffineFnT -> AffineFnT -> option AffineFnT.
  (** Compute the inverse of an affine function *)
  Parameter invertAffineFunction: AffineFnT -> option AffineFnT.
  (** Have some way to check if two points are related *)
  Parameter arePointsRelated: PointT -> PointT -> AffineRelT -> bool.
  (** Check if a point is within a polyhedra *)
  Parameter isPointInPoly: PointT -> PolyT -> bool.

  (** Returns whether one point is lex smaller than the other *)
  Parameter isLexSmaller: PointT -> PointT -> option (bool).

  (** Returns whether one point is lex smaller than the other *)
  Parameter getLexminPoint: ParamsT -> PolyT -> PointT.

  (** Returns whether one point is lex smaller than the other *)
  Parameter getLexmaxPoint: ParamsT -> PolyT -> PointT.
  
  (** Find the next point that is within the polyhedra which is
    one smaller in terms of lex order. return Nothing if not possible *)
  Parameter getPrevLexPoint:ParamsT ->
                                   PolyT ->
                                   PointT ->
                                   option (PointT).

  (** Find the next point that is within the polyhedra which is
    one larger in terms of lex order. return Nothing if not possible *)
  Parameter getLexNextPoint: ParamsT ->
                                   PolyT ->
                                   PointT ->
                                   option (PointT).

  Parameter getOverapproximationNumPointsInPoly: ParamsT ->
                                                 PolyT ->
                                                 option (nat).
  (** Definition of an empty polyhedra *)
  Parameter emptyPoly: PolyT.

  (** Empty affine relation *)
  Parameter emptyAffineRel: AffineRelT.

  (** Take a union of two relations *)
  Parameter unionAffineRel:  AffineRelT -> AffineRelT -> AffineRelT.

  (** Weaken an affine function into an affine relation *)
  Parameter affineFnToAffineRel: AffineFnT -> AffineRelT.


  (** Definition of union of polyhedra *)
  Parameter unionPoly:  PolyT -> PolyT -> option PolyT.

  (** Defines what it means to be a dependence relation. This is the
        over-approximate definition. In particular, it does not ask for
        exact dependence relations .
        t1 --R1--> p 
        t2 --R2--> p
        t1 < t2
        ===============
          t1 --D--> t2
   *)
  Definition relationIsDependenceBetweenRelations
             (r1 r2: AffineRelT)
             (dep: AffineRelT): Prop :=
    forall (tp1 tp2 ixp1 ixp2: PointT)
           (TP1_MAPSTO_IXP1: arePointsRelated  tp1 ixp1 r1 = true)
           (TP2_MAPSTO_IXP2: arePointsRelated tp2 ixp2 r2 = true)
           (IXEQ: ixp1 = ixp2)
           (TP_LEX_ORDERED: isLexSmaller tp1 tp2 = Some true),
      arePointsRelated tp1 tp2 dep = true.

  (** A function to compute the dependence polyhedra of two relations *)
  Parameter getDependenceRelation: AffineRelT -> AffineRelT -> option AffineRelT.
  
  
End POLYHEDRAL_THEORY.

Module SCOP(P: POLYHEDRAL_THEORY).

  (* define semantics for evaluating a schedule *)
  (* 
    Fixpoint evalMultidimAffineExpr (env: Environment)
             (s: MultidimAffineExpr):  option (list Value) :=
      option_traverse (List.map (evalAffineExprFn env) s).
   *)


  Definition AccessFunction := P.AffineFnT. (**r Access function to model where to read or write from *)
  Inductive MemoryAccess :=
  | MAStore: ChunkNum (**r name *)
                    -> AccessFunction
                    -> (list Value -> Value) (**r value *)    
                    -> MemoryAccess
  | MALoad: ChunkNum (**r name *)
                   -> AccessFunction
                   -> MemoryAccess.


  (** Note that for now, we don't care what is stored or loaded, because
conceptually, we don't actually care either. We just want to make sure
that the reads/writes are modeled *)
  Record ScopStmt :=
    mkScopStmt {
        scopStmtDomain: P.PolyT; (**r The domain of the scop statement. That is, interpreted as
          0 <= <indvars[i]> <= <domain[i]> *)
        scopStmtSchedule : P.AffineFnT; (**r Function from the canonical induction variables to the schedule
         timepoint.  *)
        scopStmtMemAccesses: list MemoryAccess (**r List of memory accesses *)
      }.

  Record Scop :=
    mkScop {
        scopStmts : list ScopStmt; (**r The statements in this scop *)
        scopIndvars : list P.DimensionT; (**r Induction variables in this scop *)
      }.

  Fixpoint all (bs: list bool): bool :=
    List.fold_right andb true bs.

  Fixpoint zipWith {X Y Z: Type} (f: X -> Y -> Z)
           (xs: list X)
           (ys: list Y) : list Z :=
    match xs  with
    | [] => []
    | x::xs' => match ys with
                | [] => []
                | y::ys' => (f x y)::zipWith f xs' ys'
                end
    end.

  Definition zip {X Y : Type}
             (xs: list X)
             (ys: list Y): list (X * Y) :=
    @zipWith X Y (X * Y) (fun x y => (x, y)) xs ys.



  Definition evalAccessFunction (viv : P.PointT)
             (accessfn: P.AffineFnT): (list Z) :=  [].
    

  Definition getMemAccessLoadRelation (ma: MemoryAccess) : P.AffineRelT :=
    match ma with
    | MALoad _ accessfn => P.affineFnToAffineRel accessfn
    | _  =>  P.emptyAffineRel
    end .

  Definition getMemAccessStoreRelation (ma: MemoryAccess) : P.AffineRelT :=
    match ma with
    | MAStore _ accessfn _ => P.affineFnToAffineRel accessfn
    | _=>  P.emptyAffineRel
    end .
                                        


  (* TODO: intersect with the domain of the scop statement *)
  Definition getScopStmtLoads (ss: ScopStmt): P.AffineRelT :=
    List.fold_left P.unionAffineRel
                   (List.map getMemAccessLoadRelation  (scopStmtMemAccesses ss))
                   P.emptyAffineRel.

  Definition getScopStmtStores (ss: ScopStmt): P.AffineRelT :=
    List.fold_left P.unionAffineRel
                   (List.map getMemAccessStoreRelation  (scopStmtMemAccesses ss))
                   P.emptyAffineRel.
  
  Definition getScopStores(s: Scop): P.AffineRelT :=
    List.fold_left (fun rel ss =>
                      P.unionAffineRel rel
                                       (getScopStmtStores ss))
                   (scopStmts s)
                   P.emptyAffineRel.
  
  Definition getScopLoads(s: Scop): P.AffineRelT :=
    List.fold_left (fun rel ss =>
                      P.unionAffineRel rel
                                       (getScopStmtLoads ss))
                   (scopStmts s)
                   P.emptyAffineRel.



  (* Given a dependence relation and a schedule, we define what it means
    for a schedule to respect a dependence relation *)
  Definition scheduleRespectsDependence (schedule: P.AffineFnT)
             (dep: P.AffineRelT) : Prop :=
    forall (p1 q1: P.PointT), (P.arePointsRelated p1 q1 dep) = true ->
                              exists (p2 q2: P.PointT),
                                P.mapPoint schedule p1 = Some q1 ->
                                P.mapPoint schedule p2 = Some q2 ->
                                P.arePointsRelated (q1) (q2) dep = true.

  Definition scheduleRespectsRAW (schedule: P.AffineFnT) (s: Scop) : Prop :=
    exists (rel: P.AffineRelT),
      (P.getDependenceRelation (getScopStores s)
                               (getScopLoads s) = Some rel) /\
      scheduleRespectsDependence schedule rel.

  Definition scheduleRespectsWAW (schedule: P.AffineFnT) (s: Scop) : Prop :=
    exists (rel: P.AffineRelT),
      (P.getDependenceRelation (getScopStores s)
                               (getScopStores s) = Some rel) /\
      scheduleRespectsDependence schedule rel.



  Definition applyScheduleToScopStmt
             (schedule: P.AffineFnT)
             (ss: ScopStmt): option ScopStmt :=
    option_map (fun newschedule => {|
                    scopStmtDomain:= scopStmtDomain ss;
                    scopStmtSchedule := newschedule;
                    scopStmtMemAccesses := scopStmtMemAccesses ss
                  |}) (P.composeAffineFunction (scopStmtSchedule ss) schedule).

  Definition applyScheduleToScop
             (schedule: P.AffineFnT)
             (scop: Scop): option Scop :=
    option_map (fun newScopStmts => {|
                    scopStmts :=  newScopStmts;
                    scopIndvars := scopIndvars scop;
                  |})
               (option_traverse
                  (List.map (applyScheduleToScopStmt schedule)
                            (scopStmts scop))).

  (** =============PROOF============= **)
  
  Lemma applyScheduleToScopStmt_preserves_scop_stmt_domain:
    forall (ss ss': ScopStmt)
           (schedule: P.AffineFnT)
           (MAPPED: applyScheduleToScopStmt schedule ss = Some ss'),
      scopStmtDomain ss = scopStmtDomain ss'.
  Proof.
    intros.
    unfold applyScheduleToScopStmt in MAPPED.
    simpl.

    destruct (P.composeAffineFunction (scopStmtSchedule ss) schedule);
      simpl; auto; inversion MAPPED; auto.
  Qed.

  Hint Resolve applyScheduleToScopStmt_preserves_scop_stmt_domain.
  Hint Rewrite applyScheduleToScopStmt_preserves_scop_stmt_domain.

    
    (* Check if the current value of the induction variables is within
the scop stmts domain *)
    Definition isScopStmtActive (viv: P.PointT) (ss: ScopStmt) : bool :=
      P.isPointInPoly viv (scopStmtDomain ss).

    
    (* 
  Definition runMemoryAccess
             (viv: P.PointT)
             (memacc: MemoryAccess)
             (mem: Memory): option Memory :=
    match memacc with
    | MAStore chunk accessfn valfn  =>
      
      option_map (fun accessix =>storeMemory  chunk
                                   accessix
                                   (valfn accessix)
                                   mem)
    | MALoad  _ _=> None
    end.
  *)

  Definition viv := P.PointT.
  Inductive exec_memory_accesss:  viv -> Memory -> MemoryAccess -> Memory -> Prop :=
  | exec_store:
      forall (viv: P.PointT)
        (memacc: MemoryAccess)
        (initmem: Memory)
        (accessfn: AccessFunction)
        (accessix: list Value)
        (ACCESSIX: evalAccessFunction viv accessfn = accessix)
        (storefn: list Value -> Value)
        (storeval: Value)
        (chunk: ChunkNum),
        exec_memory_accesss viv
                            initmem
                            (MAStore chunk accessfn storefn)
                            (storeMemory chunk accessix (storefn accessix) initmem).


  Inductive exec_scop_stmt: viv -> Memory -> ScopStmt -> Memory -> Prop :=
  | exec_stmt_nil:
      forall (viv: P.PointT)
        (initmem: Memory)
        (domain: P.PolyT)
        (schedule: P.AffineFnT),
        exec_scop_stmt viv initmem (mkScopStmt domain schedule []) initmem
  | exec_stmt_cons:
      forall (viv: P.PointT)
        (domain: P.PolyT)
        (PT_IN_DOMAIN: P.isPointInPoly viv domain = true)
        (schedule: P.AffineFnT)
        (mas: list MemoryAccess)
        (ma: MemoryAccess)
        (memstmt: Memory)
        (initmem: Memory)
        (MEMSTMT: exec_scop_stmt viv initmem (mkScopStmt domain schedule mas) memstmt)
        (memnew: Memory)
        (MEMNEW_FROM_MEMSTMT: exec_memory_accesss viv initmem ma memnew),
        exec_scop_stmt viv initmem (mkScopStmt domain schedule (cons ma mas)) memnew
  .

  Definition getScopDomain (scop: Scop) : P.PolyT. Admitted.
  Definition exec_scop_at_point (params: P.ParamsT) (viv: viv)
             (mem: Memory)
             (scop: Scop)
             (mem': Memory): Prop. Admitted.
                                    


  Inductive exec_scop_from_lexmin: P.ParamsT -> viv -> Memory -> Scop -> Memory -> viv -> Prop :=
    (* 
  | exec_scop_at_lexmax:
      forall (initmem mem : Memory)
        (scop: Scop)
        (params: P.ParamsT)
        (vivmax: viv)
        (vivbegin: viv)
        (EXECPREV: exec_scop_from_lexmin params vivbegin initmem scop mem vivmax)
        (MAX: P.getLexNextPoint params (getScopDomain scop) vivmax = None),
        exec_scop_from_lexmin params
                              vivbegin
                              initmem
                              scop
                              mem
                              vivmax
                              *)
  | exec_scop_begin:
      forall (initmem mem: Memory)
        (scop: Scop)
        (params: P.ParamsT)
        (vivmin: viv)
        (VIVMIN: vivmin = (P.getLexminPoint params (getScopDomain scop))),
        exec_scop_from_lexmin params
                              vivmin
                              initmem
                              scop
                              initmem
                              vivmin
  | exec_scop_middle:
      forall (initmem mem1 mem2: Memory)
        (scop: Scop)
        (params: P.ParamsT)
        (vivbegin vivcur vivnext: viv)
        (NEXT: Some vivnext = P.getLexNextPoint params (getScopDomain scop)vivcur),
        exec_scop_from_lexmin params vivbegin initmem scop mem1  vivcur ->
        exec_scop_at_point params vivcur mem1 scop mem2 ->
        exec_scop_from_lexmin params vivbegin initmem scop mem2 vivnext.
        
    

      
       
        
        



                 
  
  (** TODO: make loads an actual statement in the PolyIR language **)
  Definition evalScopStmt (ss: ScopStmt)
             (viv: P.PointT)
             (se: ScopEnvironment)
             (initmem: Memory) : option Memory :=

    option_traverse_fold_left initmem
                              (fun mem memacc => runMemoryAccess se viv memacc mem)
                              (scopStmtMemAccesses ss).
  
  

  (** Get the statements whose domain is contained in the current environment **)
  Definition getActiveScopStmtsInScop
             (s: Scop)
             (viv: P.PointT)
             : list ScopStmt :=
    List.filter (isScopStmtActive viv) (scopStmts s).

      


  Definition evalPointInScop (s: Scop)
             (se: ScopEnvironment)
             (viv: P.PointT)
             (initmem: Memory): option Memory :=
    option_traverse_fold_left
      initmem (fun m ss => evalScopStmt ss viv se m)
      (getActiveScopStmtsInScop s viv).

    
    
  Fixpoint evalPointsInScopFromVIV
           (scop: Scop)
           (scopDomain: P.PolyT)
           (params: P.ParamsT)
           (se: ScopEnvironment)
           (viv: P.PointT)
           (mem: Memory)
           (fuel: nat): option Memory :=
    match fuel with
    | O => None
    | S fuel' =>
      evalPointInScop scop se  viv mem >>=
                      (fun mem' => match P.getNextLexPoint params scopDomain viv with
                                | None => Some mem'
                                | Some viv' =>evalPointsInScopFromVIV scop
                                                                     scopDomain
                                                                     params
                                                                     se
                                                                     viv'
                                                                     mem'
                                                                     fuel'
                                end)
    end.

  Definition getScopDomain (scop: Scop): P.PolyT. Admitted.
  Definition getScopFuel (scop: Scop): nat. Admitted.
  
  Definition evalScop (scop: Scop)
             (se: ScopEnvironment)
             (params: P.ParamsT)
             (mem: Memory) : option Memory := evalPointsInScopFromVIV
                           scop
                           (getScopDomain scop)
                           params
                           se
                           (P.getLexminPoint params (getScopDomain scop))
                           mem
                           (getScopFuel scop).
  

  
End SCOP.

