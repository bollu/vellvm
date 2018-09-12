Require Import Omega.
Require Import Nat.
Require Import ZArith.
Require Import Ring.
Require Import List.
Require Import Ncring.
Require Import Ring_tac.
Require Import FunctionalExtensionality.
Require Import Sorting.
Require Import ListSet.
Require Import Coqlib.
Require Import Maps.
Require Import EquivDec.
Require Import Equalities.

Require Import Vellvm.Crush.

(** Import VPL for polyhedral goodness *)
From Vpl Require Import PedraQ DomainInterfaces.
Require Import VplTactic.Tactic.
Add Field Qcfield: Qcft (decidable Qc_eq_bool_correct, constants [vpl_cte]).

Import PedraQ.FullDom.

Local Notation "a ## b" := (ZMap.get b a) (at level 1).

(* Equalities stuff *)
Require Import EquivDec.
Require Import Equalities.
(* A schedule is a multi-dimensional timepoint that is a function of
its inputs *)

Open Scope list_scope.
Import ListNotations.


Definition option_bind
           {A B: Type}
           (oa: option A)
           (f: A -> option B) : option B :=
  match oa with
  | None => None
  | Some a => f a
  end.

Infix ">>=" := option_bind (at level 100).

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

(** ***Consider making IX a type *)
Lemma ix_eq_decidable: forall (ix1 ix2: list Z),
    {ix1 = ix2} + {ix1 <> ix2}.
Proof.
  decide equality; auto.
Admitted.
Hint Resolve ix_eq_decidable.


Module Type POLYHEDRAL_THEORY.
  (** A point in a polyhedra *)
  Parameter PointT: Type.
  (** A polyhedra *)
  Parameter PolyT: Type.
  (** Affine function *)
  Parameter AffineFnT: Type.
  (** Affine relation *)
  Parameter AffineRelT: Type.
  (** Paramter values, which allows to instantiate a parametric
      polyhedra into a concrete polyhedra *)
  Parameter ParamsT: Type.
  (** Some way to specify a dimension *)
  Parameter DimensionT: Type.
  (** Some way to map a point with an affine function *)
  Parameter mapPoint: AffineFnT -> PointT -> option (PointT).
  (** Has some way to fill in the free variables *)
  Parameter evalPoint: ParamsT -> PointT -> (list Z).

  (** Convert a point x0 to a polyhedra {x | x = x0 } *)
  Parameter pointToPoly: PointT -> PolyT.

  (** Compose an affine function *)
  Parameter composeAffineFunction: AffineFnT -> AffineFnT -> AffineFnT.

  (** Find the inverse of a concrete evaluation of an affine function **)
  Parameter invertEvalAffineFn: ParamsT -> AffineFnT -> list Z -> PointT.

  (** Evaluate an affine function *)
  Parameter evalAffineFn: ParamsT -> AffineFnT -> PointT -> list Z.

  Axiom invertEvalAffineFn_is_inverse:
    forall (params: ParamsT)
      (pt: PointT)
      (fn: AffineFnT),
      invertEvalAffineFn params fn (evalAffineFn params fn pt) = pt.
  
  (** Have some way to check if two points are related *)
  Parameter arePointsRelated: PointT -> PointT -> AffineRelT -> bool.
  (** Check if a point is within a polyhedra *)
  Parameter isPointInPoly: PointT -> PolyT -> bool.


  (** x \in { x0 } -> x = x0 *)
  Axiom pointInSingletonPoly: forall (p: PointT) (singleton: PointT),
      isPointInPoly p (pointToPoly singleton) = true ->
      p = singleton.



  (** isPolySubset P Q = is P a subset of Q *)
  Parameter isPolySubset: PolyT -> PolyT -> bool.

  (* x \in Smaller, Smaller \subset Larger -> x \in Larger *)
  Axiom isPolySubset_spec: forall (smaller larger: PolyT),
      (isPolySubset smaller larger = true) <->
      (forall (pt: PointT),
          isPointInPoly pt smaller = true -> isPointInPoly pt larger = true).

  
  (* x \notin Larger, Smaller \subset Larger -> x \notin Smaller *)
  Lemma pointInSubsetPoly_false:
    forall (p: PointT)
      (smaller larger: PolyT)
      (P_NOT_IN_LARGER: isPointInPoly p larger = false)
      (SUBSET: isPolySubset smaller larger = true),
      isPointInPoly p smaller = false.
  Proof.
    intros.
    destruct (isPointInPoly p smaller) eqn:POINT_IN_SMALLER; auto.

    assert (P_IN_LARGER: isPointInPoly p larger = true).
    eapply isPolySubset_spec; eauto.
    congruence.
  Qed.


  
  (** Returns whether one point is lex < than the other *)
  Parameter isLexLT: PointT -> PointT -> option (bool).

  Notation "p <l q" := (isLexLT p q) (at level 50).

  
  Definition isLexLE (p q: PointT) :=
    isLexLT p q = Some true \/ p = q.

  Notation "p <=l q" := (isLexLE p q) (at level 50).
  
  (** Returns whether one point is lex > than the other *)
  Parameter isLexGT: PointT -> PointT -> option (bool).

  Notation "p >l q" := (isLexGT p q) (at level 50).

  Definition isLexGE (p q: PointT) :=
    isLexGT p q = Some true \/ p = q.

  Notation "p >=l q" := (isLexGE p q) (at level 50).


  Axiom isLexLT_GT: forall (a b :PointT), isLexLT a b = Some true
                                     <-> isLexGT b a = Some true.

  Axiom isLexGT_not_refl: forall (p: PointT), isLexGT p p = Some false.


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


  (** Get the polyhedra of points which are lex <=  the given point *)
  Parameter getLexLeqPoly: ParamsT -> PolyT -> PointT -> PolyT.

  Axiom getLexLeqPoly_spec:
    forall (params: ParamsT)
      (poly: PolyT)
      (p: PointT)
      (lexsmall: PointT),
      isPointInPoly (lexsmall) (getLexLeqPoly params poly p) = true <->
      (lexsmall <=l p).

  (** Get the polyhedra of points which are lex <  the given point *)
  Parameter getLexLtPoly: ParamsT -> PolyT -> PointT -> PolyT.
  
  Lemma getLexLeqPoly_proper_wrt_subset:
    forall (params: ParamsT)
      (small large: PolyT)
      (p: PointT)
      (SUBSET: isPolySubset small large = true),
      isPolySubset (getLexLeqPoly params small p)
                   (getLexLeqPoly params large p) = true.
  Proof.
    intros.
    apply isPolySubset_spec.
    rewrite isPolySubset_spec in SUBSET.

    intros lexpt LEXPT_IN_LEXPOLY.
    rewrite getLexLeqPoly_spec.
    rewrite getLexLeqPoly_spec in LEXPT_IN_LEXPOLY.
    auto.
  Qed.

  Lemma getLexLeqPoly_contains_leq_point:
    forall (params: ParamsT)
      (poly: PolyT)
      (p: PointT),
      isPointInPoly p poly = true ->
      isPointInPoly p (getLexLeqPoly params poly p) = true.
  Proof.
    intros.
    rewrite getLexLeqPoly_spec.
    unfold isLexLE.
    auto.
  Qed.
    


  (** {x | x <= lexmin(P), x \in P} = { lexmin(P)} *)
  Axiom getLexLeqPoly_from_lexmin_is_point:
    forall (params: ParamsT)
      (poly: PolyT),
    (getLexLeqPoly params poly (getLexminPoint params poly)) =
      pointToPoly (getLexminPoint params poly).
      

  (** Get the polyhedra of points which are lex > the given point *)
  Parameter getLexGtPoly: ParamsT -> PolyT -> PointT -> PolyT.

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
  Parameter unionPoly:  PolyT -> PolyT ->  PolyT.
  
  (** unionPoly is commutative *)
  Axiom unionPoly_commutative: forall (p q: PolyT), unionPoly p q = unionPoly q p.

  
  (** unionPoly is associative *)
  Axiom unionPoly_associative:
    forall (p q r: PolyT), unionPoly p (unionPoly q r) = unionPoly (unionPoly p q) r.

  
  (** A polyhedra is always a subset of the union *)
  Axiom subset_of_union: forall (P Q: PolyT),
      isPolySubset P (unionPoly P Q) = true.


  (** Defines what it means to be a dependence relation. This is the
        over-approximate definition. In particular, it does not ask for
        exact dependence relations .
<<  
        t1 --R1--> p 
        t2 --R2--> p
        t1 < t2
        ===============
          t1 --D--> t2
>>
   *)
  Definition relationIsDependenceBetweenRelations
             (r1 r2: AffineRelT)
             (dep: AffineRelT): Prop :=
    forall (tp1 tp2 ixp1 ixp2: PointT)
           (TP1_MAPSTO_IXP1: arePointsRelated  tp1 ixp1 r1 = true)
           (TP2_MAPSTO_IXP2: arePointsRelated tp2 ixp2 r2 = true)
           (IXEQ: ixp1 = ixp2)
           (TP_LEX_ORDERED: isLexLT tp1 tp2 = Some true),
      arePointsRelated tp1 tp2 dep = true.

  (** A function to compute the dependence polyhedra of two relations *)
  Parameter getDependenceRelation: AffineRelT -> AffineRelT -> option AffineRelT.


  (** An induction principle on all points that are lex smaller tha a
  given point in the polyhedra *)
  Axiom polyhedra_ind_lex_smaller_points: forall
      (params: ParamsT)
      (P: PointT -> Prop)
      (Q: PolyT -> Prop)
      (fullpoly: PolyT),
      (Q emptyPoly) -> (
        forall (curpoint: PointT),
          Q (getLexLtPoly params fullpoly curpoint) -> P curpoint ->
          Q (getLexLeqPoly params fullpoly curpoint)) ->
      Q fullpoly.

  
  (** The lex min point is not lex greater than any point *)
  Axiom isLexGT_of_lexmin_is_always_false:
    forall (params: ParamsT) (poly: PolyT) (pt: PointT) (b: bool),
    isPointInPoly pt poly = true ->
    isLexGT (getLexminPoint params poly) pt = Some b ->
    b = false.

  Axiom isLexLT_next_implies_isLexLEQ_current:
    forall (params: ParamsT)
      (dom: PolyT)
      (next cur p: PointT)
      (NEXT: getLexNextPoint params dom cur = Some next)
      (LT: p <l next = Some true),
      p <l cur = Some true \/ p = cur.
    
  
  
End POLYHEDRAL_THEORY.

Module SCOP(P: POLYHEDRAL_THEORY).

    Definition ChunkNum := Z.

    Lemma chunk_num_eq_dec: forall (c1 c2: ChunkNum), {c1 = c2} + {c1 <> c2}.
    Proof.
      intros.
      apply Z.eq_dec.
    Qed.
    Hint Resolve chunk_num_eq_dec.

  (* define semantics for evaluating a schedule *)
  (* 
    Fixpoint evalMultidimAffineExpr (env: Environment)
             (s: MultidimAffineExpr):  option (list Value) :=
      option_traverse (List.map (evalAffineExprFn env) s).
   *)

  Definition AccessFunction := P.AffineFnT. (**r Access function to model where to read or write from *)

  
  (** The identifier of some loaded value, to be stored in the abstract
    scop environment *)
  Definition ScopLoadIdent := Z.

  (** Mapping from load identifiers to values *)
  Definition ScopEnvironment := ZMap.t (option Z).

  (** The things that a store expression is allowed to store
   A[i, j, k, ..] = <ScopStore>*)
  Inductive ScopStoreValue :=
  | SSVIndvarFn (indvarfn: list Z -> Z):
      ScopStoreValue (**r function of indvars *)
  | SSVLoadedVal (itostore: ScopLoadIdent):
      ScopStoreValue (**r store some loaded value *)
  .

  Inductive MemoryAccess :=
  | MAStore (chunk: ChunkNum) (**r array name *)
            (accessfn: AccessFunction) (**r index expression *)
            (ssv: ScopStoreValue) (**r value to store *)
            : MemoryAccess
  | MALoad (chunk: ChunkNum) (**r name *)
            (loadname: ScopLoadIdent)  (**r abstract store identiffier *)
            (accessfn: AccessFunction) (**r index expression *)
    : MemoryAccess.

  (** **Return the access function of this array *)
  Definition getMAAccessFunction (ma: MemoryAccess): AccessFunction :=
    match ma with
    | MAStore _ accessfn _ => accessfn
    | MALoad _ _ accessfn => accessfn
    end.


  (** Space where the virtual induction variables live **)
  Definition VIVSpace := P.PolyT.
  (** Space where the multidimensional timepoints live *)
  Definition ScatterSpace := P.PolyT.

  
  Record ScopStmt :=
    mkScopStmt {
        scopStmtDomain: VIVSpace; (**r Stmt is executed if `viv \in scopStmtDomain` *)
        

        scopStmtSchedule : P.AffineFnT; (**r `VIVSpace -> ScatterSpace` *)
        scopStmtMemAccesses: list MemoryAccess (**r List of memory accesses *)
      }.

  Record Scop :=
    mkScop {
        scopStmts : list ScopStmt; (**r The statements in this scop *)
      }.

  (** Get the memory accesses in a scop *)
  Definition getScopMemoryAccesses (scop: Scop): list MemoryAccess :=
    concat (List.map (scopStmtMemAccesses) (scopStmts scop)).



  Definition evalAccessFunction
             (params: P.ParamsT)
             (accessfn: P.AffineFnT)
             (viv : P.PointT) : (list Z) :=
    P.evalAffineFn params  accessfn viv.
  Hint Unfold evalAccessFunction.
  Hint Transparent  evalAccessFunction.
    

  Definition getMemAccessLoadRelation (ma: MemoryAccess) : P.AffineRelT :=
    match ma with
    | MALoad _ _ accessfn => P.affineFnToAffineRel accessfn
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
             (ss: ScopStmt):  ScopStmt :=
    {|
      scopStmtDomain := scopStmtDomain ss;
      scopStmtSchedule := P.composeAffineFunction
                            (scopStmtSchedule ss)
                            schedule;
      scopStmtMemAccesses := scopStmtMemAccesses ss
    |}.

  Definition applyScheduleToScop
             (schedule: P.AffineFnT)
             (scop: Scop): Scop :=
               {|
                 scopStmts := List.map (applyScheduleToScopStmt schedule) (scopStmts scop);
               |}.

  
  (** *Hint database of proof *)
  Create HintDb proofdb.

  (** **Add all theorems from the polyhedral theory  into hint database*)
  Hint Resolve P.invertEvalAffineFn_is_inverse: proofdb.
  Hint Resolve P.isLexLT_GT: proofdb.
  Hint Rewrite P.isLexLT_GT: proofdb.
  Hint Resolve P.unionPoly_commutative: proofdb.
  Hint Resolve P.unionPoly_associative: proofdb.
  Hint Resolve P.getLexLeqPoly_proper_wrt_subset: proofdb.
  Hint Resolve P.subset_of_union:proofdb.
  Hint Resolve P.getLexLeqPoly_from_lexmin_is_point:proofdb.
  Hint Resolve P.getLexLeqPoly_contains_leq_point:proofdb.
  Hint Resolve P.pointInSingletonPoly:proofdb.
  Hint Resolve P.isLexGT_not_refl:proofdb.
  Hint Resolve P.isLexLT_next_implies_isLexLEQ_current:proofdb.
  Hint Resolve Z.eqb_refl: proofdb.

  (** List rewrite rules *)
  Lemma existsb_app_single: forall {A: Type} (l: list A) (a: A)
    (pred: A -> bool),
      existsb pred (l ++ [a]) = existsb pred l || pred a.
  Proof.
    intros.
    rewrite existsb_app.
    simpl.
    rewrite orb_false_r.
    auto.
  Qed.
  Hint Rewrite @existsb_app_single: list.
  Hint Rewrite existsb_app: list.
  Hint Resolve existsb_app: list.
  Hint Resolve orb_false_elim: list.

  (* Value that expressions can take *)
  Notation Value := Z.
  Section MEMORY.


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
Definition Memory := (ZMap.t (option MemoryChunk)).


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
  End MEMORY.

  (** *Section that define the semantics of scop evaluation *)
  Section EVALUATION.



    Definition viv := P.PointT.
    Definition Schedule := P.AffineFnT.

    
    Inductive exec_scop_store_value:
      P.ParamsT
      -> ScopEnvironment
      -> viv
      -> ScopStoreValue
      -> Value -> Prop :=
  | eval_ssv_indvar_fn: forall (viv: P.PointT)
                          (se: ScopEnvironment)
                          (params: P.ParamsT)
                          (evalviv: list Z)
                          (EVALVIV: P.evalPoint params viv = evalviv)
                          (indvarfn: list Z -> Z),
      exec_scop_store_value params
                            se
                            viv
                            (SSVIndvarFn indvarfn)
                            (indvarfn evalviv)
  | eval_ssv_loaded_value: forall (viv: P.PointT)
                             (se: ScopEnvironment)
                             (params: P.ParamsT)
                             (ident: ScopLoadIdent)
                             (identval: Value)
                             (SE_AT_IDENT: se ## ident = Some identval),
      exec_scop_store_value params
                            se
                            viv
                            (SSVLoadedVal ident)
                            identval
  .

  Lemma exec_scop_store_value_deterministic:
    forall (params: P.ParamsT)
      (se: ScopEnvironment)
      (viv: viv)
      (ssv: ScopStoreValue)
      (v1 v2: Value)
      (EXEC1: exec_scop_store_value params se viv ssv v1)
      (EXEC2: exec_scop_store_value params se viv ssv v2),
      v1 = v2.
  Proof.
    intros.
    induction EXEC1; subst; inversion EXEC2; subst; congruence.
  Qed.

  Hint Resolve exec_scop_store_value_deterministic: proofdb.

  
  Inductive exec_memory_access:  P.ParamsT
                                 -> ScopEnvironment
                                 -> viv
                                 -> Memory
                                 -> MemoryAccess
                                 -> Memory -> Prop :=
    | exec_store:
        forall (params: P.ParamsT)
          (se: ScopEnvironment)
          (viv: P.PointT)
          (initmem: Memory)
          (accessfn: AccessFunction)
          (accessix: list Value)
          (ACCESSIX: evalAccessFunction params accessfn viv = accessix)
          (ssv: ScopStoreValue)
          (storeval: Value)
          (SSV: exec_scop_store_value params se viv ssv storeval)
          (chunk: ChunkNum),
          exec_memory_access params se viv
                              initmem
                              (MAStore chunk accessfn ssv)
                              (storeMemory chunk accessix storeval initmem).

  (** Evaluate a scop statement schedule to get the timepoint in the scatterspace *)
  Definition evalScopStmtSchedule (params: P.ParamsT) (viv: P.PointT)
             (stmt: ScopStmt) : list Z :=
    P.evalAffineFn params (scopStmtSchedule stmt) viv.



    (** Execute a statement. Checks if the statement is active or inactive before
       execution *)
  Inductive exec_scop_stmt: P.ParamsT
                            -> ScopEnvironment
                            -> viv
                            -> Memory
                            -> ScopStmt
                            -> Memory -> Prop :=
    | exec_stmt_nil:
        forall (params: P.ParamsT)
          (se: ScopEnvironment)
          (viv: P.PointT)
          (initmem: Memory)
          (domain: P.PolyT)
          (schedule: P.AffineFnT),
          exec_scop_stmt params se viv initmem (mkScopStmt domain schedule []) initmem
    | exec_stmt_cons_active:
        forall (params: P.ParamsT)
          (se: ScopEnvironment)
          (viv: P.PointT)
          (domain: P.PolyT)
          (PT_IN_DOMAIN: P.isPointInPoly viv domain = true)
          (schedule: P.AffineFnT)
          (mas: list MemoryAccess)
          (ma: MemoryAccess)
          (memstmt: Memory)
          (initmem: Memory)
          (MEMSTMT: exec_scop_stmt params se viv initmem (mkScopStmt domain schedule mas) memstmt)
          (memnew: Memory)
          (MEMNEW_FROM_MEMSTMT: exec_memory_access params se viv memstmt ma memnew),
          exec_scop_stmt params se viv initmem (mkScopStmt domain schedule (cons ma mas)) memnew
    | exec_stmt_cons_inactive:
        forall (params: P.ParamsT)
          (se: ScopEnvironment)
          (viv: P.PointT)
          (domain: P.PolyT)
          (PT_IN_DOMAIN: P.isPointInPoly viv domain = false)
          (schedule: P.AffineFnT)
          (mas: list MemoryAccess)
          (initmem: Memory),
          exec_scop_stmt params se viv initmem (mkScopStmt domain schedule mas) initmem
  .

  Definition isLexGt (l1: list Z) (l2: list Z): bool := false.

  Definition stmtIsScheduledAfter (params: P.ParamsT) (vivcur: viv)
             (safter: ScopStmt) (sbefore: ScopStmt):=
    isLexGt (evalScopStmtSchedule params vivcur sbefore)
            (evalScopStmtSchedule params vivcur safter).
    
  (** Execute a scop at a point given that the statements are sorted
      in DESCENGIN order:
    That is, the first element of the list is the lex LARGEST.
   So, the first element in the list is executed LAST.
   `[s1, s0]` is executed in the order `(s0; s1)`. *)
    Inductive exec_scop_at_point_sorted_stmts: P.ParamsT
                                  -> ScopEnvironment
                                  -> viv
                                  -> Memory
                                  -> Scop
                                  -> Memory -> Prop :=
    | exec_scop_at_point_nil:
        forall (params: P.ParamsT)
          (se: ScopEnvironment)
          (viv: P.PointT)
          (initmem: Memory)
          (scop: Scop)
          (mem': Memory),
          exec_scop_at_point_sorted_stmts  params se viv initmem (mkScop []) initmem
    | exec_scop_at_point_cons:
        forall (params: P.ParamsT)
          (se: ScopEnvironment)
          (viv: P.PointT)
          (initmem: Memory)
          (scop: Scop)
          (curstmt: ScopStmt)
          (prevstmts: list ScopStmt)
          (mem1 mem2: Memory)
          (SORTED: forall (s: ScopStmt) (S_IN_PREV: List.In s prevstmts),
              stmtIsScheduledAfter params viv curstmt s = true)
          (EXECPREV: exec_scop_at_point_sorted_stmts  params se viv initmem (mkScop prevstmts) mem1)
          (EXECCUR: exec_scop_stmt params se viv mem1 curstmt mem2),
          exec_scop_at_point_sorted_stmts
            params
            se
            viv
            initmem
            (mkScop (curstmt::prevstmts))
            mem2.


    (** sort statement in the ascending order acording to their schedule *)
    Definition sortStmtsBySchedDescend (params: P.ParamsT)
               (viv: viv)
             (l: list ScopStmt): list ScopStmt := l.

  (** Sort points in ascending order and then execute them *)
  Definition exec_scop_at_point (params: P.ParamsT)
             (se: ScopEnvironment)
             (viv: viv)
             (initmem: Memory)
             (scop: Scop)
             (finalmem: Memory) : Prop :=
    exec_scop_at_point_sorted_stmts
      params
      se
      viv
      initmem
      (mkScop (sortStmtsBySchedDescend params viv (scopStmts scop)))
      finalmem.

    Definition getScopDomain (scop: Scop): P.PolyT :=
      List.fold_left P.unionPoly (map scopStmtDomain (scopStmts scop)) P.emptyPoly.

    Lemma fold_left_reverse_input:
      forall {T: Type}
        (op: T -> T -> T)
        (ts1 ts2: list T)
        (t0: T)
        (OP_COMMUT: forall t1 t2, op t1 t2 = op t2 t1)
        (OP_ASSOC: forall t1 t2 t3, op (op t1 t2) t3 = op t1 (op t2 t3)),
        fold_left op (ts1 ++ ts2) t0 = fold_left op (ts2 ++ ts1) t0.
    Proof.
      intros until ts1.
      induction ts1.
      - intros.
        simpl.
        rewrite List.app_nil_r.
        auto.

      - intros ts2.
        induction ts2.
        + intros. simpl. rewrite List.app_nil_r.
          reflexivity.
        + intros.
          simpl.
          rewrite IHts1; auto.
          rewrite <- IHts2; auto.
          simpl.
          rewrite IHts1; auto.
          replace (op (op t0 a ) a0) with (op (op t0 a0) a).
          reflexivity.

          rewrite OP_ASSOC.
          replace (op a0 a) with (op a a0); auto.
    Qed.


    Check fold_left.
    Lemma fold_left_nest_app:
      forall {T: Type}
        (op: T -> T -> T)
        (ts1 ts2: list T)
        (t0: T)
        (OP_COMMUT: forall t1 t2, op t1 t2 = op t2 t1)
        (OP_ASSOC: forall t1 t2 t3, op (op t1 t2) t3 = op t1 (op t2 t3)),
        fold_left op (ts1 ++ ts2) t0 = fold_left op ts1 (fold_left op ts2 t0).
    Proof.
      intros until ts2.
      generalize ts1.
      induction ts2; auto.
      - intros.
        rewrite List.app_nil_r; auto.
      - intros.
        replace (ts0 ++ a :: ts2) with ((ts0 ++ [a]) ++ ts2); auto.
        replace (a :: ts2) with ([a] ++ ts2); auto.
        repeat (rewrite IHts2; auto).
        simpl.
        erewrite fold_left_reverse_input; eauto.

        induction ts0; auto.
        simpl.
        rewrite IHts0; auto.
    Qed.

    Lemma fold_left_pull_out_app:
      forall {T: Type}
        (op: T -> T -> T)
        (ts: list T)
        (OP_COMMUT: forall t1 t2, op t1 t2 = op t2 t1)
        (OP_ASSOC: forall t1 t2 t3, op (op t1 t2) t3 = op t1 (op t2 t3))
        (t t0: T),
        fold_left op (t :: ts) t0 = op t (fold_left op ts t0).
    Proof.
      intros until ts.
      induction ts.
      - simpl; auto.
      - intros.
        replace (t0 :: a :: ts) with ([t0;a] ++ ts); auto.
        erewrite fold_left_reverse_input; eauto.
        replace (ts ++ [t0; a]) with ((ts++ [t0]) ++ [a]); eauto.
        erewrite fold_left_nest_app; eauto.
        erewrite fold_left_reverse_input; eauto.

        assert (forall (ls: list T) (l0 l1: T), (ls ++ [l0]) ++ [l1] = ls ++ [l0;l1]).
        intros until ls; induction ls; simpl; auto.
        rewrite H; auto.
    Qed.


      

    (** getScopDomain commutes with unionPoly in a cons **)
    Lemma getScopDomain_cons: forall (ss: ScopStmt) (lss: list ScopStmt),
      getScopDomain ({| scopStmts := ss :: lss |}) =
      P.unionPoly 
        (scopStmtDomain ss)
        (getScopDomain {| scopStmts := lss |}).
    Proof.
      intros.
      unfold getScopDomain.
      Opaque fold_left.
      simpl.
      generalize (map scopStmtDomain lss) as ds.
      generalize (scopStmtDomain ss) as d.
      clear ss.
      clear lss.
      intros.
      erewrite fold_left_pull_out_app; eauto with proofdb.
    Qed.

      Hint Extern 0 (getScopDomain {| scopStmts := ?S :: ?SS |}) =>
      rewrite (getScopDomain_cons S SS): proofdb.

    Hint Resolve getScopDomain_cons: proofdb.
    Hint Rewrite getScopDomain_cons: proofdb.
    
    (* Execute from the begining viv to the end viv INCLUSIVE!! *)
    Inductive exec_scop_from_lexmin:
      P.ParamsT
      -> ScopEnvironment
      -> viv (**r begin VIV, inclusive *)
      -> Memory
      -> Scop
      -> Memory
      -> viv (**r end VIV, inclusive *)
      -> Prop :=
    | exec_scop_begin:
        forall 
          (se: ScopEnvironment)
          (initmem mem: Memory)
          (scop: Scop)
          (params: P.ParamsT)
          (vivmin: viv)
          (VIVMIN: vivmin = (P.getLexminPoint params (getScopDomain scop)))
          (EXEC_SCOP_AT_POINT: exec_scop_at_point params se vivmin initmem scop mem),
          exec_scop_from_lexmin params
                                se
                                vivmin
                                initmem
                                scop
                                initmem
                                vivmin
    | exec_scop_middle:
        forall (initmem mem1 mem2: Memory)
          (scop: Scop)
          (params: P.ParamsT)
          (se: ScopEnvironment)
          (vivbegin vivprev vivcur: viv)
          (CUR: Some vivcur = P.getLexNextPoint params (getScopDomain scop) vivprev)
          (EXEC_SCOP_TILL: exec_scop_from_lexmin params se vivbegin initmem scop mem1  vivprev)
          (EXEC_SCOP_AT_POINT: exec_scop_at_point params se vivcur mem1 scop mem2),
          exec_scop_from_lexmin params se vivbegin initmem scop mem2 vivcur.

    Definition initScopEnvironment : ScopEnvironment := ZMap.init None.
    Definition exec_scop (params: P.ParamsT)
               (initmem: Memory)
               (scop: Scop)
               (finalmem: Memory): Prop :=
      exec_scop_from_lexmin params
                            initScopEnvironment
                            (P.getLexminPoint params (getScopDomain scop))
                            initmem
                            scop
                            finalmem
                            (P.getLexmaxPoint params (getScopDomain scop)).
  End EVALUATION.


  (** *Section about writes *)
  Section WRITES.

    
    (** **Define what it means for a memory access to not write to memory *)
    (* 
    Inductive MAStoreNoWrite:
      P.ParamsT
      -> VIVSpace
      -> MemoryAccess
      -> ChunkNum
      -> list Z
      -> Prop :=
    | mkMAStoreNoWrite: forall
        (params: P.ParamsT)
        (domain: VIVSpace)
        (accessfn: AccessFunction)
        (needlechunk: ChunkNum)
        (ssv: ScopStoreValue)
        (viv: P.PointT)
        (needleix: list Z)
        (VIV_IN_DOMAIN: P.isPointInPoly viv domain = false)
        (VIV_AT_ACCESSFN: evalAccessFunction params accessfn viv = needleix),
        MAStoreNoWrite
          params
          domain
          (MAStore needlechunk accessfn ssv)
          needlechunk
          needleix.
    *)

    (** **Computational version of the write*)
    Definition MAWriteb
               (params: P.ParamsT)
               (domain: VIVSpace)
               (needlechunk: ChunkNum)
               (needleix: list Z)
               (memacc: MemoryAccess)
      : bool :=
      match memacc with
      | MAStore chunk accessfn _ =>
        Z.eqb needlechunk chunk && P.isPointInPoly
                             (P.invertEvalAffineFn params accessfn needleix) (domain)
      | _ => false
      end.

    Lemma MAWriteb_smaller_domain: forall
               (params: P.ParamsT)
               (larger smaller: VIVSpace)
               (SUBSET: P.isPolySubset smaller larger = true)
               (needlechunk: ChunkNum)
               (needleix: list Z)
               (memacc: MemoryAccess)
               (WRITE: MAWriteb params larger needlechunk needleix memacc = false),
               MAWriteb params smaller needlechunk needleix memacc = false.
    Proof.
      intros.
      destruct memacc;
        simpl in *; auto.

      (* MAStore *)
      simpl in *.
      rewrite andb_false_iff in *.

      destruct WRITE as [CHUNK | POINTINPOLY]; auto.
      right.
      eapply P.pointInSubsetPoly_false; eauto.
    Qed.
    
    (** **TODO: SSReflect MAStoreWrite, MAStoreNoWrite, and Mhere **)

    (** **Extension of MemoryAccessWritesmemoryatix to statements *)
    Definition scopStmtWriteb
               (params: P.ParamsT)
               (needlechunk: ChunkNum)
               (needleix: list Z)
               (stmt: ScopStmt) : bool :=
      existsb (MAWriteb
                 params
                 (scopStmtDomain stmt)
                 needlechunk needleix)
              (scopStmtMemAccesses stmt).


      
    (** Extension of MAWrites to scops *)
    Definition scopWriteb
               (params: P.ParamsT)
               (needlechunk: ChunkNum)
               (needleix: list Z)
               (scop: Scop): bool :=
      existsb (scopStmtWriteb params needlechunk needleix) (scopStmts scop).

    
    Lemma scopWriteb_unchanged_on_sorting:
      forall (params: P.ParamsT)
        (chunk: ChunkNum)
        (ix: list Z)
        (scop: Scop)
        (b: bool)
        (viv: viv)
        (scopWriteB: scopWriteb params chunk ix scop = b),
        scopWriteb params chunk ix
                   {| scopStmts := sortStmtsBySchedDescend
                                     params
                                     viv
                                     (scopStmts scop)
                   |} = b.
    Proof.
    Admitted.

    

    
    (** **If the point of access is not written by the memory access, then the memory access does not change that location *)
    Lemma point_not_in_memacc_implies_value_unchanged:
      forall (memacc: MemoryAccess)
        (domain: VIVSpace)
        (initmem finalmem: Memory)
        (params: P.ParamsT)
        (se: ScopEnvironment)
        (viv: viv)
        (PT_IN_DOMAIN: P.isPointInPoly viv domain = true)
        (EXECMA: exec_memory_access params se viv initmem memacc finalmem)
        (chunk: ChunkNum)
        (ix: list Z)
        (POINT_NOT_IN_POLY: MAWriteb params domain chunk ix memacc = false),
        loadMemory chunk ix finalmem = loadMemory chunk ix initmem.
    Proof.
      intros.
      induction EXECMA.
      - (* Execute store *)
        assert (CHUNK_CASES: {chunk = chunk0} + {chunk <> chunk0}). auto.
        unfold MAWriteb in POINT_NOT_IN_POLY.
        destruct CHUNK_CASES eqn:CASES ; auto; subst; auto.

        (* TODO: figure out how to proof automae this *)
        replace (chunk0 =? chunk0) with true in *; try (rewrite Z.eqb_refl; auto).

        simpl in POINT_NOT_IN_POLY.

        assert (IXCASES: {ix =  (evalAccessFunction params accessfn viv0)} + 
                         {ix <>  (evalAccessFunction params accessfn viv0)}). auto.

        destruct IXCASES; auto; subst.
        replace (P.invertEvalAffineFn params accessfn (evalAccessFunction params accessfn viv0))
          with viv0 in POINT_NOT_IN_POLY; auto with proofdb; try congruence.
    Qed.

    Hint Resolve point_not_in_memacc_implies_value_unchanged: proofdb.


    (** A point not in the domain of the scop statement is not written to *)
    Lemma point_not_in_scop_stmt_implies_value_unchanged:
      forall (stmt: ScopStmt)
        (initmem finalmem: Memory)
        (params: P.ParamsT)
        (se: ScopEnvironment)
        (viv: viv)
        (EXECSTMT: exec_scop_stmt params se viv initmem stmt finalmem)
        (chunk: ChunkNum)
        (ix: list Z)
        (POINT_NOT_IN_POLY: scopStmtWriteb params chunk ix stmt = false),
        loadMemory chunk ix finalmem = loadMemory chunk ix initmem.
    Proof.
      intros.
      induction EXECSTMT; auto.

      unfold scopStmtWriteb in *.
      simpl in *.

      assert (POINT_NOT_IN_POLY_CONJ: MAWriteb params domain chunk ix ma = false /\
                                       existsb (MAWriteb params domain chunk ix) mas = false).
      apply orb_false_elim; auto.

      destruct POINT_NOT_IN_POLY_CONJ as [P_NOT_IN_CUR_WRITE  P_NOT_IN_OTHER_WRITES].

      assert (MEMSTMT_EQ_INITMEM:
                loadMemory chunk ix memstmt = loadMemory chunk ix initmem); auto.
      assert (MEMSTMT_EQ_MEMNEW:
                loadMemory chunk ix memnew = loadMemory chunk ix memstmt).
      eauto with proofdb.

      congruence.
    Qed.

    Hint Resolve point_not_in_scop_stmt_implies_value_unchanged: proofdb.

    
    Lemma point_not_in_write_polyhedra_for_scop_at_point_sorted_stmts_implies_value_unchanged:
      forall (scop: Scop)
        (initmem finalmem: Memory)
        (params: P.ParamsT)
        (se: ScopEnvironment)
        (viv: viv)
        (EXECSCOPATPOINT: exec_scop_at_point_sorted_stmts params se viv initmem scop finalmem)
        (chunk: ChunkNum)
        (ix: list Z)
        (POINT_NOT_IN_POLY: scopWriteb params chunk ix scop = false),
        loadMemory chunk ix finalmem = loadMemory chunk ix initmem.
    Proof.
      intros.
      induction EXECSCOPATPOINT; auto.
      unfold scopWriteb in *; simpl in *.
      
      assert (POINT_NOT_IN_POLY_CONJ:
                scopStmtWriteb params chunk  ix curstmt = false /\
                existsb (scopStmtWriteb params chunk ix) prevstmts = false).
      auto with list.

      
      destruct POINT_NOT_IN_POLY_CONJ as [P_NOT_IN_CUR_STMT  P_NOT_IN_OTHER_STMTS].

      assert (MEMSTMT_EQ_INITMEM:
                loadMemory chunk ix mem2 = loadMemory chunk ix mem1).
      eapply point_not_in_scop_stmt_implies_value_unchanged; eauto.
      
      assert (MEMSTMT_EQ_MEMNEW:
                loadMemory chunk ix mem1 = loadMemory chunk ix initmem).
      eapply IHEXECSCOPATPOINT. eauto with proofdb.
      congruence.
    Qed.

    
    Hint Resolve point_not_in_write_polyhedra_for_scop_at_point_sorted_stmts_implies_value_unchanged: proofdb.

    Lemma point_not_in_write_polyhedra_for_scop_at_point_implies_value_unchanged:
      forall (scop: Scop)
        (initmem finalmem: Memory)
        (params: P.ParamsT)
        (se: ScopEnvironment)
        (viv: viv)
        (EXECSCOPATPOINT: exec_scop_at_point params se viv initmem scop finalmem)
        (chunk: ChunkNum)
        (ix: list Z)
        (POINT_NOT_IN_POLY: scopWriteb params chunk ix scop = false),
        loadMemory chunk ix finalmem = loadMemory chunk ix initmem.
    Proof.
      intros.
      unfold exec_scop_at_point in *.
      eapply point_not_in_write_polyhedra_for_scop_at_point_sorted_stmts_implies_value_unchanged.
      exact EXECSCOPATPOINT.
      apply scopWriteb_unchanged_on_sorting; auto.
    Qed.
         
    Hint Resolve point_not_in_write_polyhedra_for_scop_at_point_implies_value_unchanged: proofdb.

      

    

    Lemma point_not_in_write_polyhedra_implies_value_unchanged:
      forall (scop: Scop)
        (initmem finalmem: Memory)
        (params: P.ParamsT)
        (EXECSCOP: exec_scop params initmem scop finalmem)
        (chunk: ChunkNum)
        (ix: list Z)
        (POINT_NOT_IN_POLY: scopWriteb params chunk ix scop = false),
        loadMemory chunk ix finalmem = loadMemory chunk ix initmem.
    Proof.
      intros until params. intro.
      induction EXECSCOP ;  auto.
      intros.

      assert (MEM1_EQ_MEM: loadMemory chunk ix mem1 = loadMemory chunk ix initmem). auto.

      assert (MEM2_EQ_MEM1: loadMemory chunk ix mem2 = loadMemory chunk ix mem1).
      eauto with proofdb.

      congruence.
    Qed.

    
    Hint Resolve point_not_in_write_polyhedra_implies_value_unchanged: proofdb.
    Hint Rewrite point_not_in_write_polyhedra_implies_value_unchanged: proofdb.


    
  End WRITES.


  (** *Section to reason about last writes *)
  Section LASTWRITE.

    (** **The definition of a last write in a scop *)
        
    (* Is the last write in a scop for this domain *)
    Record IsLastWrite
           (params: P.ParamsT)
           (domain: VIVSpace)
           (lwma: MemoryAccess)
           (lwchunk: ChunkNum)
           (lwviv: P.PointT)
           (lwix: list Z) : Prop :=
      mkLastWrite {
          lastWriteVivInDomain: P.isPointInPoly lwviv domain = true;
          lastWriteVivIx: lwix = evalAccessFunction params (getMAAccessFunction lwma) lwviv;
          lastWriteWrite: MAWriteb params domain lwchunk lwix lwma = true;
          lastWriteLast:
            forall (macur: MemoryAccess)
              (vivcur: P.PointT)
              (VIVCUR_IX: lwix = evalAccessFunction params (getMAAccessFunction macur) vivcur)
              (VIVLW_LT_VIVCUR: P.isLexLT  lwviv vivcur = Some true),
              MAWriteb params domain lwchunk lwix macur = false;
        }.

    Hint Constructors IsLastWrite: proofdb.
    Hint Resolve lastWriteVivInDomain: proofdb.
    Hint Resolve lastWriteVivIx: proofdb.
    Hint Resolve lastWriteWrite: proofdb.
    Hint Resolve lastWriteLast: proofdb.

      

    (** **Last write is decidable *)
    Lemma IsLastWriteDecidable: forall(params: P.ParamsT)
                                 (domain: VIVSpace)
        (ma: MemoryAccess)
        (chunk: ChunkNum)
        (ix: list Z)
        (viv: P.PointT),
        {IsLastWrite params domain ma chunk viv ix} +
        {~IsLastWrite params domain ma chunk viv ix}.
    Proof.
      intros.
    Admitted.

    Hint Resolve IsLastWriteDecidable: proofdb.
    Hint Rewrite IsLastWriteDecidable: proofdb.

    (* A last write in a larger domain continues to be a last write in a smaller
    domain *)
    Lemma LastWrite_domain_inclusive: forall
           (params: P.ParamsT)
           (largerdomain smallerdomain: VIVSpace)
           (ma: MemoryAccess)
           (lwchunk: ChunkNum)
           (lwviv: P.PointT)
           (lwix: list Z)
           (SMALLERDOMAIN: P.isPolySubset smallerdomain largerdomain = true)
           (LASTWRITE: IsLastWrite params largerdomain ma lwchunk lwviv lwix),
           IsLastWrite params smallerdomain ma lwchunk lwviv lwix.
    Proof.
      intros.
      destruct LASTWRITE.
      
      constructor; simpl; auto.
      - eapply P.PointInSubsetPoly_spec; eauto.
      - unfold MAWriteb in *.
        destruct ma; auto.
        admit.
      -  intros.
         assert (WRITEB_LARGER_DOMAIN:
                   MAWriteb params largerdomain lwchunk lwix macur = false).
         eapply lastWriteLast0; eauto.
         (* TODO: theorem to convert larger domain to smaller domain *)
         eapply MAWriteb_smaller_domain.

    Admitted.
     
    Hint Resolve LastWrite_domain_inclusive: proofdb.
    Hint Rewrite IsLastWriteDecidable: proofdb.

    (** Defines a list of memory accesses that do not alias in a domain *)
    (** NOTE THAT THIS DEFINITION IGNORES READ / WRITE DISTINCTIONS! This needs
    to be patched up in fugure *)
    Definition noWritesAliasInDomain (domain: VIVSpace) (mas: list MemoryAccess) : Prop :=
      forall ma1 ma2 viv params
        (VIV_IN_DOMAIN: P.isPointInPoly viv domain = true)
        (MA1_IN_STMT: List.In ma1 mas)
        (MA2_IN_STMT: List.In ma2 mas)
        (MA1_MA2_ALIAS:
           evalAccessFunction params (getMAAccessFunction ma1) viv =
           evalAccessFunction params (getMAAccessFunction ma2) viv),
        ma1 = ma2.

    (** NoWritesAlias on a larger list continues to hold on a sublist *)
    Lemma noWritesAlias_cons_destruct:
      forall (domain: VIVSpace)
        (mas: list MemoryAccess)
        (ma: MemoryAccess)
        (NOWRITESALIAS: noWritesAliasInDomain domain (ma::mas)),
        noWritesAliasInDomain domain mas.
    Proof.
      intros.
      unfold noWritesAliasInDomain in *.
      intros.
      eapply NOWRITESALIAS; eauto; repeat (apply List.in_cons; auto).
    Qed.

    Hint Resolve noWritesAlias_cons_destruct: proofdb.


    

    (** A ScopStmt is valid if none of the writes *in* a scop stmt can alias *)
    Definition ScopStmt_noWritesAlias (stmt: ScopStmt) : Prop :=
      noWritesAliasInDomain (scopStmtDomain stmt)
                            (scopStmtMemAccesses stmt).


    Hint Unfold ScopStmt_noWritesAlias: proofdb.

        


    
    (** No statements in the scop have write aliases between them *)
    Definition scopNoWritesAlias (scop: Scop) :=
      forall (stmt: ScopStmt)
        (STMT_IN_SCOP: List.In stmt (scopStmts scop)),
        ScopStmt_noWritesAlias stmt.

    Lemma scopNoWritesAlias_inclusive_on_subset:
      forall (stmt: ScopStmt)
        (stmts: list ScopStmt)
        (NOWRITES_LARGER: scopNoWritesAlias (mkScop (stmt::stmts))),
        scopNoWritesAlias (mkScop stmts).
    Proof.
      intros.
      unfold scopNoWritesAlias in *.
      intros.
      apply NOWRITES_LARGER.
      simpl. auto.
    Qed.

    
    Lemma LastWriteImposesMemoryValueAtLastWriteIx_exec_scop_at_point_sorted_stmts:
      
      forall (params: P.ParamsT)
        (se: ScopEnvironment)
        (initmem finalmem: Memory)
        (scop: Scop)
        (vivlw: viv)
        (EXEC_SCOP_AT_POINT: exec_scop_at_point_sorted_stmts
                               params
                               se
                               vivlw
                               initmem
                               scop
                               finalmem)
        (lwaccessfn: AccessFunction)
        (lwchunk: ChunkNum)
        (lwix: list Z)
        (lwssv: ScopStoreValue)
        (lwssvval: Value)
        (EVAL_LWSSV: exec_scop_store_value params se vivlw lwssv lwssvval)
        (LASTWRITE: IsLastWrite params
                                (P.getLexLeqPoly params (getScopDomain scop) vivlw)
                                (MAStore lwchunk lwaccessfn lwssv)
                                lwchunk
                                vivlw
                                lwix)
        (LASTWRITE_IN_SCOP: List.In (MAStore lwchunk lwaccessfn lwssv)
                                    (getScopMemoryAccesses scop))
      (NOWRITEALIAS: scopNoWritesAlias scop),
        loadMemory lwchunk lwix finalmem = Some lwssvval.
    Proof.
      intros until 1.
      induction EXEC_SCOP_AT_POINT.

      - intros.
        simpl in LASTWRITE_IN_SCOP.
        contradiction.

      - intros.
        unfold getScopMemoryAccesses in LASTWRITE_IN_SCOP.
        simpl in *.
        rewrite List.in_app_iff in LASTWRITE_IN_SCOP.
        destruct (LASTWRITE_IN_SCOP) as [LASTWRITE_IN_CUR_STMT |
                                         LASTWRITE_IN_PREV_STMTS].

        + (* We are executing the current stmt *)
          eapply LastWriteImposesMemoryValueAtLastWriteIx_scop_stmt;
            eauto.
          eapply LastWrite_domain_inclusive with
              (largerdomain := P.getLexLeqPoly
                                 params 
                                 (getScopDomain {| scopStmts := curstmt:: prevstmts |})
                                 viv0); auto.
          (** TODO: proof automation should have done this **)
          rewrite getScopDomain_cons.
          apply P.getLexLeqPoly_proper_wrt_subset.
          apply P.subset_of_union.
          unfold scopNoWritesAlias in NOWRITEALIAS.
          apply NOWRITEALIAS; simpl; auto.

          
        + (** Lastwrite was in the other statements *)
          assert (MEM2: loadMemory lwchunk lwix mem2 =
                        loadMemory lwchunk lwix mem1).
          admit.

          assert (MEM1: loadMemory lwchunk lwix mem1 = Some lwssvval).
          eapply IHEXEC_SCOP_AT_POINT; eauto.
          eapply LastWrite_domain_inclusive with
              (largerdomain := P.getLexLeqPoly
                                 params 
                                 (getScopDomain {| scopStmts := curstmt:: prevstmts |})
                                 viv0); auto.
          (** TODO: proof automation should have done this **)
          rewrite getScopDomain_cons.
          apply P.getLexLeqPoly_proper_wrt_subset.
          rewrite P.unionPoly_commutative.
          apply P.subset_of_union.
          eapply scopNoWritesAlias_inclusive_on_subset; eauto.

          (** MEM1 and MEM2 *)
          congruence.
    Qed.



    
    Lemma LastWriteImposesMemoryValueAtLastWriteIx_exec_scop_at_point:
      forall (params: P.ParamsT)
        (se: ScopEnvironment)
        (initmem finalmem: Memory)
        (scop: Scop)
        (vivlw: viv)
        (EXEC_SCOP_AT_POINT: exec_scop_at_point params se vivlw initmem scop finalmem)
        (lwaccessfn: AccessFunction)
        (lwchunk: ChunkNum)
        (lwix: list Z)
        (lwssv: ScopStoreValue)
        (lwssvval: Value)
        (EVAL_LWSSV: exec_scop_store_value params se vivlw lwssv lwssvval)
        (LASTWRITE: IsLastWrite params
                                (P.getLexLeqPoly params (getScopDomain scop) vivlw)
                                (MAStore lwchunk lwaccessfn lwssv)
                                lwchunk
                                vivlw
                                lwix)
        (LASTWRITE_IN_SCOP: List.In (MAStore lwchunk lwaccessfn lwssv)
                                    (getScopMemoryAccesses scop))
      (NOWRITEALIAS: True),
        loadMemory lwchunk lwix finalmem = Some lwssvval.
    Proof.
      (* Use the version of sorted_stmts *)
    Qed.


      

    
    (** **Any write that runs after the last write (LEXCUR_GT_VIVLW) cannot modify the state of memory at the last write *)
    Lemma LastWriteImposesMemoryValue_exec_mem_access:
      forall (params: P.ParamsT)
        (se: ScopEnvironment)
        (vivcur: viv)
        (initmem finalmem: Memory)
        (macur: MemoryAccess)
        (domain: VIVSpace)
        (EXEC_MEM_ACCESS: exec_memory_access params se vivcur initmem macur finalmem)
        (VIVCUR_IN_DOMAIN: P.isPointInPoly vivcur domain = true)
        (vivlw: viv)
        (LEXCUR_GT_VIVLW: P.isLexGT vivcur vivlw = Some true)
        (lwaccessfn: AccessFunction)
        (lwchunk: ChunkNum)
        (lwix: list Z)
        (lwssv: ScopStoreValue)
        (LASTWRITE: IsLastWrite params
                                domain
                                (MAStore lwchunk lwaccessfn lwssv)
                                lwchunk vivlw lwix),
        loadMemory lwchunk lwix finalmem = loadMemory lwchunk lwix initmem.
    Proof.
      intros until 1.
      induction EXEC_MEM_ACCESS; auto.
      intros.
       (* cur > lw *)
        assert (CHUNK_CASES: {lwchunk = chunk} + {lwchunk <> chunk}); auto.
        destruct CHUNK_CASES as [EQ | NEQ]; eauto with proofdb.
        rewrite EQ in *. 

        assert (IX_CASES: {lwix = accessix} + {lwix <> accessix}); auto.
        destruct IX_CASES as [IXEQ | IXNEQ]; eauto with proofdb.

        (** From the fact that the write perfectly aliases, we can conclucde
      that this write does write into the last write ix *)
        assert (WRITE_IN_LW: MAWriteb params domain lwchunk lwix
                                      (MAStore lwchunk accessfn ssv)= true).
        subst.
        simpl.
        rewrite andb_true_intro; auto.
        split; eauto with proofdb.

        (* However, from the fact that we have a _last write_, and that vivcur > vivlw,
         this cannot happen! *)
        assert (WRITE_NOT_IN_LW: MAWriteb params domain lwchunk lwix
                                          (MAStore lwchunk accessfn ssv) = false).
        subst.
        eapply lastWriteLast; eauto with proofdb.
        (** TODO: this should automatically work, figure out why it is not *)
        eapply P.isLexLT_GT; auto.

        (* Boom *)
        assert (CONTRA: true = false); congruence.
    Qed.
                  

    Hint Resolve LastWriteImposesMemoryValue_exec_mem_access: proofdb.

    
    (** **Any stmt that runs after the last write cannot edit the last write value of memory **)
    Lemma LastWriteImposesMemoryValue_exec_scop_stmt:
      forall (params: P.ParamsT)
        (se: ScopEnvironment)
        (vivcur: viv)
        (initmem finalmem: Memory)
        (stmt: ScopStmt)
        (EXEC_SCOP_STMT: exec_scop_stmt params se vivcur initmem stmt finalmem)
        (vivlw: viv)
        (LEXCUR_GT_VIVLW: P.isLexGT vivcur vivlw = Some true)
        (lwaccessfn: AccessFunction)
        (lwchunk: ChunkNum)
        (lwix: list Z)
        (lwssv: ScopStoreValue)
        (LASTWRITE: IsLastWrite params (P.getLexLeqPoly params (scopStmtDomain stmt) vivcur)
                                (MAStore lwchunk lwaccessfn lwssv) lwchunk vivlw lwix),
        loadMemory lwchunk lwix finalmem = loadMemory lwchunk lwix initmem.
    Proof.
      intros until 1.
      induction EXEC_SCOP_STMT; auto.

      intros.

      assert (MEMSTMT: loadMemory lwchunk lwix memstmt =
                       loadMemory lwchunk lwix initmem).
      eapply IHEXEC_SCOP_STMT; eauto.


      assert (MEMNEW: loadMemory lwchunk lwix memnew =
                      loadMemory lwchunk lwix memstmt).
      eapply LastWriteImposesMemoryValue_exec_mem_access with
          (domain := (P.getLexLeqPoly params domain viv0)); try eassumption.
      eauto with proofdb.
      congruence.
    Qed.

    
    Hint Resolve LastWriteImposesMemoryValue_exec_scop_stmt: proofdb.

    
    (** **Executing the scop at any point after the last write cannot edit the last write value of memory **)
    (** TODO: we should be able to convert this repetition into some kind of "scheme" that lets us generalize results about memory accesses into those of scopStmt and ScopAtPoint. Think about this **)
    Lemma LastWriteImposesMemoryValue_exec_scop_at_point:
      forall (params: P.ParamsT)
        (se: ScopEnvironment)
        (vivcur: viv)
        (initmem finalmem: Memory)
        (scop: Scop)
        (EXEC_SCOP_AT_POINT: exec_scop_at_point params se vivcur initmem scop finalmem)
        (vivlw: viv)
        (LEXCUR_GT_VIVLW: P.isLexGT vivcur vivlw = Some true)
        (lwaccessfn: AccessFunction)
        (lwchunk: ChunkNum)
        (lwix: list Z)
        (lwssv: ScopStoreValue)
        (LASTWRITE: IsLastWrite params (P.getLexLeqPoly params (getScopDomain scop) vivcur) 
                                (MAStore lwchunk lwaccessfn lwssv) lwchunk vivlw lwix),
        loadMemory lwchunk lwix finalmem = loadMemory lwchunk lwix initmem.
    Proof.
      intros until 1.
      induction EXEC_SCOP_AT_POINT; auto.

      intros.
      rewrite getScopDomain_cons in *.

      assert (SUBSET1:
                
                P.isPolySubset (P.getLexLeqPoly params (scopStmtDomain stmt) viv0)
                               (P.getLexLeqPoly
                                  params
                                  (P.unionPoly
                                     (scopStmtDomain stmt)
                                     (getScopDomain {| scopStmts := stmts |})) viv0)
                = true).
      auto with proofdb.

      
      assert (SUBSET2:
                P.isPolySubset (P.getLexLeqPoly
                                  params (getScopDomain {| scopStmts := stmts |}) viv0)
                 (P.getLexLeqPoly params
                                  (P.unionPoly (scopStmtDomain stmt)
                                               (getScopDomain
                                                  {| scopStmts := stmts |})) viv0)
                = true).
      simpl.
      apply P.getLexLeqPoly_proper_wrt_subset.
      rewrite P.unionPoly_commutative.
      apply P.subset_of_union.
      

      assert (MEM2: loadMemory lwchunk lwix mem2 =
                       loadMemory lwchunk lwix mem1).
      eapply IHEXEC_SCOP_AT_POINT; try eassumption.
      eapply LastWrite_domain_inclusive; try eassumption.
      
                                       


      assert (MEM1: loadMemory lwchunk lwix mem1 =
                    loadMemory lwchunk lwix initmem).
      
      eapply LastWriteImposesMemoryValue_exec_scop_stmt; try eassumption.
      eapply LastWrite_domain_inclusive; try eassumption.

      congruence.
    Qed.

    
    Lemma LastWriteImposesMemoryValue_exec_scop:
      forall (params: P.ParamsT)
        (scop: Scop)
        (initmem finalmem: Memory)
        (se: ScopEnvironment)
        (vivstart vivend: viv)
        (EXECSCOP: exec_scop_from_lexmin params se vivstart initmem scop finalmem vivend)
        (lwchunk: ChunkNum)
        (lwix: list Z)
        (lwssv: ScopStoreValue)
        (lwaccessfn: AccessFunction)
        (vivlw: viv)
        (* We must have executed the last write to make this statement *)
        (VIVEND_GE_VIVLW: P.isLexGT vivend vivlw = Some true \/ vivend = vivlw)
        (LASTWRITE: IsLastWrite params (P.getLexLeqPoly params (getScopDomain scop) vivend) 
                                (MAStore lwchunk lwaccessfn lwssv) lwchunk vivlw lwix)
        (storeval: Value)
        (se: ScopEnvironment)
        (EXECWRITEVAL: exec_scop_store_value params se vivlw lwssv storeval),
        loadMemory lwchunk lwix finalmem = Some storeval.
    Proof.
      intros until 1.
      induction EXECSCOP.
        intros.

        (* the min point is greater than the last write,
        this is nonsense, so contradiction *)
          assert (VIVLW_IN_DOMAIN: 
                    P.isPointInPoly vivlw
                                    (P.getLexLeqPoly params (getScopDomain scop) vivmin) = true).
          eauto with proofdb.
          rewrite VIVMIN in VIVLW_IN_DOMAIN.

          assert (VIVLW_IN_VIVMIN_POLYHEDRA: 
                    P.isPointInPoly vivlw (P.pointToPoly vivmin) = true).
          rewrite VIVMIN.
          rewrite <- VIVLW_IN_DOMAIN.
          eauto with proofdb.

          assert (VIVLW_EQ_VIVMIN: vivlw = vivmin).
          eauto with proofdb.

          assert (CONTRA: P.isLexGT vivmin vivlw = Some false).
          rewrite VIVLW_EQ_VIVMIN.
          eauto with proofdb.
          congruence.

      - (* Second part of proof. *)
        intros.

        (* vivprev --(+1)--> vivcur *)
        (* vivlw ---(<)--> vivcur *)
        (* vivlw ---(<=)--> vivprev *)
        assert (VIVLW_VIVPREV_CASES: P.isLexLT vivlw vivprev = Some true \/ vivlw = vivprev).
        eapply P.isLexLT_next_implies_isLexLEQ_current; eauto.
        eapply P.isLexLT_GT.
        auto.


        destruct VIVLW_VIVPREV_CASES as [VIVLW_LT_PREV |
                                        VIVLW_EQ_PREV].
        + assert (MEM1: loadMemory lwchunk lwix mem1 = Some storeval).
          eapply IHEXECSCOP; try eassumption.
          eapply P.isLexLT_GT; eauto.
          admit.

          + 
        
        congruence.
    Qed.


      

    Lemma LastWriteImposesMemoryValue_exec_scop_from_lexmin:
      forall (params: P.ParamsT)
        (scop: Scop)
        (initmem finalmem: Memory)
        (se: ScopEnvironment)
        (lexstart lexcur: viv)
        (EXECSCOP: exec_scop_from_lexmin params se lexstart initmem scop finalmem lexcur)
        (stmt: ScopStmt)
        (chunk: ChunkNum)
        (ix: list Z)
        (accessfn: AccessFunction)
        (ssv: ScopStoreValue)
        (vivlw: viv)
        (* We must have executed the last write to make this statement *)
        (LEXCUR_GT_VIVLW: P.isLexGT lexstart vivlw = Some true)
        (LASTWRITE: IsLastWrite params scop stmt (MAStore chunk accessfn ssv) chunk vivlw ix)
        (storeval: Value)
        (se: ScopEnvironment)
        (EXECWRITEVAL: exec_scop_store_value params se vivlw ssv storeval),
        loadMemory chunk ix finalmem = Some storeval.
    Proof.
      intros until 1.
      
      induction EXECSCOP.
      - (* In the beginning, we would not have executed the last write, so this is absurd *)
        intros. subst.
        assert (CONTRA: true = false).
        eapply P.isLexGT_of_lexmin_is_always_false; eauto with proofdb.
        congruence.
        
      - intros.
        assert (MEM1: loadMemory chunk ix mem1 = Some storeval).
        eapply IHEXECSCOP; eauto.


        assert (MEM2: loadMemory chunk ix mem2 = loadMemory chunk ix mem1).

        congruence.
    Qed.


    

    (** *If we have a last write, then the value in memory is the value written by the last write *)
    Theorem LastWriteImposesMemoryValue:
      forall (params: P.ParamsT)
        (scop: Scop)
        (initmem finalmem: Memory)
        (EXECSCOP: exec_scop params initmem scop finalmem)
        (stmt: ScopStmt)
        (chunk: ChunkNum)
        (ix: list Z)
        (accessfn: AccessFunction)
        (ssv: ScopStoreValue)
        (viv: viv)
        (VIV_WITNESS: evalAccessFunction params  accessfn viv = ix)
        (LASTWRITE: IsLastWrite params scop stmt (MAStore chunk accessfn ssv) chunk viv ix)
        (storeval: Value)
        (se: ScopEnvironment)
        (EXECWRITEVAL: exec_scop_store_value params se viv ssv storeval),
        loadMemory chunk ix finalmem = Some storeval.
    Proof.
      (** Show that we can split scop execution into two parts: The first part that is
       *till* the last write, and the second part that is *after* the last write *)
      
      intros until 1.
      induction EXECSCOP; auto.

      - (* We are starting execution. *)
        intros.
        inversion EXECWRITEVAL; subst.

      (** Show that on the part *till* the last write, the last write value
          is the value of the scop execution *)

    Qed.
        

      
    
  End LASTWRITE.

  
  Hint Resolve LastWriteImposesMemoryValue: proofdb.
  Hint Rewrite LastWriteImposesMemoryValue: proofdb.

  (** *Schedule properties and interactions with last writes *)
  Section SCHEDULE.
    Record validSchedule (scop: Scop) (schedule: Schedule) (scop': Scop) : Prop :=
      mkValidSchedule {
          NEWSCOP_IS_SCHEDULED_OLDSCOP: (scop' = applyScheduleToScop schedule scop);
          RESPECTSRAW: scheduleRespectsRAW schedule scop;
          RESPECTSWAW: scheduleRespectsWAW schedule scop;
        }.
    
    (** Given a point in a write polyhedra, show that there must exist
    a corresponding write in the scop *)
    Lemma point_in_write_polyhedra_implies_last_write_exists:
      forall (params: P.ParamsT)
        (scop: Scop)
        (chunk: ChunkNum)
        (ix: list Z)
        (POINT_IN_POLY: scopWriteb params chunk ix scop = true),
      exists stmt accessfn ssv viv,
        List.In stmt (scopStmts scop) /\
        List.In (MAStore chunk accessfn ssv) (scopStmtMemAccesses stmt) /\
        (evalAccessFunction params accessfn viv = ix) /\
        P.isPointInPoly viv (getScopDomain scop) = true /\
        IsLastWrite params scop stmt (MAStore chunk accessfn ssv) chunk viv ix.
    Proof.
    Admitted.
      
          
    Hint Resolve point_in_write_polyhedra_implies_last_write_exists: proofdb.
    Hint Rewrite point_in_write_polyhedra_implies_last_write_exists: proofdb.


    (** a valid schedule preserves inclusion and exclusion into the write
    polyhedra **)
    Lemma valid_schedule_preserves_write_polyhedra_non_containment:
      forall (params: P.ParamsT)
        (scop scop': Scop)
        (schedule: Schedule)
        (VALIDSCHEDULE: validSchedule scop schedule scop')
        (chunk: ChunkNum)
        (ix: list Z)
        (NOTINPOLY: scopWriteb params chunk ix scop = false),
        scopWriteb params chunk ix scop' = false.
    Proof.
    Admitted.

    Hint Resolve valid_schedule_preserves_write_polyhedra_non_containment: proofdb.
    Hint Rewrite valid_schedule_preserves_write_polyhedra_non_containment: proofdb.

    (** **Last write in SCOP => last write in SCOP'*)
    Lemma transport_write_along_schedule:
      forall (params: P.ParamsT)
        (scop scop': Scop)
        (stmt: ScopStmt)
        (schedule: Schedule)
        (VALIDSCHEDULE: validSchedule scop schedule scop')
        (chunk: ChunkNum)
        (ix: list Z)
        accessfn
        ssv
        viv
        (STMT_IN_SCOP: List.In stmt (scopStmts scop))
        (STORE_IN_STMT: List.In (MAStore chunk accessfn ssv) (scopStmtMemAccesses stmt))
        (ACCESSFN: evalAccessFunction params accessfn viv = ix)
        (VIV_IN_SCOP: P.isPointInPoly viv (getScopDomain scop) = true)
        (LASTWRITE: IsLastWrite params scop stmt (MAStore chunk accessfn ssv) chunk viv ix),
        IsLastWrite params scop'
                    (applyScheduleToScopStmt schedule stmt)
                    (MAStore chunk accessfn ssv) chunk viv ix.
    Proof.
    Admitted.

  End SCHEDULE.

  (** *Section that formalises the proof *)
  Section PROOF.


    Definition MemExtesionallyEqual (mem1 mem2: Memory): Prop :=
      forall (chunk: ChunkNum) (ix: list Z),
        loadMemory chunk ix mem1 = loadMemory chunk ix mem2.




    (** **Stores of reads are disallowed currrently **)
    Axiom NoSSVLoadedVal: forall (stmt: ScopStmt) (scop: Scop)
            (chunk: ChunkNum)
            (accessfn: AccessFunction)
            (ident: ScopLoadIdent),
        In stmt (scopStmts scop)
        -> In (MAStore chunk accessfn (SSVLoadedVal ident)) (scopStmtMemAccesses stmt)
        -> False.
        

    Hint Resolve transport_write_along_schedule: proofdb.
    Hint Rewrite transport_write_along_schedule: proofdb.

    Theorem valid_schedule_preserves_semantics:
      forall (scop scop': Scop)
        (schedule: Schedule)
        (VALIDSCHEDULE: validSchedule scop schedule scop')
        (initmem finalmem finalmem': Memory)
        (params: P.ParamsT)
        (EXECSCOP: exec_scop params initmem scop finalmem)
        (EXECSCOP': exec_scop params initmem scop' finalmem'),
        MemExtesionallyEqual finalmem finalmem'.
    Proof.
      unfold MemExtesionallyEqual.
      intros.

      destruct (scopWriteb  params chunk ix scop) eqn: POINTINPOLY_CASES.
      - (* write in poly *)
        rename POINTINPOLY_CASES into POINT_IN_POLY.

        assert (WRITEINPOLY: 
            exists stmt accessfn ssv viv,
              List.In stmt (scopStmts scop) /\
              List.In (MAStore chunk accessfn ssv) (scopStmtMemAccesses stmt)  /\
              (evalAccessFunction params accessfn viv = ix) /\
              P.isPointInPoly viv (getScopDomain scop) = true /\
              IsLastWrite params scop stmt (MAStore chunk accessfn ssv) chunk viv ix).
        eauto with proofdb.
        

        destruct WRITEINPOLY as (stmt & accessfn & ssv & viv &
                                 STMT_IN_SCOP & MEM_IN_STMT & EVALACCESSFN &
                                 VIV_IN_DOMAIN & LASTWRITE).

        assert (LASTWRITE_SCOP': 
                  IsLastWrite params
                              scop'
                              (applyScheduleToScopStmt schedule stmt)
                              (MAStore chunk accessfn ssv)
                              chunk
                              viv
                              ix).
        eapply transport_write_along_schedule; try eassumption.

        induction ssv.
        + (* Pure Function of indvars *)
          assert (execSSV: forall se, exec_scop_store_value
                                   params
                                   se
                                   viv
                                   (SSVIndvarFn indvarfn)
                                   (indvarfn (P.evalPoint params viv))).
          intros.
          constructor; auto.

          assert (MEMWRITE: loadMemory chunk ix finalmem =
                            Some (indvarfn (P.evalPoint params viv))).
          eapply LastWriteImposesMemoryValue; eauto.

          assert (MEM'WRITE: loadMemory chunk ix finalmem' =
                 Some (indvarfn (P.evalPoint params viv))).
          eapply LastWriteImposesMemoryValue; eauto.
          congruence.

        + (* Function of memory *)
          assert (AXIOM_CONTRA: False).
          eapply NoSSVLoadedVal; eassumption.
          contradiction.
        
        
      - rename POINTINPOLY_CASES into POINT_NOT_IN_POLY.
        assert (POINT_NOT_IN_POLY': scopWriteb params chunk ix scop' = false).
        eauto with proofdb.

        (* Write not in poly *)
        assert (LOAD_FINALMEM: loadMemory chunk ix finalmem  = loadMemory chunk ix initmem).
        eapply point_not_in_write_polyhedra_implies_value_unchanged; eauto.
        
        assert (LOAD_FINALMEM': loadMemory chunk ix finalmem'  = loadMemory chunk ix initmem).
        eapply point_not_in_write_polyhedra_implies_value_unchanged; eauto.

        congruence.

        (** TODO: I need to track the scopEnvironment in some lemma. This
        scopEnvironment is never instantiated in execSSV. Somewhere, some theorem should
        refer to a specific environment **)
        Unshelve.
        exact initScopEnvironment.
        exact initScopEnvironment.
    Qed.
  End PROOF.
End SCOP.
