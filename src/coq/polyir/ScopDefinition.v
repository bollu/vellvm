Require Import Omega.
Require Import Nat.
Require Import ZArith.
Require Import Ring.
Require Import List.
Require Import Ncring.
Require Import Ring_tac.
Require Import FunctionalExtensionality.
Require Import Maps.

Require Import Vellvm.Crush.
Require Import Vellvm.polyir.PolyIRUtil.
Require Import Vellvm.polyir.PolyIRDefinition.

(** Import VPL for polyhedral goodness **)
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
Qed.
Hint Resolve ix_eq_decidable.

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
  Parameter evalPoint: ParamsT -> PointT -> (list Z).

  
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
  Parameter isPointInPolyProp: PointT -> PolyT -> Prop.


  
  (** Returns whether one point is lex < than the other *)
  Parameter isLexLT: PointT -> PointT -> option (bool).

  
  (** Returns whether one point is lex > than the other *)
  Parameter isLexGT: PointT -> PointT -> option (bool).

  Axiom isLexLT_GT: forall (a b :PointT), isLexLT a b = Some true <-> isLexGT b a = Some true.


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

  (** Get the polyhedra of points which are lex <  the given point *)
  Parameter getLexLtPoly: ParamsT -> PolyT -> PointT -> PolyT.

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
           (TP_LEX_ORDERED: isLexLT tp1 tp2 = Some true),
      arePointsRelated tp1 tp2 dep = true.

  (** A function to compute the dependence polyhedra of two relations *)
  Parameter getDependenceRelation: AffineRelT -> AffineRelT -> option AffineRelT.


  (** An induction principle on all points that are lex smaller tha a
  given point in the polyhedra *)
  Axiom polyhedra_ind_lex_smaller_points: forall
      (params: ParamsT) (P: PointT -> Prop) (Q: PolyT -> Prop) (fullpoly: PolyT),
      (Q emptyPoly) -> (forall (curpoint: PointT),
                          Q (getLexLtPoly params fullpoly curpoint) -> P curpoint ->
                          Q (getLexLeqPoly params fullpoly curpoint)) ->
      Q fullpoly.

  
  (** The lex min point is not lex greater than any point *)
  Axiom isLexGT_of_lexmin_is_always_false:
    forall (params: ParamsT) (poly: PolyT) (pt: PointT) (b: bool),
    isPointInPoly pt poly = true ->
    isLexGT (getLexminPoint params poly) pt = Some b ->
    b = false.
  
  
End POLYHEDRAL_THEORY.

Module SCOP(P: POLYHEDRAL_THEORY).

  (* define semantics for evaluating a schedule *)
  (* 
    Fixpoint evalMultidimAffineExpr (env: Environment)
             (s: MultidimAffineExpr):  option (list Value) :=
      option_traverse (List.map (evalAffineExprFn env) s).
   *)

  Definition AccessFunction := P.AffineFnT. (**r Access function to model where to read or write from *)

  
  (** The identifier of some loaded value, to be stored in the abstract
    scop environment **)
  Definition ScopLoadIdent := Z.

  (** Mapping from load identifiers to values *)
  Definition ScopEnvironment := ZMap.t (option Z).

  (** The things that a store expression is allowed to store
   A[i, j, k, ..] = <ScopStore>*)
  Inductive ScopStoreValue :=
  | SSVIndvarFn (indvarfn: list Z -> Z): ScopStoreValue (**r function of indvars *)
  | SSVLoadedVal (itostore: ScopLoadIdent): ScopStoreValue (**r store some loaded value *)
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


  Definition Domain := P.PolyT.
  Record ScopStmt :=
    mkScopStmt {
        scopStmtDomain: Domain; (**r The domain of the scop statement. That is, interpreted as
          0 <= <indvars[i]> <= <domain[i]> *)
        scopStmtSchedule : P.AffineFnT; (**r Function from the canonical induction variables to the schedule
         timepoint.  *)
        scopStmtMemAccesses: list MemoryAccess (**r List of memory accesses *)
      }.

  Record Scop :=
    mkScop {
        scopStmts : list ScopStmt; (**r The statements in this scop *)
      }.

  (** Get the memory accesses in a scop *)
  Definition getScopMemoryAccessses (scop: Scop): list MemoryAccess :=
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
      scopStmtSchedule := P.composeAffineFunction (scopStmtSchedule ss) schedule;
      scopStmtMemAccesses := scopStmtMemAccesses ss
    |}.

  Definition applyScheduleToScop
             (schedule: P.AffineFnT)
             (scop: Scop): Scop :=
               {|
                 scopStmts := List.map (applyScheduleToScopStmt schedule) (scopStmts scop);
               |}.

  (** *Section that define the semantics of scop evaluation *)
  Section EVALUATION.

    Definition viv := P.PointT.
    Definition Schedule := P.AffineFnT.

    
  Inductive exec_scop_store_value: P.ParamsT -> ScopEnvironment -> viv -> ScopStoreValue -> Value -> Prop :=
  | eval_ssv_indvar_fn: forall (viv: P.PointT)
                          (se: ScopEnvironment)
                          (params: P.ParamsT)
                          (evalviv: list Z)
                          (EVALVIV: P.evalPoint params viv = evalviv)
                          (indvarfn: list Z -> Z),
      exec_scop_store_value params se viv (SSVIndvarFn indvarfn) (indvarfn evalviv)
  | eval_ssv_loaded_value: forall (viv: P.PointT)
                             (se: ScopEnvironment)
                             (params: P.ParamsT)
                             (ident: ScopLoadIdent)
                             (identval: Value)
                             (SE_AT_IDENT: se ## ident = Some identval),
      exec_scop_store_value params se viv (SSVLoadedVal ident) identval
  .

  
    Inductive exec_memory_access:  P.ParamsT -> ScopEnvironment -> viv -> Memory -> MemoryAccess -> Memory -> Prop :=
    | exec_store:
        forall (params: P.ParamsT)
          (se: ScopEnvironment)
          (viv: P.PointT)
          (memacc: MemoryAccess)
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


    (** Execute a statement. Checks if the statement is active or inactive before
       execution *)
    Inductive exec_scop_stmt: P.ParamsT -> ScopEnvironment -> viv -> Memory -> ScopStmt -> Memory -> Prop :=
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

    Inductive exec_scop_at_point: P.ParamsT -> ScopEnvironment -> viv -> Memory -> Scop -> Memory -> Prop :=
    | exec_scop_at_point_nil:
        forall (params: P.ParamsT)
          (se: ScopEnvironment)
          (viv: P.PointT)
          (initmem: Memory)
          (scop: Scop)
          (mem': Memory),
          exec_scop_at_point  params se viv initmem (mkScop []) initmem
    | exec_scop_at_point_cons:
        forall (params: P.ParamsT)
          (se: ScopEnvironment)
          (viv: P.PointT)
          (initmem: Memory)
          (scop: Scop)
          (stmt: ScopStmt)
          (stmts: list ScopStmt)
          (mem1 mem2: Memory)
          (EXECSTMT: exec_scop_stmt params se viv initmem stmt mem1)
          (EXECNEXT: exec_scop_at_point  params se viv mem1 (mkScop stmts) mem2),
          exec_scop_at_point params se viv initmem (mkScop (cons stmt stmts)) mem2.
    


    Definition getScopDomain (scop: Scop): P.PolyT :=
      List.fold_left P.unionPoly (map scopStmtDomain (scopStmts scop)) P.emptyPoly.
    
    Inductive exec_scop_from_lexmin: P.ParamsT -> ScopEnvironment -> viv -> Memory -> Scop -> Memory -> viv -> Prop :=
    | exec_scop_begin:
        forall 
          (se: ScopEnvironment)
          (initmem mem: Memory)
          (scop: Scop)
          (params: P.ParamsT)
          (vivmin: viv)
          (VIVMIN: vivmin = (P.getLexminPoint params (getScopDomain scop))),
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
          (vivbegin vivcur vivnext: viv)
          (NEXT: Some vivnext = P.getLexNextPoint params (getScopDomain scop)vivcur)
          (EXEC_SCOP_TILL: exec_scop_from_lexmin params se vivbegin initmem scop mem1  vivcur)
          (EXEC_SCOP_AT_POINT: exec_scop_at_point params se vivcur mem1 scop mem2),
          exec_scop_from_lexmin params se vivbegin initmem scop mem2 vivnext.

    Definition initScopEnvironment : ScopEnvironment. Admitted.
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

  (** **Hint database of proof *)
  Create HintDb proofdb.

  (** **Add all theorems from the polyhedral theory  into hint database*)
  Hint Resolve P.invertEvalAffineFn_is_inverse: proofdb.
  Hint Resolve P.isLexLT_GT: proofdb.
  Hint Rewrite P.isLexLT_GT: proofdb.
  Hint Resolve Z.eqb_refl: proofdb.

  (** *Section about writes *)
  Section WRITES.

    
    (** **Define what it means for a memory access to not write to memory *)
    Inductive MAStoreNoWrite:
      P.ParamsT
      -> Domain
      -> MemoryAccess
      -> ChunkNum
      -> list Z
      -> Prop :=
    | mkMAStoreNoWrite: forall
        (params: P.ParamsT)
        (domain: Domain)
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

    (** **Computational version of the write*)
    Definition MAWriteb
               (params: P.ParamsT)
               (domain: Domain)
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

    
    (** **If the point of access is not written by the memory access, then the memory access does not change that location *)
    Lemma point_not_in_memacc_implies_value_unchanged:
      forall (memacc: MemoryAccess)
        (domain: Domain)
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


    Lemma point_not_in_scop_stmt_implies_value_unchanged:
      forall (scop: Scop)
        (stmt: ScopStmt)
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
      induction EXECSCOPATPOINT; auto.
      unfold scopWriteb in *; simpl in *.
      
      assert (POINT_NOT_IN_POLY_CONJ: scopStmtWriteb params chunk  ix stmt  = false /\
                                       existsb (scopStmtWriteb params chunk ix) stmts = false).
      apply orb_false_elim; auto.

      
      destruct POINT_NOT_IN_POLY_CONJ as [P_NOT_IN_CUR_STMT  P_NOT_IN_OTHER_STMTS].

      assert (MEMSTMT_EQ_INITMEM:
                loadMemory chunk ix mem2 = loadMemory chunk ix mem1); auto.
      assert (MEMSTMT_EQ_MEMNEW:
                loadMemory chunk ix mem1 = loadMemory chunk ix initmem).
      eauto with proofdb.
      congruence.
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
    (* Inductive IsLastWrite: Params -> Scop -> ScopStmt -> MemoryAccess -> ChunkNum -> list Z -> Prop :=
    | mkLastWrite: forall (scop: Scop)
                     (stmt: Stmt)
                     (accessfn: AccessFunction)
                     (ssv: ScopStoreValue)
                     (chunk: ChunkNum)
                     (ix: list Z),
        MAWriteb params (scopStmtDomain stmt) chunk ix  (MAstore chunk )
               (params: P.ParamsT)
               (domain: Domain)
               (needlechunk: ChunkNum)
               (needleix: list Z)
               (memacc: MemoryAccess)
               *)
        
    Record IsLastWrite (params: P.ParamsT)
           (scop: Scop)
           (stmt: ScopStmt)
           (ma: MemoryAccess)
           (lwchunk: ChunkNum)
           (lwviv: P.PointT)
           (lwix: list Z) : Prop :=
      mkLastWrite {
          lastWriteVivInDomain: P.isPointInPoly lwviv (getScopDomain scop) = true;
          lastWriteVivIx: lwix = evalAccessFunction params (getMAAccessFunction ma) lwviv;
          lastWriteWrite: MAWriteb params (scopStmtDomain stmt) lwchunk lwix ma = true;
          lastWriteLast:
            forall (macur: MemoryAccess)
              (vivcur: P.PointT)
              (VIVCUR_IX: lwix = evalAccessFunction params (getMAAccessFunction macur) vivcur)
              (VIVLW_LT_VIVCUR: P.isLexLT  lwviv vivcur = Some true),
              MAWriteb params (getScopDomain scop) lwchunk lwix macur = false;
        }.

    Hint Constructors IsLastWrite: proofdb.
    Hint Resolve lastWriteVivInDomain: proofdb.
    Hint Resolve lastWriteVivIx: proofdb.
    Hint Resolve lastWriteWrite: proofdb.
    Hint Resolve lastWriteLast: proofdb.

      

    (** **Last write is decidable *)
    Lemma IsLastWriteDecidable: forall(params: P.ParamsT)
        (scop: Scop)
        (stmt: ScopStmt)
        (ma: MemoryAccess)
        (chunk: ChunkNum)
        (ix: list Z)
        (viv: P.PointT),
        {IsLastWrite params scop stmt ma chunk viv ix} +
        {~IsLastWrite params scop stmt ma chunk viv ix}.
    Proof.
    Admitted.

    Hint Resolve IsLastWriteDecidable: proofdb.
    Hint Rewrite IsLastWriteDecidable: proofdb.

    
    Lemma LastWriteImposesMemoryValue_exec_mem_access:
      forall (params: P.ParamsT)
        (se: ScopEnvironment)
        (vivcur: viv)
        (initmem finalmem: Memory)
        (macur: MemoryAccess)
        (EXEC_MEM_ACCESS: exec_memory_access params se vivcur initmem macur finalmem)
        (scop: Scop)
        (VIVCUR_IN_DOMAIN: P.isPointInPoly vivcur (getScopDomain scop) = true)
        (vivlw: viv)
        (LEXCUR_GT_VIVLW: P.isLexGT vivcur vivlw = Some true)
        (lwaccessfn: AccessFunction)
        (lwchunk: ChunkNum)
        (lwix: list Z)
        (lwssv: ScopStoreValue)
        (lwstmt: ScopStmt)
        (LASTWRITE: IsLastWrite params scop lwstmt
                                (MAStore lwchunk lwaccessfn lwssv) lwchunk vivlw lwix),
        loadMemory lwchunk lwix finalmem = loadMemory lwchunk lwix initmem.
    Proof.
      intros until 1.
      induction EXEC_MEM_ACCESS; auto.
      intros.
      assert (CHUNK_CASES: {lwchunk = chunk} + {lwchunk <> chunk}); auto.
      destruct CHUNK_CASES as [EQ | NEQ]; eauto with proofdb.
      rewrite EQ in *. 

      assert (IX_CASES: {lwix = accessix} + {lwix <> accessix}); auto.
      destruct IX_CASES as [IXEQ | IXNEQ]; eauto with proofdb.

      (** From the fact that the write perfectly aliases, we can conclucde
      that this write does write into the last write ix *)
      assert (WRITE_IN_LW: MAWriteb params (getScopDomain scop) lwchunk lwix
                       (MAStore lwchunk accessfn ssv)= true).
      subst.
      simpl.
      rewrite andb_true_intro; auto.
      split; eauto with proofdb.

      (* However, from the fact that we have a _last write_, and that vivcur > vivlw,
         this cannot happen! *)
      assert (WRITE_NOT_IN_LW: MAWriteb params (getScopDomain scop) lwchunk lwix
                                        (MAStore lwchunk accessfn ssv) = false).
      subst.
      eapply lastWriteLast; eauto with proofdb.
      (** TODO: this should automatically work, figure out why it is not *)
      eapply P.isLexLT_GT; auto.

      (* Boom *)
      assert (CONTRA: true = false).
      congruence.

      inversion CONTRA.
    Qed.
      
      
    Inductive exec_memory_access:  P.ParamsT -> ScopEnvironment -> viv -> Memory -> MemoryAccess -> Memory -> Prop :=
      

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
        admit.

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
      (** Show that on appending )

    Qed.
        

      
    
  End LASTWRITE.

  
  Hint Resolve LastWriteImposesMemoryValue: proofdb.
  Hint Rewrite LastWriteImposesMemoryValue: proofdb.

  (** *Section that formalises the proof *)
  Section PROOF.

    Record validSchedule (scop: Scop) (schedule: Schedule) (scop': Scop) : Prop :=
      mkValidSchedule {
          NEWSCOP_IS_SCHEDULED_OLDSCOP: (scop' = applyScheduleToScop schedule scop);
          RESPECTSRAW: scheduleRespectsRAW schedule scop;
          RESPECTSWAW: scheduleRespectsWAW schedule scop;
        }.


    Definition MemExtesionallyEqual (mem1 mem2: Memory): Prop :=
      forall (chunk: ChunkNum) (ix: list Z),
        loadMemory chunk ix mem1 = loadMemory chunk ix mem2.




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
