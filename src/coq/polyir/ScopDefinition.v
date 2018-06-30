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
  Parameter isPointInPolyProp: PointT -> PolyT -> Prop.

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

  
  (** The identifier of some loaded value, to be stored in the abstract
    scop environment **)
  Definition ScopLoadIdent := Z.

  (** Mapping from load identifiers to values *)
  Definition ScopEnvironment := ZMap.t (option Z).

  (** The things that a store expression is allowed to store
   A[i, j, k, ..] = <ScopStore>*)
  Inductive ScopStoreValue :=
  | SSVIndvarFn: (list Z -> Z) -> ScopStoreValue (**r function of indvars *)
  | SSVLoadedVal: ScopLoadIdent -> ScopStoreValue (**r store some loaded value *)
  .

  Inductive MemoryAccess :=
  | MAStore: ChunkNum (**r array name *)
                    -> AccessFunction (**r index expression *)
                    -> ScopStoreValue (**r value to store *)
                    -> MemoryAccess
  | MALoad: ChunkNum (**r name *)
            -> ScopLoadIdent  (**r abstract store identiffier *)
            -> AccessFunction (**r index expression *)
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
      }.

  (** Get the memory accesses in a scop *)
  Definition getScopMemoryAccessses (scop: Scop): list MemoryAccess :=
    concat (List.map (scopStmtMemAccesses) (scopStmts scop)).



  Definition evalAccessFunction (viv : P.PointT)
             (accessfn: P.AffineFnT): (list Z) :=  [].
    

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
                  |})
               (option_traverse
                  (List.map (applyScheduleToScopStmt schedule)
                            (scopStmts scop))).

  Section EVALUATION.

    Definition viv := P.PointT.
    Definition Schedule := P.AffineFnT.

    
  Inductive exec_scop_store_value: P.ParamsT -> ScopEnvironment -> viv -> ScopStoreValue -> Value -> Prop :=
  | eval_ssv_indvar_fn: forall (viv: P.PointT)
                          (se: ScopEnvironment)
                          (params: P.ParamsT)
                          (evalviv: list Z)
                          (EVALVIV: P.evalPoint params viv = Some evalviv)
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


    (** Execute a statement. Checks if the statement is active or inactive before
       execution *)
    Inductive exec_scop_stmt: viv -> Memory -> ScopStmt -> Memory -> Prop :=
    | exec_stmt_nil:
        forall (viv: P.PointT)
          (initmem: Memory)
          (domain: P.PolyT)
          (schedule: P.AffineFnT),
          exec_scop_stmt viv initmem (mkScopStmt domain schedule []) initmem
    | exec_stmt_cons_active:
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
    | exec_stmt_cons_inactive:
        forall (viv: P.PointT)
          (domain: P.PolyT)
          (PT_IN_DOMAIN: P.isPointInPoly viv domain = false)
          (schedule: P.AffineFnT)
          (mas: list MemoryAccess)
          (initmem: Memory),
          exec_scop_stmt viv initmem (mkScopStmt domain schedule mas) initmem
    .

    Inductive exec_scop_at_point: viv -> Memory -> Scop -> Memory -> Prop :=
    | exec_scop_at_point_nil: forall (viv: viv)
                                (initmem: Memory)
                                (scop: Scop)
                                (mem': Memory),
        exec_scop_at_point  viv initmem (mkScop []) initmem
    | exec_scop_at_point_cons:
        forall (viv: viv)
          (initmem: Memory)
          (scop: Scop)
          (stmt: ScopStmt)
          (stmts: list ScopStmt)
          (mem1 mem2: Memory),
          exec_scop_stmt viv initmem stmt mem1 ->
          exec_scop_at_point  viv mem1 (mkScop stmts) mem2 ->
          exec_scop_at_point viv initmem (mkScop (cons stmt stmts)) mem2.
    


    Definition getScopDomain (scop: Scop): P.PolyT :=
      List.fold_left P.unionPoly (map scopStmtDomain (scopStmts scop)) P.emptyPoly.
    
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
          exec_scop_at_point vivcur mem1 scop mem2 ->
          exec_scop_from_lexmin params vivbegin initmem scop mem2 vivnext.

    Definition exec_scop (params: P.ParamsT)
               (initmem: Memory)
               (scop: Scop)
               (finalmem: Memory): Prop :=
      exec_scop_from_lexmin params
                            (P.getLexminPoint params (getScopDomain scop))
                            initmem
                            scop
                            finalmem
                            (P.getLexmaxPoint params (getScopDomain scop)).
  End EVALUATION.

  Section PROOF.

    Create HintDb proofdb.

    Record validSchedule (scop: Scop) (schedule: Schedule) (scop': Scop) : Prop :=
      mkValidSchedule {
          NEWSCOP_IS_SCHEDULED_OLDSCOP: (Some scop' = applyScheduleToScop schedule scop);
          RESPECTSRAW: scheduleRespectsRAW schedule scop;
          RESPECTSWAW: scheduleRespectsWAW schedule scop;
        }.


    Definition MemExtesionallyEqual (mem1 mem2: Memory): Prop :=
      forall (chunk: ChunkNum) (ix: list Z),
        loadMemory chunk ix mem1 = loadMemory chunk ix mem2.

    (** Construct the write polyhedra of the scop,
        which contains the set of all multidimensional
    time points that perform a write *)
    Definition writePolyhedra (scop: Scop): P.PolyT.
    Admitted.

    (** Convert a write in memory into the abstract multidimensional timepoint **)
    Definition writeToPoint (chunk: ChunkNum) (ix: list Z): P.PointT.
    Admitted.

    (** If a point has not been written to, then the value
        remains unchanged *)
    Lemma point_not_in_write_polyhedra_implies_value_unchanged:
      forall (scop: Scop)
        (initmem finalmem: Memory)
        (params: P.ParamsT)
        (EXECSCOP: exec_scop params initmem scop finalmem)
        (chunk: ChunkNum)
        (ix: list Z)
        (POINT_NOT_IN_POLY: P.isPointInPoly (writeToPoint chunk ix)
                                            (writePolyhedra scop) = false),
        loadMemory chunk ix finalmem = loadMemory chunk ix initmem.
    Proof.
    Admitted.

    Hint Resolve point_not_in_write_polyhedra_implies_value_unchanged: proofdb.
    Hint Rewrite point_not_in_write_polyhedra_implies_value_unchanged: proofdb.


    (** a valid schedule preserves inclusion and exclusion into the write
    polyhedra **)
    Lemma valid_schedule_preserves_write_polyhedra_containment:
      forall (scop scop': Scop)
        (schedule: Schedule)
        (VALIDSCHEDULE: validSchedule scop schedule scop')
        (chunk: ChunkNum)
        (ix: list Z),
        P.isPointInPoly
          (writeToPoint chunk ix)
          (writePolyhedra scop') = 
        P.isPointInPoly
          (writeToPoint chunk ix)
          (writePolyhedra scop).
    Proof.
    Admitted.

    Hint Resolve valid_schedule_preserves_write_polyhedra_containment: proofdb.
    Hint Rewrite valid_schedule_preserves_write_polyhedra_containment: proofdb.


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
      intros.
      unfold MemExtesionallyEqual.

      intros.

      
        assert (POINTINPOLY': P.isPointInPoly (writeToPoint chunk ix)
                                              (writePolyhedra scop') =
                              P.isPointInPoly (writeToPoint chunk ix)
                                              (writePolyhedra scop));
        eauto with proofdb.

      destruct (P.isPointInPoly (writeToPoint chunk ix) (writePolyhedra scop))
             eqn: POINTINPOLY_CASES.
      - (* write in poly *)

        assert (WRITE_AT_TIIMEPOINT: exists tp, exists write,
                     List.In ()
               )


        
        
      -
        (* Write not in poly *)
        assert (LOAD_FINALMEM: loadMemory chunk ix finalmem  = loadMemory chunk ix initmem);
          eauto with proofdb.
        
        assert (LOAD_FINALMEM': loadMemory chunk ix finalmem'  = loadMemory chunk ix initmem);
          eauto with proofdb.

        congruence.
    Admitted.
  End PROOF.

End SCOP.
