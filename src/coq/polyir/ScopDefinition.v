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


  (** Note that for now, we don't care what is stored or loaded, because
conceptually, we don't actually care either. We just want to make sure
that the reads/writes are modeled *)
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
          (MEMNEW_FROM_MEMSTMT: exec_memory_access params se viv initmem ma memnew),
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


    Lemma point_not_in_scop_stmt_implies_value_unchanged:
      forall (scop: Scop)
        (stmt: ScopStmt)
        (initmem finalmem: Memory)
        (params: P.ParamsT)
        (se: ScopEnvironment)
        (viv: viv)
        (EXECSCOP: exec_scop_stmt params se viv initmem stmt finalmem)
        (chunk: ChunkNum)
        (ix: list Z)
        (POINT_NOT_IN_POLY: scopStmtWriteb params chunk ix stmt = false),
        loadMemory chunk ix finalmem = loadMemory chunk ix initmem.
    Proof.
    Admitted.

    

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
      
      admit.
    Admitted.



    
    Hint Resolve point_not_in_write_polyhedra_implies_value_unchanged: proofdb.
    Hint Rewrite point_not_in_write_polyhedra_implies_value_unchanged: proofdb.


    
    End WRITES.

  (** *Section to reason about last writes *)
  Section LASTWRITE.

    (** **The definition of a last write in a scop *)
    Definition IsLastWrite (scop: Scop)
               (stmt: ScopStmt)
               (ma: MemoryAccess)
               (chunk: ChunkNum)
               (ix: list Z): Prop.
    Admitted.

    (** **Last write is decidable *)
    Lemma IsLastWriteDecidable: forall (scop: Scop)
                                  (stmt: ScopStmt)
                                  (ma: MemoryAccess)
                                  (chunk: ChunkNum)
                                  (ix: list Z),
        {IsLastWrite scop stmt ma chunk ix} + {~IsLastWrite scop stmt ma chunk ix}.
    Proof.
    Admitted.

    Hint Resolve IsLastWriteDecidable: proofdb.
    Hint Rewrite IsLastWriteDecidable: proofdb.

    (** **If we have a last write, then the value in memory is the value written by the last write *)
    Lemma LastWriteImposesMemoryValue:
      forall (scop: Scop)
        (stmt: ScopStmt)
        (mem: Memory)
        (chunk: ChunkNum)
        (ix: list Z)
        (accessfn: AccessFunction)
        (ssv: ScopStoreValue)
        (viv: viv)
        (VIV_WITNESS: evalAccessFunction viv accessfn = ix)
        (LASTWRITE: IsLastWrite scop stmt (MAStore chunk accessfn ssv) chunk ix)
        (storeval: Value)
        (se: ScopEnvironment)
        (params: P.ParamsT)
        (EXECWRITEVAL: exec_scop_store_value params se viv ssv storeval),
        loadMemory chunk ix mem = Some storeval.
    Admitted.
    
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
        (evalAccessFunction viv accessfn = ix) /\
        P.isPointInPoly viv (getScopDomain scop) = true /\
        IsLastWrite scop stmt (MAStore chunk accessfn ssv) chunk ix.
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
      forall (scop scop': Scop)
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
        (ACCESSFN: evalAccessFunction viv accessfn = ix)
        (VIV_IN_SCOP: P.isPointInPoly viv (getScopDomain scop) = true)
        (LASTWRITE: IsLastWrite scop stmt (MAStore chunk accessfn ssv) chunk ix),
        IsLastWrite scop' (applyScheduleToScopStmt schedule stmt) (MAStore chunk accessfn ssv) chunk ix.
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
              (evalAccessFunction viv accessfn = ix) /\
              P.isPointInPoly viv (getScopDomain scop) = true /\
              IsLastWrite scop stmt (MAStore chunk accessfn ssv) chunk ix).
        eauto with proofdb.
        

        destruct WRITEINPOLY as (stmt & accessfn & ssv & viv &
                                 STMT_IN_SCOP & MEM_IN_STMT & EVALACCESSFN &
                                 VIV_IN_DOMAIN & LASTWRITE).

        assert (LASTWRITE_SCOP': 
                  IsLastWrite scop'
                              (applyScheduleToScopStmt schedule stmt)
                              (MAStore chunk accessfn ssv)
                              chunk
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
