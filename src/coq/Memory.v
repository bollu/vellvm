Require Import ZArith List String Omega.
Require Import Vellvm.LLVMAst Vellvm.Classes Vellvm.Util.
Require Import Vellvm.MemoryAddress.
Require Import Vellvm.LLVMIO.
Require Import FSets.FMapAVL.
Require Import Integers.
Require Coq.Structures.OrderedTypeEx.
Require Import ZMicromega.
Import ListNotations.
Require Import Setoid Morphisms Relations.


From mathcomp Require ssreflect ssrbool ssrfun bigop.
Import ssreflect.SsrSyntax.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Implicit Arguments.
Set Contextual Implicit.

Module A : MemoryAddress.ADDRESS with Definition addr := (Z * Z) % type.
  Definition addr := (Z * Z) % type.
  Definition null := (0, 0).
  Definition t := addr.
  Lemma addr_dec : forall (a b : addr), {a = b} + {a <> b}.
  Proof.
    intros [a1 a2] [b1 b2].
    destruct (a1 == b1); 
      destruct (a2 == b2); subst.
    - left; reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.
    - right. intros H. inversion H; subst. apply n. reflexivity.      
  Qed.
End A.


Module Make(LLVMIO: LLVM_INTERACTIONS(A)).
  Import LLVMIO.
  Import DV.
  
Definition addr := A.addr.

Module IM := FMapAVL.Make(Coq.Structures.OrderedTypeEx.Z_as_OT).
Definition IntMap := IM.t.

Definition add {a} k (v:a) := IM.add k v.
Definition delete {a} k (m:IntMap a) := IM.remove k m.
Definition member {a} k (m:IntMap a) := IM.mem k m.
Definition lookup {a} k (m:IntMap a) := IM.find k m.
Definition empty {a} := @IM.empty a.

Fixpoint add_all {a} ks (m:IntMap a) :=
  match ks with
  | [] => m
  | (k,v) :: tl => add k v (add_all tl m)
  end.

Fixpoint add_all_index {a} vs (i:Z) (m:IntMap a) :=
  match vs with
  | [] => m
  | v :: tl => add i v (add_all_index tl (i+1) m)
  end.

(* Give back a list of values from i to (i + sz) - 1 in m. *)
(* Uses def as the default value if a lookup failed. *)
Definition lookup_all_index {a} (i:Z) (sz:Z) (m:IntMap a) (def:a) : list a :=
  map (fun x =>
         let x' := lookup (Z.of_nat x) m in
         match x' with
         | None => def
         | Some val => val
         end) (seq (Z.to_nat i) (Z.to_nat sz)).

Definition union {a} (m1 : IntMap a) (m2 : IntMap a)
  := IM.map2 (fun mx my =>
                match mx with | Some x => Some x | None => my end) m1 m2.

Definition size {a} (m : IM.t a) : Z := Z.of_nat (IM.cardinal m).

Inductive SByte :=
| Byte : byte -> SByte
| Ptr : addr -> SByte
| PtrFrag : SByte
| SUndef : SByte.

Definition mem_block := IntMap SByte.
Definition memory := IntMap mem_block.
Definition undef := DVALUE_Undef. (* TODO: should this be an empty block? *)

(* Computes the byte size of this type. *)
Fixpoint sizeof_dtyp (ty:dtyp) : Z :=
  match ty with
  | DTYPE_I sz => 8 (* All integers are padded to 8 bytes. *)
  | DTYPE_Pointer => 8
  | DTYPE_Struct l => fold_left (fun x acc => x + sizeof_dtyp acc) l 0
  | DTYPE_Array sz ty' => sz * sizeof_dtyp ty'
  | _ => 0 (* TODO: add support for more types as necessary *)
  end.

(* Convert integer to its SByte representation. *)
Fixpoint Z_to_sbyte_list (count:nat) (z:Z) : list SByte :=
  match count with
  | O => []
  | S n => (Z_to_sbyte_list n (z / 256)) ++ [Byte (Byte.repr (z mod 256))]
  end.

(* Converts SBytes into their integer representation. *)
Definition sbyte_list_to_Z (bytes:list SByte) : Z :=
  fst (fold_right (fun x acc =>
               match x with
               | Byte b =>
                 let shift := snd acc in
                 ((fst acc) + ((Byte.intval b) * shift), shift * 256)
               | _ => acc (* should not have other kinds bytes in an int *)
               end) (0, 1) bytes).

(* Serializes a dvalue into its SByte-sensitive form. *)
Fixpoint serialize_dvalue (dval:dvalue) : list SByte :=
  match dval with
  | DVALUE_Addr addr => (Ptr addr) :: (repeat PtrFrag 7)
  | DVALUE_I1 i => Z_to_sbyte_list 8 (DynamicValues.Int1.unsigned i)
  | DVALUE_I32 i => Z_to_sbyte_list 8 (DynamicValues.Int32.unsigned i)
  | DVALUE_I64 i => Z_to_sbyte_list 8 (Int64.unsigned i)
  | DVALUE_Struct fields | DVALUE_Array fields =>
      (* note the _right_ fold is necessary for byte ordering. *)
      fold_right (fun 'dv acc => ((serialize_dvalue dv) ++ acc) % list) [] fields
  | _ => [] (* TODO add more dvalues as necessary *)
  end.

(* Deserialize a list of SBytes into a dvalue. *)
Fixpoint deserialize_sbytes (bytes:list SByte) (t:dtyp) : dvalue :=
  match t with
  | DTYPE_I sz =>
    let des_int := sbyte_list_to_Z bytes in
    match sz with
    | 1 => DVALUE_I1 (DynamicValues.Int1.repr des_int)
    | 32 => DVALUE_I32 (DynamicValues.Int32.repr des_int)
    | 64 => DVALUE_I64 (Int64.repr des_int)
    | _ => DVALUE_None (* invalid size. *)
    end
  | DTYPE_Pointer =>
    match bytes with
    | Ptr addr :: tl => DVALUE_Addr addr
    | _ => DVALUE_None (* invalid pointer. *)
    end
  | DTYPE_Array sz t' =>
    let fix array_parse count byte_sz bytes :=
        match count with
        | O => []
        | S n => (deserialize_sbytes (firstn byte_sz bytes) t')
                   :: array_parse n byte_sz (skipn byte_sz bytes)
        end in
    DVALUE_Array (array_parse (Z.to_nat sz) (Z.to_nat (sizeof_dtyp t')) bytes)
  | DTYPE_Struct fields =>
    let fix struct_parse typ_list bytes :=
        match typ_list with
        | [] => []
        | t :: tl =>
          let size_ty := Z.to_nat (sizeof_dtyp t) in
          (deserialize_sbytes (firstn size_ty bytes) t)
            :: struct_parse tl (skipn size_ty bytes)
        end in
    DVALUE_Struct (struct_parse fields bytes)
  | _ => DVALUE_None (* TODO add more as serialization support increases *)
  end.

(* Construct block indexed from 0 to n. *)
Fixpoint init_block_h (n:nat) (m:mem_block) : mem_block :=
  match n with
  | O => add 0 SUndef m
  | S n' => add (Z.of_nat n) SUndef (init_block_h n' m)
  end.

(* Initializes a block of n 0-bytes. *)
Definition init_block (n:Z) : mem_block :=
  match n with
  | 0 => empty
  | Z.pos n' => init_block_h (BinPosDef.Pos.to_nat (n' - 1)) empty
  | Z.neg _ => empty (* invalid argument *)
  end.

(* Makes a block appropriately sized for the given type. *)
Definition make_empty_block (ty:dtyp) : mem_block :=
  init_block (sizeof_dtyp ty).

Definition mem_step {X} (e:IO X) (m:memory) : (IO X) + (memory * X) :=
  match e with
  | Alloca t =>
    let new_block := make_empty_block t in
    inr  (add (size m) new_block m,
          DVALUE_Addr (size m, 0))
         
  | Load t dv =>
    match dv with
    | DVALUE_Addr a =>
      match a with
      | (b, i) =>
        match lookup b m with
        | Some block =>
          inr (m,
               deserialize_sbytes (lookup_all_index i (sizeof_dtyp t) block SUndef) t)
        | None => inl (Load t dv)
        end
      end
    | _ => inl (Load t dv)
    end 

  | Store dv v =>
    match dv with
    | DVALUE_Addr a =>
      match a with
      | (b, i) =>
        match lookup b m with
        | Some m' =>
          inr (add b (add_all_index (serialize_dvalue v) i m') m, ()) 
        | None => inl (Store dv v)
        end
      end
    | _ => inl (Store dv v)
    end
      
  | GEP t dv vs =>
    (* Index into a structured data type. *)
    let index_into_type typ index :=
        match typ with
        | DTYPE_Array sz ty =>
          if sz <=? index then None else
            Some (ty, index * (sizeof_dtyp ty))
        | DTYPE_Struct fields =>
          let new_typ := List.nth_error fields (Z.to_nat index) in
          match new_typ with
          | Some new_typ' =>
            (* Compute the byte-offset induced by the first i elements of the struct. *)
            let fix compute_offset typ_list i :=
                match typ_list with
                | [] => 0
                | hd :: tl =>
                  if i <? index
                  then sizeof_dtyp hd + compute_offset tl (i + 1)
                  else 0
                end
              in
            Some (new_typ', compute_offset fields 0)
          | None => None
          end
        | _ => None (* add type support as necessary *)
        end
    in
    (* Give back the final byte-offset into mem_bytes *)
    let fix gep_helper mem_bytes cur_type offsets offset_acc :=
        match offsets with
        | [] => offset_acc
        | dval :: tl =>
          match dval with
          | DVALUE_I32 x =>
            let nat_index := DynamicValues.Int32.unsigned x in
            let new_typ_info := index_into_type cur_type nat_index in
            match new_typ_info with
              | Some (new_typ, offset) => 
                gep_helper mem_bytes new_typ tl (offset_acc + offset)
              | None => 0 (* fail *)
            end
          | _ => 0 (* fail, at least until supporting non-i32 indexes *)
          end
        end
    in
    match dv with
    | DVALUE_Addr a =>
      match a with
      | (b, i) =>
        match lookup b m with
        | Some block =>
          let mem_val := lookup_all_index i (sizeof_dtyp t) block SUndef in
          let answer := gep_helper mem_val t vs 0 in
          inr (m, DVALUE_Addr (b, i + answer))
        | None => inl (GEP t dv vs)
        end
      end
    | _ => inl (GEP t dv vs)
    end
  | ItoP i => inl (ItoP i) (* TODO: ItoP semantics *)

  | PtoI a => inl (PtoI a) (* TODO: ItoP semantics *)                     
                       
  | Call t f args  => inl (Call t f args)

                         
  (* | DeclareFun f => *)
  (*   (* TODO: should check for re-declarations and maintain that state in the memory *) *)
  (*   (* TODO: what should be the "size" of the block associated with a function? *) *)
  (*   let new_block := make_empty_block DTYPE_Pointer in *)
  (*   inr  (add (size m) new_block m, *)
  (*         DVALUE_Addr (size m, 0)) *)
  end.

(*
 memory -> TraceLLVMIO () -> TraceX86IO () -> Prop
*)

CoFixpoint memD {X} (m:memory) (d:Trace X) : Trace X :=
  match d with
  | Trace.Tau d'            => Trace.Tau (memD m d')
  | Trace.Vis _ io k =>
    match mem_step io m with
    | inr (m', v) => Trace.Tau (memD m' (k v))
    | inl e => Trace.Err "uninterpretiable IO call" (* Trace.Vis io k *)
    end
  | Trace.Ret x => d
  | Trace.Err x => d
  end.


(* 
| TFRet: forall (x: X), TraceFinite (Ret x)
| TFErr: forall (s: String.string), TraceFinite (Err s)
| TFTau: forall (mex: M E X) (FIN: TraceFinite mex),
    TraceFinite (Tau mex)
| TFVis: forall {Y: Type} (e: E Y) (k: Y -> M E X)
           (FINK: forall (y: Y), TraceFinite (k y)),
    TraceFinite (Vis e k)
 *)


Definition pairMemToTrace {X}
                             (m: memory)
                             (d: Trace X): Trace (memory * X) :=
  Trace.mapM (fun t => (m, t)) d.

(** From haskell's Control.Arrow.Second **)
Definition arrowSecond {A P Q: Type} (f: P -> Q) (tuple: A * P): A * Q :=
  match tuple with
    (a, p) => (a, f p)
  end.

Definition traceJoin {X: Type} (trtrx: Trace (Trace X)): Trace X :=
  Trace.bindM (trtrx) id.

Definition arrowSecondTrace {A P Q: Type} (f: P -> Trace Q) (tuple: Trace (A * P)): Trace  (A * Q) :=
  Trace.bindM tuple (fun t => match t with
                             (a, p) => Trace.mapM (fun t' => (a, t')) (f p)
                           end).

            

(** A version of memD that also provides the state of memory at a
    given point *)
CoFixpoint memEffect {X} (m: memory) (tx: Trace X):
  Trace (memory * X) :=
  (* (Trace memory) * (Trace X) := *)
  match tx with
  | Trace.Ret x => (Trace.Ret ( m,  x))
  | Trace.Err e => Trace.Err e
  | Trace.Tau x' =>  Trace.Tau (memEffect m x')
  | Trace.Vis Y io k => 
    match mem_step io m with
    | inr (m', v) => Trace.Tau (memEffect m' (k v))
    | inl e => Trace.Err "uninterpretiable IO call "
    end
  end.
                                                               
(** Tear down the finite trace to record effects that happened on memory **)
Fixpoint mem_effect_fin {X} (m: memory) (d: Trace X) (FIN: Trace.TraceFinite d)
  {struct FIN}: memory *Trace X :=
  match FIN with
  | Trace.TFRet _ => (m, d)
  | Trace.TFErr  _ => (m, d)
  | Trace.TFTau mex' FIN' => let (m, t) := mem_effect_fin m FIN'
                            in (m, Trace.Tau t)
  | Trace.TFVis Y io k FINK => match (mem_step io m) with
                              | inr (m', v) =>
                                (* Is this correct..?*)
                                let (m'', t) := mem_effect_fin m' (FINK v)
                                in  (m'', Trace.Tau t)
                              | inl e => (m, Trace.Err "uninterpretiable IO call")
                              end
  end.

Check (mem_effect_fin).
Print mem_effect_fin.
    
                             
                             

Open Scope list_scope.
Lemma seq_inc_size: forall (begin size: nat),
    (seq begin (S size)) = (seq begin size) ++ [(begin+size)%nat].
Proof.
  intros.
  simpl.
  generalize dependent begin.
  induction size0; intros; simpl; auto.
  - replace (begin + 0)%nat with begin; auto; try omega.
  - simpl.
    rewrite IHsize0.
    replace (S begin + size0)%nat with (begin + S size0)%nat; auto; try omega.
Qed.


Lemma seq_inc_begin: forall (begin size: nat) (SIZE_GT_0: (size > 0)%nat),
    (seq begin (size)) = begin::(seq (S begin) (size - 1)%nat).
Proof.
  intros.
  simpl.
  generalize dependent begin.
  induction size0; intros; simpl; auto.
  - omega.
  - replace (size0 - 0)%nat with size0; auto; try omega.
Qed.

Definition list_length_Z {A: Type} (l: list A) : Z :=
  Z.of_nat (List.length l).

Lemma lookup_add: forall {A: Type} (ix: Z) (v: A) (mem: IntMap A),
    lookup ix (add ix v mem) = Some v.
Proof.
  intros.
  unfold lookup.
  unfold add.
  auto.
  assert (ADD_MAPSTO: IM.MapsTo ix v ( (IM.add ix v mem) )).
  apply IM.add_1; auto.
  apply IM.find_1; auto.
Qed.

Lemma lookup_add_all_index:
  forall {A: Type}
    (writevs: list A)
    (lookupix beginix: Z)
    (mem: IntMap A)
    (LOOKUP_IN_RANGE: lookupix >= beginix /\ lookupix < beginix + list_length_Z writevs),
    (lookup lookupix (add_all_index writevs beginix mem)) =
    List.nth_error writevs (Z.to_nat (lookupix  - beginix)%Z).
Proof.
  intros until writevs.
  induction writevs using rev_ind.
  - intros.
    unfold list_length_Z in *.
    simpl in *.
    omega.
  - intros.
    unfold list_length_Z in *.
    simpl in *.
    replace (Z.of_nat (Datatypes.length (writevs ++ [x]))) with
        (Z.of_nat (Datatypes.length writevs) + 1)%Z in *.
    assert (LOOKUPIX_CASES:
              lookupix = beginix +
                         (Z.of_nat (Datatypes.length writevs))
              \/
              (lookupix >= beginix
               /\ lookupix < beginix +
                            Z.of_nat (Datatypes.length writevs))).
    omega.
    destruct LOOKUPIX_CASES as [LOOKUPIXCASES_END | LOOKUPIX_CASES_INRANGE].

    + unfold add_all_index.
Admitted.
  
  
  
                                                                


Lemma lookup_all_index_of_add_all_index_full_alias:
  forall {A: Type}
    (writevs: list A)
    (beginix size: Z)
    (mem: IntMap A)
    (default: A)
    (LENEQ: Z.of_nat (List.length writevs) = size),
    (@lookup_all_index A beginix size (add_all_index writevs beginix mem) default) =
    writevs.
Proof.
  intros until default.
  generalize dependent beginix.
  generalize dependent size0.
  induction writevs using rev_ind.
  - intros.
    simpl in *.
    subst.
    auto.

  - intros.
    simpl in *.
    unfold lookup_all_index.

    assert (size0_as_succ: exists psize, size0 = Z.of_nat (S psize)).
    admit.

    destruct (size0_as_succ) as [psize PSIZE_WITNESS].
    subst.
    rewrite PSIZE_WITNESS.
    replace (Z.to_nat (Z.of_nat (S psize))) with (S psize).
    rewrite seq_inc_size.
    rewrite map_app.
    simpl.
Admitted.


Lemma lookup_all_index_of_add_all_index_no_alias:
  forall {A: Type}
    (writevs: list A)
    (beginwix beginrix rsize: Z)
    (mem: IntMap A)
    (default: A)
    (NOALIAS: beginrix + rsize <= beginwix \/ beginrix > beginwix + list_length_Z writevs), 
    (@lookup_all_index A beginrix rsize (add_all_index writevs beginwix mem) default) = lookup_all_index beginrix rsize mem default.
Proof.
Admitted.

Close Scope list_scope.
         
(* Make this opaque so it does not simplify outside the module *)
Opaque add_all_index.


(** Theorems about the interactions of memory with traces **)
Lemma force_memD_vis:
  forall { X Y: Type}
    (e: LLVMIO.IO Y)
    (k: Y -> Trace X)
    (mem: memory),
    memD mem  (Trace.Vis e k) ≡
    match mem_step e mem with
    | inl _ => Trace.Err "uninterpretiable IO call"
    | inr (m', v) => Trace.Tau (memD m' (k v))
    end.
Proof.
  intros.
  rewrite @Trace.matchM with (i := memD _ _).
  simpl.
  destruct (mem_step e mem).
  - reflexivity.
  - destruct p. reflexivity.
Defined.


Lemma force_memD_ret:
  forall { X: Type}
    (x:  Trace X)
    (mem: memory),
    memD mem  (Trace.Ret x) ≡ Trace.Ret x.
Proof.
  intros.
  rewrite @Trace.matchM with (i := memD _ _).
  simpl.
  reflexivity.
Defined.


Lemma force_memD_err:
  forall {X: Type}
    (s:String.string)
    (mem: memory),
    memD (X:=X) mem  (Trace.Err s) ≡ Trace.Err s.
Proof.
  intros.
  rewrite @Trace.matchM with (i := memD _ _).
  simpl.
  reflexivity.
Defined.

Ltac forcememd := do [rewrite force_memD_ret | rewrite force_memD_vis |
                     rewrite force_memD_err]; simpl; auto.

Import Trace.MonadVerif.


Lemma memD_commutes_tauN: forall (X: Type) n (x: Trace X) mem,
             memD mem (tauN n x) ≡ tauN n (memD mem x).
  intros until n.
  induction n.
  - simpl; auto.
  - simpl.
    intros.
    rewrite @Trace.matchM with (i := memD _ _).
    simpl.
    constructor.
    apply IHn.
Qed.

Lemma memD_annhilates_tauN:
  forall {X: Type} (n: nat) (x: Trace X) (mem: memory),
    memD mem (tauN n x) ≡  (memD mem x).
Proof.

  intros.
    rewrite memD_commutes_tauN.
    symmetry.
    apply tauN_eutt.
Qed.




Lemma memD_proper_wrt_ret: forall {X: Type} (x x': Trace X) (mem: memory)
    (XEQ: x ≡ x')
    (XRET: exists x0, x = Trace.Ret x0),
    memD mem x ≡ memD mem x'.
Proof.
  intros until X.
  cofix.
  intros.

  destruct XRET as [x0 XRET].
  rewrite XRET in *. inversion XEQ; subst; forcetrace; try auto.
  Guarded.
  inversion H1; subst.
  + assert (TN: exists n: nat, t = tauN n (Trace.Ret x0)).
    apply untau_count_layers; auto.

    destruct TN as [N TN].
    rewrite TN in *.
    rewrite <- tauN_destruct.
    rewrite memD_commutes_tauN.
    rewrite <- tauN_eutt.


    rewrite @Trace.matchM with (i := memD _ _); simpl.
    reflexivity.

  + assert (CONTRA: ~UnTau t (Trace.Tau t0)).
    apply untau_notau.
    contradiction.
Qed.

  


    
    

(** I want to be able to rewrite inside M.memD for my proof **)
Lemma MemD_proper_wrt_eutt:
  forall {X: Type}
    (x x': Trace X)
    (mem :memory),
    x ≡ x' -> memD mem x ≡ memD mem x'.
Proof.
Admitted.

Instance register_memD_proper_eutt {X: Type}:
  Proper (eq ==> (@EquivUpToTau IO X) ==>
             (@EquivUpToTau IO X)) memD.
Proof.
  intros m1 m2 meq.
  intros x1 x2 xeq.
  subst.
  apply MemD_proper_wrt_eutt; assumption.
Qed.

Require Import Vellvm.Trace.

Check (memD).
Check (mem_step).
(**
x
y
z
x >>= \f -> ....
**)
Theorem memD_commutes_with_bind_fin: forall {X Y: Type}
                                 (trx: Trace X)
                                 (FINTRX: Trace.TraceFinite trx)
                                 (f: X -> Trace Y)
                                 (m: memory),
    let (m', trx') := mem_effect_fin m FINTRX
    in memD m (bindM trx f) ≡
            memD m' (bindM trx' f).
Proof.
  intros until FINTRX.
  induction FINTRX; intros.
  - (* Ret *)
    simpl.
    euttnorm.

  - (* Err *)
    simpl.
    euttnorm.

  - (* Tau *)
    simpl.
    destruct (mem_effect_fin m FINTRX) eqn:EFF.
    euttnorm.
    specialize IHFINTRX with (f:= f) (m:=m).
    rewrite EFF in IHFINTRX.
    auto.
    Guarded.

  - (* Vis *)
    simpl.
    destruct (mem_step e m) eqn:MEMSTEP.
    + euttnorm.
      forcememd.
      rewrite MEMSTEP.
      forcememd.
      
    + euttnorm.
      destruct p eqn:P.
      subst.
      destruct (mem_effect_fin m0 (FINK y)) eqn:EFF.
      subst.
      specialize H with (f := f).
      specialize H with (m := m0).
      specialize H with (y := y).
      destruct (mem_effect_fin m0 (FINK y)) eqn:EFF'.
      inversion EFF; subst.
      euttnorm.
      forcememd.
      rewrite MEMSTEP.
      euttnorm.
Qed.


Theorem memD_commutes_with_bind_fin': forall {X Y: Type}
                                 (trx: Trace X)
                                 (FINTRX: Trace.TraceFinite trx)
                                 (f: X -> Trace Y)
                                 (m: memory),
    memD m (bindM trx f) ≡
            memD (fst (mem_effect_fin m FINTRX)) (bindM (snd (mem_effect_fin m FINTRX)) f).
Proof.
  intros.
  assert (
    let (m', trx') := mem_effect_fin m FINTRX
    in memD m (bindM trx f) ≡
            memD m' (bindM trx' f)).
  apply memD_commutes_with_bind_fin.
  destruct (mem_effect_fin m FINTRX) eqn:EFF.
  simpl in *.
  auto.
Qed.

Check (Ret).

Theorem memD_commutes_with_bind_memEffect: forall {X Y: Type}
                                 (trx: Trace X)
                                 (f: X -> Trace Y)
                                 (m: memory),
    memD m (bindM trx f) ≡
            bindM (memEffect m trx)
            (fun out =>  match out with
                      | (m', x) => memD m' (bindM (Ret x) f)
                      end).
Proof.
  intros until Y.
  cofix CIH.
  intros.
  destruct trx.
  - (* ret *)
    euttnorm.
    rewrite (@Trace.matchM) with (i := memEffect _ _); simpl.
    euttnorm.
    Guarded.
  - (* Vis *)
    rewrite (@Trace.matchM) with (i := memD _ _); simpl.
    rewrite (@Trace.matchM) with (i := memEffect _ _); simpl.
    destruct (mem_step e m) eqn:MEMSTEP.
    + euttnorm.
      constructor.
    + destruct p.
      rewrite (@Trace.matchM) with (i := bindM _ _); simpl.
      constructor.
      Guarded.
      simpl.
      apply CIH with (m := m0) (trx := (k y)) (f :=f).
      Guarded.

  - (* Tau *)
      rewrite (@Trace.matchM) with (i := bindM (Tau _) _); simpl.
      rewrite (@Trace.matchM) with (i := memEffect _ _); simpl.
      rewrite (@Trace.matchM) with (i := bindM (Tau _) _); simpl.
      rewrite (@Trace.matchM) with (i := memD _ _); simpl.
      constructor.
      apply CIH with (m := m) (trx := trx) (f :=f).
      

  - euttnorm.
    Guarded.
    rewrite (@Trace.matchM) with (i := memEffect _ _); simpl.
    euttnorm.
    forcememd.
    Guarded.
Qed.


Theorem rewrite_memD_as_memEffect_fin: forall {X: Type}
                             (trx: Trace X)
                             (FINTRX: Trace.TraceFinite trx)
                             (m: memory),
    let (m', trx') := mem_effect_fin m FINTRX
    in memD m trx ≡
            memD m' (bindM trx' (Ret (Event:=IO) (X:=X))).
Proof.
  intros.
  assert (BIND_RET: memD m trx ≡ memD m (bindM trx (Ret (X:=X)))).
  euttnorm.
  destruct (mem_effect_fin m FINTRX) eqn:MEMEFF.
  rewrite BIND_RET.

  assert (M_EFFECT: let (m', trx') := mem_effect_fin m FINTRX in
      memD m (bindM trx (Ret (X:=X))) ≡
           memD m' (bindM trx' (Ret (X:=X)))).
  apply memD_commutes_with_bind_fin.

  rewrite MEMEFF in M_EFFECT.
  auto.
Qed.


(** Easier version without let in hypothesis **)
Theorem rewrite_memD_as_memEffect_fin': forall {X: Type}
                             (trx: Trace X)
                             (FINTRX: Trace.TraceFinite trx)
                             (m: memory),
     memD m trx ≡
            memD (fst (mem_effect_fin m FINTRX)) (bindM (snd (mem_effect_fin m FINTRX)) (Ret (Event:=IO) (X:=X))).
Proof.
  intros.
  assert (
    let (m', trx') := mem_effect_fin m FINTRX
    in memD m trx ≡
            memD m' (bindM trx' (Ret (Event:=IO) (X:=X)))).
  apply rewrite_memD_as_memEffect_fin.
  destruct (mem_effect_fin m FINTRX); auto.
Qed.

(** Rewrite memD in terms of mem effect. Useful to reason about
 memory effects of arbitrary traces, or to chop a trace at a given point *)
Theorem rewrite_memD_as_memEffect: forall {X: Type}
                                     (trx: Trace X)
                                     (m: memory),
    memD m trx ≡ bindM (memEffect m trx)
      (fun out : memory * X => memD (fst out) (Ret (snd out))).
Proof.
  intros.
  assert (TRX_AS_BIND: memD m trx ≡ memD m (bindM trx (Ret (X:=X)))).
  euttnorm.

  rewrite TRX_AS_BIND.
  rewrite memD_commutes_with_bind_memEffect.

  assert (FNEQ: PointwiseEUTT
            (fun out : memory * X => let (m', x) := out in memD m' (bindM (Ret x) (Ret (X:=X))))
            (fun out : memory * X => memD (fst out) (Ret (snd out)))).
  unfold PointwiseEUTT.
  intros.
  destruct x; euttnorm.
  rewrite FNEQ.
  reflexivity.
Qed.
            
Definition PointwiseMemEffectEUTT {X Y: Type} (f g: X -> Trace Y): Prop :=
  forall (m: memory) (x: X), memEffect m (f x) ≡ memEffect m (g x).


Lemma memEffect_proper_wrt_PointwiseMemEffectEUTT:
  forall {X Y: Type}
    (x: Trace X)
    (f g: X -> Trace Y)
    (FGEQUIV: PointwiseMemEffectEUTT f g)
    (mem :memory),
    memEffect mem (bindM x f) ≡ memEffect mem (bindM x g).
Proof.
  intros.
  generalize dependent x.
  generalize dependent mem.
  cofix CIH.
  intros.

  intros.
  destruct x.
  - rewrite @Trace.matchM with (i := bindM _ f).
    rewrite @Trace.matchM with (i := bindM _ g).
    simpl.
    rewrite @Trace.matchM with (i := memEffect _ (Tau (f x))).
    rewrite @Trace.matchM with (i := memEffect _ (Tau (g x))).
    simpl.
    euttnorm.
    Guarded.

  - rewrite @Trace.matchM with (i := bindM _ f).
    rewrite @Trace.matchM with (i := bindM _ g).
    simpl.
    rewrite @Trace.matchM with (i := memEffect _ (Vis _ _)).
    rewrite @Trace.matchM with
        (i := memEffect _
                        ((Vis e
                              (fun y : Y0 =>
                                 (cofix go (s : M IO X) : M IO Y :=
                                    match s with
                                    | Ret x => Tau (g x)
                                    | @Vis _ _ Y1 e0 k0 => Vis e0 (fun y0 : Y1 => go (k0 y0))
                                    | Tau k0 => Tau (go k0)
                                    | Err s0 => Err s0
                                    end) (k y))))).
    simpl.
    destruct (mem_step e mem).
    + reflexivity.
      Guarded.
    + destruct p. simpl.
      constructor.
      apply CIH.
      Guarded.
  - 
    rewrite @Trace.matchM with (i := memEffect _ (_ (Tau x) f)).
    rewrite @Trace.matchM with (i := memEffect _ (_ (Tau x) g)).
    simpl.
    constructor.
    apply CIH.
    Guarded.

  -
    rewrite @Trace.matchM with (i := memEffect _ (_ (Err s) f)).
    rewrite @Trace.matchM with (i := memEffect _ (_ (Err s) g)).
    simpl.
    reflexivity.
Qed.
  


Lemma MemD_proper_wrt_PointwiseMemEffectEUTT:
  forall {X Y: Type}
    (x: Trace X)
    (f g: X -> Trace Y)
    (FGEQUIV: PointwiseMemEffectEUTT f g)
    (mem :memory),
    memD mem (Trace.bindM x f) ≡ memD mem (Trace.bindM x g).
Proof.
  intros.
  
  repeat rewrite rewrite_memD_as_memEffect.
  unfold PointwiseMemEffectEUTT in FGEQUIV.


  assert (MEMEFF_EQUIV: memEffect mem (bindM x f) ≡ memEffect mem (bindM x g)).
  apply memEffect_proper_wrt_PointwiseMemEffectEUTT; auto.

  rewrite MEMEFF_EQUIV.
  reflexivity.
Qed.



(*
Definition run_with_memory prog : option (Trace dvalue) :=
  let scfg := Vellvm.AstLib.modul_of_toplevel_entities prog in
  match CFG.mcfg_of_modul scfg with
  | None => None
  | Some mcfg =>
    mret
      (memD empty
      ('s <- SS.init_state mcfg "main";
         SS.step_sem mcfg (SS.Step s)))
  end.
*)

(*
Fixpoint MemDFin (m:memory) (d:Trace ()) (steps:nat) : option memory :=
  match steps with
  | O => None
  | S x =>
    match d with
    | Vis (Fin d) => Some m
    | Vis (Err s) => None
    | Tau _ d' => MemDFin m d' x
    | Vis (Eff e)  =>
      match mem_step e m with
      | inr (m', v, k) => MemDFin m' (k v) x
      | inl _ => None
      end
    end
  end%N.
*)

(*
Previous bug: 
Fixpoint MemDFin {A} (memory:mtype) (d:Obs A) (steps:nat) : option mtype :=
  match steps with
  | O => None
  | S x =>
    match d with
    | Ret a => None
    | Fin d => Some memory
    | Err s => None
    | Tau d' => MemDFin memory d' x
    | Eff (Alloca t k)  => MemDFin (memory ++ [undef])%list (k (DVALUE_Addr (pred (List.length memory)))) x
    | Eff (Load a k)    => MemDFin memory (k (nth_default undef memory a)) x
    | Eff (Store a v k) => MemDFin (replace memory a v) k x
    | Eff (Call d ds k)    => None
    end
  end%N.
 *)
End Make.
                        


