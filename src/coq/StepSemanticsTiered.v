(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 *--------------------------------------------------------------------------- *)

Require Import ZArith List String Omega.
Require Coq.FSets.FMapAVL.
Require Coq.FSets.FMapFacts.
Require Coq.Structures.OrderedTypeEx.

Require Import compcert.lib.Integers compcert.lib.Floats.

Require Import Vellvm.Classes.
Require Import Vellvm.Util.
Require Import Vellvm.Trace.
Require Import Vellvm.LLVMAst.
Require Import Vellvm.AstLib.
Require Import Vellvm.CFG.
Require Import Vellvm.MemoryAddress.
Require Import Vellvm.LLVMIO.
Require Import Vellvm.DynamicValues.
Require Import Vellvm.TypeUtil.
Import ListNotations.


From mathcomp Require ssreflect ssrbool ssrfun bigop.
Import ssreflect.SsrSyntax.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Set Implicit Arguments.
Set Contextual Implicit.

Open Scope Z_scope.
Open Scope string_scope.

(** This module refactors [StepSemantics], so that we express stepping through the
LLVM IR in semantic increments, rather than having a single [step] function which steps
over instructions, from which we try to recover higher level semantics
*)
Module StepSemanticsTiered(A:MemoryAddress.ADDRESS)(LLVMIO:LLVM_INTERACTIONS(A)).

  
  Import LLVMIO.
  
  (**  *Environments *)
  (** This is the same as the original [StepSemantics]. The delta starts
      from "instruction execution" *)
  Module ENV := FMapAVL.Make(AstLib.RawIDOrd).
  Module ENVFacts := FMapFacts.WFacts_fun(AstLib.RawIDOrd)(ENV).
  Module ENVProps := FMapFacts.WProperties_fun(AstLib.RawIDOrd)(ENV).
  
  Definition env_of_assoc {A} (l:list (raw_id * A)) : ENV.t A :=
    List.fold_left (fun e '(k,v) => ENV.add k v e) l (@ENV.empty A).
  
  Definition genv := ENV.t dvalue.
  Definition env  := ENV.t dvalue.


  
  Fixpoint string_of_env' (e:list (raw_id * dvalue)) : string :=
    match e with
    | [] => ""
    | (lid, _)::rest => (string_of_raw_id lid) ++ " " ++ (string_of_env' rest)
    end.

  Instance string_of_env : StringOf env := fun env => string_of_env' (ENV.elements env).
  
  Definition lookup_env {X} (e:ENV.t X) (id:raw_id) : err X :=
    match ENV.find id e with
    | Some v => mret v
    | None => failwith "lookup_env: failed to find id" (* can't include ids in the error ++ (string_of id) *)
    end.

  Definition lookup_id (g:genv) (e:env) (i:ident) : err dvalue :=
    match i with
    | ID_Global x => lookup_env g x
    | ID_Local x => lookup_env e x
    end.

  Definition reverse_lookup_function_id (g:genv) (a:A.addr) : err raw_id :=
    let f x :=
        match x with
        | (_, DVALUE_Addr b) => if a == b then true else false
        | _ => false
        end
    in
    match List.find f (ENV.elements g) with
    | None => failwith "reverse_lookup_function_id failed"
    | Some (fid, _) => mret fid
    end.
  
  Definition add_env := ENV.add.

  
  Section CONVERSIONS.
  (* Conversions can't go into DynamicValues because Int2Ptr and Ptr2Int casts 
     generate memory effects. *) 
  Definition eval_conv_h conv t1 x t2 : Trace dvalue :=
    match conv with
    | Trunc =>
      match t1, x, t2 with
      | TYPE_I 32, DVALUE_I32 i1, TYPE_I 1 =>
        mret (DVALUE_I1 (Int1.repr (Int32.unsigned i1)))
      | TYPE_I 64, DVALUE_I64 i1, TYPE_I 1 =>
        mret (DVALUE_I1 (Int1.repr (Int64.unsigned i1)))
      | TYPE_I 64, DVALUE_I64 i1, TYPE_I 32 =>
        mret (DVALUE_I32 (Int32.repr (Int64.unsigned i1)))
      | _, _, _ => failwith "ill typed-conv"
      end
    | Zext =>
      match t1, x, t2 with
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 32 =>
        mret (DVALUE_I32 (Int32.repr (Int1.unsigned i1)))
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 64 =>
        mret (DVALUE_I64 (Int64.repr (Int1.unsigned i1)))
      | TYPE_I 32, DVALUE_I32 i1, TYPE_I 64 =>
        mret (DVALUE_I64 (Int64.repr (Int32.unsigned i1)))
      | _, _, _ => failwith "ill typed-conv"
      end
    | Sext =>
      match t1, x, t2 with
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 32 =>
        mret (DVALUE_I32 (Int32.repr (Int1.signed i1)))
      | TYPE_I 1, DVALUE_I1 i1, TYPE_I 64 =>
        mret (DVALUE_I64 (Int64.repr (Int1.signed i1)))
      | TYPE_I 32, DVALUE_I32 i1, TYPE_I 64 =>
        mret (DVALUE_I64 (Int64.repr (Int32.signed i1)))
      | _, _, _ => failwith "ill typed-conv"
      end
    | Bitcast =>
      match t1, x, t2 with
      | TYPE_I bits1, x, TYPE_I bits2 =>
        if bits1 =? bits2 then mret x else failwith "unequal bitsize in cast"
      | TYPE_Pointer t1, DVALUE_Addr a, TYPE_Pointer t2 =>
        mret (DVALUE_Addr a) 
      | _, _, _ => failwith "ill-typed_conv"
      end
    | Fptrunc
    | Fpext
    | Uitofp
    | Sitofp
    | Fptoui
    | Fptosi => failwith "TODO: floating point conversion not yet implemented"
    | Inttoptr =>
      match t1, t2 with
      | TYPE_I 64, TYPE_Pointer t => Trace.Vis (ItoP x) mret
      | _, _ => raise "ERROR: Inttoptr got illegal arguments"
      end 
    | Ptrtoint =>
      match t1, t2 with
      | TYPE_Pointer t, TYPE_I 64 => Trace.Vis (PtoI x) mret
      | _, _ => raise "ERROR: Ptrtoint got illegal arguments"
      end
    end.
  Arguments eval_conv_h _ _ _ _ : simpl nomatch.

  
  Definition eval_conv conv t1 x t2 : Trace dvalue :=
    match t1, x with
    | TYPE_I bits, dv =>
        eval_conv_h conv t1 dv t2
    | TYPE_Vector s t, (DVALUE_Vector elts) =>
      (* In the future, implement bitcast and etc with vectors *)
      failwith "vectors unimplemented"
    | _, _ => eval_conv_h conv t1 x t2
    end.
  Arguments eval_conv _ _ _ _ : simpl nomatch.

  End CONVERSIONS.

  Definition dv_zero_initializer (t:dtyp) : err dvalue :=
    failwith "dv_zero_initializer unimplemented".


Section IN_TYPEDEFS_CONTEXT.
  (** Note that we do not depend on the entire mcfg. Rather, we import in piecemeal exactly what we need,
      so that our proofs about these objects don't drag in the entire mcfg. This makes showing
      semantic preservation at least theoretically cleaner.
  *)
  Variable tds: typedefs.

Definition eval_typ (t:typ) : dtyp :=
  TypeUtil.normalize_type tds t.


Section IN_LOCAL_ENVIRONMENT.
Variable g : genv.
Variable e : env.

(** eval_exp is unchanged, except for the fact that it now takes [typedefs], rather than [mcfg] for typeinfo *)
(*
  [eval_exp] is the main entry point for evaluating LLVM expressions.
  top : is the type at which the expression should be evaluated (if any)
  INVARIANT: 
    - top may be None only for 
        - EXP_Ident 
        - OP_* cases

    - top must be Some t for the remaining EXP_* cases
      Note that when top is Some t, the resulting dvalue can never be
      a function pointer for a well-typed LLVM program.
*)
Fixpoint eval_exp (top:option dtyp) (o:exp) {struct o} : Trace dvalue :=
  let eval_texp '(t,ex) :=
             let dt := eval_typ t in
             'v <- eval_exp (Some dt) ex; mret v
  in
  match o with
  | EXP_Ident i => lift_err_d (lookup_id g e i) mret

  | EXP_Integer x =>
    match top with
    | None =>  failwith "eval_exp given untyped EXP_Integer"
    | Some (DTYPE_I bits) => do w <- coerce_integer_to_int bits x; mret w
    | _ => failwith "bad type for constant int"
    end

  | EXP_Float x   =>
    match top with
    | None => failwith "eval_exp given untyped EXP_Float"
    | Some DTYPE_Float  =>  mret (DVALUE_Float (Float32.of_double x))
    | Some DTYPE_Double =>  mret (DVALUE_Double x)
    | _ => failwith "bad type for constant float"
    end

  | EXP_Hex x     =>
    match top with
    | None => failwith "eval_exp given untyped EXP_Hex"
    | Some DTYPE_Float  =>  mret (DVALUE_Float (Float32.of_double x))
    | Some DTYPE_Double =>  mret (DVALUE_Double x)
    | _ => failwith "bad type for constant hex float"
    end

  | EXP_Bool b    =>
    match b with
    | true  => mret (DVALUE_I1 Int1.one)
    | false => mret (DVALUE_I1 Int1.zero)
    end

  | EXP_Null => mret (DVALUE_Addr A.null)

  | EXP_Zero_initializer =>
    match top with
    | None => failwith "eval_exp given untyped EXP_Zero_initializer"
    | Some t => do w <- dv_zero_initializer t; mret w
    end

  | EXP_Cstring s =>
    failwith "EXP_Cstring not yet implemented"

  | EXP_Undef =>
    match top with
    | None => failwith "eval_exp given untyped EXP_Undef"
    | Some t => mret DVALUE_Undef  (* TODO: use t for size? *)
    end

  (* Question: should we do any typechecking for aggregate types here? *)
  (* Option 1: do no typechecking: *)
  | EXP_Struct es =>
    'vs <- map_monad eval_texp es;
      mret (DVALUE_Struct vs)

  (* Option 2: do a little bit of typechecking *)
  | EXP_Packed_struct es =>
    match top with
    | None => failwith "eval_exp given untyped EXP_Struct"
    | Some (DTYPE_Packed_struct _) =>
      'vs <- map_monad eval_texp es;
        mret (DVALUE_Packed_struct vs)
    | _ => failwith "bad type for VALUE_Packed_struct"
    end

  | EXP_Array es =>
    'vs <- map_monad eval_texp es;
      mret (DVALUE_Array vs)
    
  | EXP_Vector es =>
    'vs <- map_monad eval_texp es;
      mret (DVALUE_Vector vs)

  | OP_IBinop iop t op1 op2 =>
    let dt := eval_typ t in
    'v1 <- eval_exp (Some dt) op1;
    'v2 <- eval_exp (Some dt) op2;
    do w <- eval_iop iop v1 v2;
    mret w

  | OP_ICmp cmp t op1 op2 =>
    let dt := eval_typ t in
    'v1 <- eval_exp (Some dt) op1;                   
    'v2 <- eval_exp (Some dt) op2;
    do w <- (eval_icmp cmp) v1 v2;
    mret w

  | OP_FBinop fop fm t op1 op2 =>
    let dt := eval_typ t in    
    'v1 <- eval_exp (Some dt) op1;
    'v2 <- eval_exp (Some dt) op2;
    do w <- eval_fop fop v1 v2;
    mret w

  | OP_FCmp fcmp t op1 op2 =>
    let dt := eval_typ t in
    'v1 <- eval_exp (Some dt) op1;
    'v2 <- eval_exp (Some dt) op2;
    do w <- eval_fcmp fcmp v1 v2;
    mret w
              
  | OP_Conversion conv t1 op t2 =>
    let dt1 := eval_typ t1 in
    'v <- eval_exp (Some dt1) op;
    eval_conv conv t1 v t2

  | OP_GetElementPtr _ (TYPE_Pointer t, ptrval) idxs =>
    let dt := eval_typ t in
    'vptr <- eval_exp (Some DTYPE_Pointer) ptrval;
    'vs <- map_monad (fun '(_, index) => eval_exp (Some (DTYPE_I 32)) index) idxs;
    Trace.Vis (GEP dt vptr vs) mret

  | OP_GetElementPtr _ (_, _) _ =>
    failwith "getelementptr has non-pointer type annotation"
              
  | OP_ExtractElement vecop idx =>
    (*    'vec <- monad_app_snd (eval_exp e) vecop;
    'vidx <- monad_app_snd (eval_exp e) idx;  *)
    failwith "extractelement not implemented" (* TODO: Extract Element *) 
      
  | OP_InsertElement vecop eltop idx =>
(*    'vec <- monad_app_snd (eval_exp e) vecop;
    'v <- monad_app_snd (eval_exp e) eltop;
    'vidx <- monad_app_snd (eval_exp e) idx; *)
    failwith "insertelement not implemented" (* TODO *)
    
  | OP_ShuffleVector vecop1 vecop2 idxmask =>
(*    'vec1 <- monad_app_snd (eval_exp e) vecop1;
    'vec2 <- monad_app_snd (eval_exp e) vecop2;      
    'vidx <- monad_app_snd (eval_exp e) idxmask; *)
    failwith "shufflevector not implemented" (* TODO *)

  | OP_ExtractValue strop idxs =>
    let '(t, str) := strop in
    let dt := eval_typ t in
    'str <- eval_exp (Some dt) str;
    let fix loop str idxs : err dvalue :=
        match idxs with
        | [] => mret str
        | i :: tl =>
          'v <- index_into_str str i;
          loop v tl
        end in
    do w <- loop str idxs;
      mret w
        
  | OP_InsertValue strop eltop idxs =>
    (*
    '(t1, str) <- monad_app_snd (eval_exp e) strop;
    '(t2, v) <- monad_app_snd (eval_exp e) eltop;
    let fix loop str idxs : err dvalue :=
        match idxs with
        | [] => failwith "invalid indices"
        | [i] =>
          insert_into_str str v i
        | i :: tl =>
          '(_, v) <- index_into_str str i;
          'v <- loop v tl;
          insert_into_str str v i
        end in
    loop str idxs*)
    failwith "TODO"
    
  | OP_Select (t, cnd) (t1, op1) (t2, op2) =>
    let dt := eval_typ t in
    let dt1 := eval_typ t1 in
    let dt2 := eval_typ t2 in
    'cndv <- eval_exp (Some dt) cnd;
    'v1 <- eval_exp (Some dt1) op1;
    'v2 <- eval_exp (Some dt2) op2;
    do w <- eval_select cndv v1 v2;
    mret w
  end.
Arguments eval_exp _ _ : simpl nomatch.

Definition eval_op (o:exp) : Trace dvalue :=
  eval_exp None o.
Arguments eval_op _ : simpl nomatch.

End IN_LOCAL_ENVIRONMENT.
End IN_TYPEDEFS_CONTEXT.
(** We split our semantics into instruction, basic block,function, and toplevel "interpreter"
execution. Each of these follow the old model of returning a [result], but this [result] is different between the different layers *)

(** * Semantics of instruction execution  *)
Section INSTRUCTION.
  Inductive InstResult : Type :=
  | IRCall: function_id (**r function to call *)
            -> list (dvalue) (**r parameters *)
            -> instr_id (**r instruction to set return value to *)
            -> instr_id (**r instruction to resume execution from *)
            -> InstResult (**r call a function. *)
  | IRCallVoid: function_id (**r function to call *)
                -> list (dvalue) (**r parameters *)
                -> instr_id (**r instruction to resume execution from *)
                -> InstResult (**r call a function with void return *)
  | IREnvEffect: env  -> InstResult (**r set the [env] **)
  | IRNone (**r  noop *)
  .

(** Note that we immediately get some payoff: reasoning about an
  instruction execution is now a local process, since it is a
  [Definition] that returns a predictable [InstResult].

- This is cleaner than [exec] having to handle both instructions
  and terminators, thereby mixing up issues of control flow with that
  of instruction execution.

- Note that we "bubble up" control flow of function calls
  with a custom [InstResult]. This way, we can predictably reason
  about the state transition which occurs during a function call,
  rather than [magic() + change the pc] *)
  Definition execInst
             (tds: typedefs)
             (ge:  genv)
             (e: env)
             (id: instr_id)
             (i: instr): Trace InstResult :=
    match id, i with
    | IId id, INSTR_Load _ t (u,ptr) _ =>
      'dv <- eval_exp tds ge e (Some (eval_typ tds u)) ptr;
        Trace.Vis (Load (eval_typ tds t) dv)
                  (fun dv => Ret (IREnvEffect (add_env id dv e)))
                  
    | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => 
      'dv <- eval_exp tds ge e (Some (eval_typ tds t)) val; 
        'v <- eval_exp tds ge e(Some (eval_typ tds u)) ptr;
        Trace.Vis (Store v dv) (fun _ => Ret IRNone)
    | IId id, INSTR_Alloca t _ _ =>
      Trace.Vis (Alloca (eval_typ tds t)) (fun (a:dvalue) =>  Ret (IREnvEffect (add_env id a e)))
    | pt, INSTR_Call (t, f) args =>
      'fv <- eval_exp tds ge e None f;
        'dvs <-  map_monad (fun '(t, op) => (eval_exp tds ge e (Some (eval_typ tds t)) op)) args;
        match fv with
        | DVALUE_Addr addr =>
          (* TODO: lookup fid given addr from global environment *)
          do fid <- reverse_lookup_function_id ge addr;
            match pt with
            | IVoid _ => Ret (IRCallVoid fid dvs id)
            | IId _ => Ret (IRCall fid dvs pt id)
                          (* cont (ge, pc_f, env, (KRet e id pc_next::k)) *)
            (* cont (ge, pc_f, env, (KRet_void e pc_next::k)) *)
            (* | IId _ => Ret (IRCall fid bs id id) *)
                          (* cont (ge, pc_f, env, (KRet e id pc_next::k)) *)
            end
        (* 
            match (find_function_entry CFG fid) with
            | Some fnentry =>
              let 'FunctionEntry ids pc_f := fnentry in
              do bs <- combine_lists_err ids dvs;
                match pt with
                | IVoid _ => Ret (IRCallVoid fid bs id)
                  (* cont (ge, pc_f, env, (KRet_void e pc_next::k)) *)
                | IId _ => Ret (IRCall fid bs id id)
                  (* cont (ge, pc_f, env, (KRet e id pc_next::k)) *)
                end
            | None => (* This must have been a registered external function *)
              match fid with
              (* TODO: make sure the external call's type is correct *)
              | Name s => Err "implement external function call"
                (* Trace.Vis (Call DTYPE_Void s dvs)
                                   (fun dv => cont (ge, pc_next, e, k)) *)
              | _ => raise ("step: no function " ++ (string_of fid))
              end
            end
         *)
        | _ => Err  "call got non-function pointer"
        end
    |  _, _ => Err "unimplemented instruction"
    end.
End INSTRUCTION.

(** *Semantics of Terminator execution *)
Section TERMINATOR.
  Inductive TermResult : Type :=
  | TRBreak: block_id -> TermResult (**r Break from current BB into new BB *)
  | TRRet: dvalue -> TermResult (**r Return from the function *)
  | TRRetVoid: TermResult (**r Return void from the function *)
  .

  (** Once again, we exchange a [CoFixpoint] for a [Definition],
  which gives us some measure of local reasoning *)
  Definition execTerm
             (tds: typedefs)
             (ge: genv) (e: env)
             (term: terminator): Trace TermResult :=
  match term with
  | (TERM_Ret (t, op)) =>
    'dv <- eval_exp tds ge e (Some (eval_typ tds t)) op;
      Ret (TRRet dv)
        
  | TERM_Ret_void =>Ret (TRRetVoid)
      
  | TERM_Br (t,op) br1 br2 =>
    'dv <- eval_exp tds ge e(Some (eval_typ tds t)) op; 
    'br <- match dv with 
            | DVALUE_I1 comparison_bit =>
              if Int1.eq comparison_bit Int1.one then
                mret br1
              else
                mret br2
            | _ => failwith "Br got non-bool value"
          end;
    Ret (TRBreak br)
  | TERM_Br_1 bid => Ret (TRBreak bid)
  | _ => Err "unimplemented terminator"
  end.
End TERMINATOR.

(** Location of the current instruction in the BB *)
Definition instr_pt := nat.

(** *Semantics of basic block execution *)
Section BASICBLOCK.
  Inductive BBResult :=
  | BBRBreak: env ->  block_id -> BBResult (**r Break from the current BB to the next BB *)
  | BBRRet:  dvalue -> BBResult (**r Return from the function *)
  | BBRRetVoid:  BBResult  (**r Return void from the function *)
  | BBRCall: env -> (**r environment value *)
             function_id (**r function to call *)
             -> list (dvalue) (**r parameters *)
             -> instr_id (**r return value ID *)
             -> instr_pt (**r instruction to resume execution from *)
             -> block_id (**r BB to resume execution from *)
             -> BBResult (**r Call a function *)
  | BBRCallVoid: env -> function_id -> list (dvalue) -> instr_pt -> block_id -> BBResult
  .

  Definition BBResultFromTermResult (e: env) (tr: TermResult): BBResult :=
    match tr with
    | TRBreak bid => BBRBreak e bid
    | TRRet v =>  BBRRet v
    | TRRetVoid => BBRRetVoid
    end.

  (** TODO: rewrite using [Foldable] or some such equivalent *)
  (** TODO: meditate on this a little bit and try it on a couple
  simple examples to make sure it does what I think it does *)
  (** This function executes a basic block.

    It tries to execute the current instruction if it exists.
    If this was a function call, it creates a [BBRCall] to propogate
    the function call information upwards.
    Otherwise, it recurses to execute the next instruction.

    If there is no current instruction, it executes the terminator of the
    basic block *)
  (** One advantage here is that again, we get a [Fixpoint] for the
  execution of basic block, which are much nicer to deal with that
  CoFixpoint. The hope is that this makes expresing things about basic
  block execution cleaner.

- We allow execution from some [instr_pt] (type alias for nat)
  after the fashion of Steve's [better_pc] branch. This way,
  we do not tie our emantics to that of the instruction name
  in the basic block.

- We need the ability to restart computation from some point when we
  re enter a basic block after a function call.
  *)
  Fixpoint execBBInstrs
           (tds: typedefs)
           (ge: genv)
           (e: env)
           (bbid: block_id)
           (instrs: list (instr_id *instr))
           (term: terminator)
           (pt: instr_pt): Trace BBResult :=
    match instrs with
    | [] =>  Trace.mapM (BBResultFromTermResult e) (execTerm tds ge e term)
    | cons (id, i) irest =>
      'iresult <- (execInst tds ge e id i);
        match iresult with
        | IRCall fnid args retinstid instid =>
          Ret (BBRCall e fnid args retinstid pt bbid)
        | IRCallVoid fnid args instid => Ret (BBRCallVoid e fnid args pt bbid)
        | IREnvEffect e' => execBBInstrs tds ge e' bbid irest term (pt + 1)%nat
        | IRNone => execBBInstrs tds ge e bbid irest term (pt + 1)%nat
        end
    end.

  Fixpoint findInstrsAfterInstr_ (li: list (instr_id * instr))
           (needle: nat) (cur: nat): list (instr_id * instr) :=
    if needle == cur
    then match li with
         | [] => []
         | _::li' => li'
         end
    else match li with
         | [] => []
         | _::li' => findInstrsAfterInstr_ li' needle (cur + 1)
         end.

  Definition findInstrsAfterInstr (li: list (instr_id * instr))
             (needle: nat): list (instr_id * instr) :=
    findInstrsAfterInstr_ li needle 0.
             

  (** Do note that this does not to run PHI nodes **)
  Definition execBBAfterLoc
             (tds: typedefs)
             (ge: genv)
             (e: env)
             (bb: block)
             (loc: nat):
    Trace BBResult := execBBInstrs tds
                                   ge
                                   e
                                   (blk_id bb)
                                   (findInstrsAfterInstr (blk_code bb) loc)
                                   (snd (blk_term bb))
                                   (loc + 1)%nat.

  Check (assoc).
  (**
  let eval_phi (e:env) '(iid, phi t ls) :=
      match assoc RawIDOrd.eq_dec bid_src ls with
      | Some op =>
        let dt := eval_typ t in
        'dv <- eval_exp g e_init (Some dt) op;
          mret (add_env iid dv e)
      | None => failwith ("jump: block " ++ string_of bid_src ++ " not found in " ++ string_of iid)
      end
  in
  match find_block_entry CFG fid bid_tgt with
  | None => raise ("jump: target block " ++ string_of bid_tgt ++ " not found")
  | Some (BlockEntry phis pc_entry) =>
      'e_out <- monad_fold_right eval_phi phis e_init;
      cont (g, pc_entry, e_out, k)
  end.
   *)

                   
  (** *Phi node evaluation
  Phi updates are supposed to be like function calls:
  That is, the entire phi environment should be updated in one-shot.
  So, evaluating a previous phi should not affect the next phi,

  counterexample would be something like:

    entry:
        br counterex
    counterex:
        iv = phi [0, entry] [iv.next, counterex]
        x = phi[0, entry] [y, counterex]
        y = phi [0, entry] [iv.next, counterex]
        iv.next = iv + 1
        br counterex


    According to LLVM semantics, the values should be:
    {iv: 0, x: 0, y: 0}
    {iv:1, y:1, x:0}

   So, we evaluate the phis according to `einit`, while updating and `ecur`.

    *)



  Definition evalPhi (tds: typedefs)
             (ge: genv)
             (prev_blk_id: block_id)
             (einit: env)
             (ecur: env)
             (id_phi: raw_id * phi) : Trace env :=
    match snd id_phi with
    | Phi typ args => 
      match assoc RawIDOrd.eq_dec prev_blk_id args with
      | Some expr =>
        let dt := eval_typ tds typ in
        'dv <- eval_exp tds ge einit (Some dt) expr;
          Ret  (add_env (fst id_phi) dv ecur)
      | None => Err ("jump: block " ++ string_of prev_blk_id ++ " not found in " ++
                                   string_of (fst id_phi))
      end
    end.
  
  
  Definition  evalPhis (tds: typedefs) (ge: genv) (einit: env) (oprev_blk_id: option block_id)
              (phis: list (raw_id * phi)) : Trace env :=
    match oprev_blk_id with
    | Some prev_blk_id => monad_fold_right (evalPhi tds ge prev_blk_id einit) phis einit
    | None => Ret einit
    end.
    
                                   

  (** On adding PHI nodes, we will simply have another
  function call sequenced before the execBBInstrs which executes
  the PHI nodes *)
  Definition execBB (tds: typedefs)
             (ge: genv)
             (e: env)
             (oprev_blk_id: option block_id)
             (bb: block):
    Trace BBResult :=
    bindM (evalPhis tds ge e oprev_blk_id (blk_phis bb))
          (fun e' =>
             execBBInstrs tds ge e'
                          (blk_id bb)
                          (blk_code bb)
                          (snd (blk_term bb))
                          0%nat).
End BASICBLOCK.


Definition pc : Type := instr_pt * block_id * function_id.

(** *Semantics of Function execution *)
Section FUNCTION.
  Inductive FunctionResult :=
  | FRReturn: dvalue -> FunctionResult
  | FRReturnVoid: FunctionResult
  | FRCall: env
            -> function_id
            -> list (dvalue)
            -> instr_id
            -> pc
            -> FunctionResult
  | FRCallVoid: env
                -> function_id
                -> list (dvalue)
                -> pc
                -> FunctionResult.


  (** To execute a function, execute the current basic block.
- If the BB returns a value, return it upwards
- If the BB performs control flow, execute the next BB
- If the BB calls a function, push this information upwards


It is at function level execution that [CoFixpoint] enters back into
the game, since we can provide no guarantees about the termination
capabilities of a function call.
   *)
  CoFixpoint execFunctionAtBBId (tds: typedefs)(ge: genv) (e: env)
             (CFG: cfg) (fnid: function_id) (oprev_blk_id: option block_id) (bbid: block_id): 
    Trace FunctionResult :=
    match find_block (blks CFG) bbid with
    | None => 
      Err "no block found"
    | Some bb =>
      'bbres <- execBB tds ge e oprev_blk_id bb;
        match bbres with
        | BBRBreak e' bbid' => execFunctionAtBBId tds ge e' CFG fnid (Some bbid) bbid' 
        | BBRRet dv => Ret (FRReturn dv)
        | BBRRetVoid => Ret FRReturnVoid
        | BBRCall e' fnid args retinstid instid bbid =>
          Ret (FRCall e' fnid args retinstid (instid, bbid, fnid))
        | BBRCallVoid e' fnid args instid bbid =>
          Ret (FRCallVoid e' fnid args (instid, bbid, fnid))
        end
    end.

  Definition execFunction
             (tds: typedefs)
             (ge: genv)
             (e: env)
             (CFG: cfg)
             (fnid: function_id) : Trace FunctionResult :=
    execFunctionAtBBId tds ge e CFG fnid None (init CFG).

  

  (** Do note that DOES NOT  RUN PHI nodes **)
  CoFixpoint execFunctionAtBBIdAfterLoc (tds: typedefs) (ge: genv) (e: env)
    (CFG: cfg) (fnid: function_id) (bbid: block_id) (loc: instr_pt):
    Trace FunctionResult :=
    match find_block (blks CFG) bbid with
    | None => 
      Err "no block found"
    | Some bb =>
      'bbres <- execBBAfterLoc tds ge e bb loc;
        match bbres with
        | BBRBreak e' bbid' => execFunctionAtBBId tds ge e' CFG fnid (Some bbid) bbid' 
        | BBRRet dv => Ret (FRReturn dv)
        | BBRRetVoid => Ret FRReturnVoid
        | BBRCall e' fnid args retinstid instid bbid =>
          Ret (FRCall e' fnid args retinstid (instid, bbid, fnid))
        | BBRCallVoid e' fnid args instid bbid =>
          Ret (FRCallVoid e' fnid args (instid, bbid, fnid))
        end
    end.
    
    
End FUNCTION.


(** *Semantics of interpreter execution *)
Section INTERPRETER.
  (** Stack frames, same as the old version *)
  Inductive frame : Type :=
  | KRet      (e:env) (retid: instr_id) (pc: pc)
  | KRet_void (e:env) (pc: pc)
  .
  
  Definition stack := list frame.
  Definition InterpreterState : Type := genv * env * stack.
  
  Inductive InterpreterResult :=
  | IRDone (v: dvalue)  (**r Return a value to toplevel *)
  | IREnterFunction (fnid: function_id) (args: list dvalue) (**r Enter into a function *)
  | IRReturnFunction  (fres: FunctionResult) (**r Return from a function *)
  | IRResumeFunction  (pc: pc) (**r Resume execution of a given function *)
  .

(** There is some trade off here with respect to the definition of
[InterpreterResult]. The choices are:
- Wrap the [genv], [env], [stack], and [pc] into a single [State] that is
  passed within the different [InterpreterResult] values.

- Make the [InterpreterResult] values carry
  minimum semantic information required
  (That is the definition I chose here), and then explicitly
  pass the [genv], [env], [stack], and [pc] manually as parameters.
  I do not understand this trade-off very well, and would greatly
  appreciate comments about this *)

  (** TODO: the spurious tau nodes are possible a code smell,
  so I need to think about this a little more carefully *)
  CoFixpoint execInterpreter (ge: genv)
             (e: env) (s: stack) (MCFG: mcfg)
             (ir: InterpreterResult) :
      Trace InterpreterResult :=
    let tds := m_type_defs MCFG
    in
    match ir with
    | IRDone v => Ret (IRDone v)
    | IRResumeFunction pc' =>
      let '(iid, bbid, fnid) := pc' in
      match find_function MCFG fnid with
      | Some CFGDefn =>
        'fres <- execFunctionAtBBIdAfterLoc tds ge e (df_instrs CFGDefn) fnid bbid iid;
          Ret (IRReturnFunction fres)
      | None => Err "unable to find function"
      end
      
    | IREnterFunction fnid fn_arg_dvs =>
      match find_function MCFG fnid with
      | Some CFGDefn =>
        let fn_arg_ids := df_args CFGDefn in
        do fn_args <- combine_lists_err fn_arg_ids fn_arg_dvs;
        let fn_env := env_of_assoc fn_args in
        'fres <- execFunction tds ge fn_env (df_instrs CFGDefn) fnid;
          Ret (IRReturnFunction fres)
                           
      | None => Err "unable to find function"
      end
    | IRReturnFunction fres =>
          match fres with
          | FRReturn retval => match s with
                              | [] => Ret (IRDone retval)
                              | (KRet e' instrid pc) :: s' =>
                                let e'' := e' (* TODO: wrote value *) in
                                Tau (execInterpreter ge e'' s' MCFG (IRResumeFunction pc))

                              | _ => Err "incorrect environment"
                              end
          | FRReturnVoid => match s with
                           | [] => Err "no value to return"
                           | (KRet_void e' pc :: s') =>
                             Tau (execInterpreter ge e s' MCFG (IRResumeFunction pc))
                           | _ => Err "incorrect stack frame"
                           end
          | FRCall e' callfnid argvals retinstid pc =>
            
                               Tau (execInterpreter ge
                                                    e'
                                                    (cons (KRet e' retinstid pc) s)
                                                    MCFG
                                                    (IREnterFunction callfnid argvals))
          | FRCallVoid e' callfnid args pc =>
            Tau (execInterpreter ge
                            e
                            (cons (KRet_void e' pc) s)
                            MCFG
                            (IREnterFunction callfnid args))
                     end
    end.
End INTERPRETER.


CoFixpoint step_sem_tiered
           (ge: genv)
           (e: env)
           (s: stack)
           (MCFG: mcfg)
           (r:InterpreterResult) : Trace dvalue :=
  match r with
  | IRDone v => mret v
  | _ => 'rnext <- execInterpreter ge e s MCFG r ;
          step_sem_tiered ge e s MCFG rnext
  end.

(** *Initializing global section *)
(** The rest of the file is the same as StepSemantics, except for
some plumbing differences that are not very interesting *)

Definition allocate_globals_tiered (tds: typedefs)(gs:list global) : Trace genv :=
  monad_fold_right
    (fun (m:genv) (g:global) =>
       Trace.Vis (Alloca (eval_typ tds (g_typ g))) (fun v => mret (ENV.add (g_ident g) v m))) gs (@ENV.empty _).


Definition register_declaration_tiered (g:genv) (d:declaration) : Trace genv :=
  (* TODO: map dc_name d to the returned address *)
    Trace.Vis (Alloca DTYPE_Pointer) (fun v => mret (ENV.add (dc_name d) v g)).

Definition register_functions_tiered (g:genv)
           (decls: list declaration) :=
  monad_fold_right register_declaration_tiered decls g.
                   (* )
                   ((m_declarations MCFG) ++
                    (List.map df_prototype (m_definitions MCFG)))
*)
  
Definition initialize_globals_tiered (tds: typedefs)
           (gs:list global)
           (g:genv) : Trace unit :=
  monad_fold_right
    (fun (_:unit) (glb:global) =>
       let dt := eval_typ tds (g_typ glb) in
       do a <- lookup_env g (g_ident glb);
       'dv <-
           match (g_exp glb) with
           | None => mret DVALUE_Undef
           | Some e => eval_exp tds g (@ENV.empty _) (Some dt) e
           end;
       Trace.Vis (Store a dv) mret)
    gs tt.
  
Definition build_global_environment_tiered
           (tds: typedefs)
           (gs: list global)
           (decls: list declaration) : Trace genv :=
  'g <- allocate_globals_tiered tds gs;
  'g2 <- register_functions_tiered g decls;
  '_ <- initialize_globals_tiered tds gs g2;
  mret g2.

(* Assumes that the entry-point function is named "fname" and that it takes
   no parameters *)
Definition declarations_in_module_tiered (MCFG: mcfg): list declaration :=
                   ((m_declarations MCFG) ++
                    (List.map df_prototype (m_definitions MCFG))).

Definition init_state_tiered (MCFG: mcfg) (fname:string) :
  Trace (InterpreterResult *genv) :=
  'g <- build_global_environment_tiered (m_type_defs MCFG)
     (m_globals MCFG)
     (declarations_in_module_tiered MCFG);
    mret ((IREnterFunction (Name fname) []), g).

(** *Theorems and lemmas on properties of StepSemanticsTiered, Forcing functions **)
(** Write some lemmas to allow simplification of CoFixpoints without
having to unfold and force them manually. The proof terms are
 horrible if we unfold them *)
Import Trace.MonadVerif.

(** TODO: cleanup repetition in proof with LTac **)

Lemma force_step_sem_tiered:
  forall (e: env)
    (ge: genv)
    (st: stack)
    (MCFG: mcfg)
    (r: InterpreterResult),
    (step_sem_tiered ge e st MCFG r) ≡
                                        ('rnext <- execInterpreter ge e  st MCFG r ;
                                           step_sem_tiered ge e  st MCFG rnext).
Proof.
  intros.
  destruct r.

  - rewrite @Trace.matchM with (i := step_sem_tiered _ _ _ _ (IRDone _)).
    rewrite @Trace.matchM with (i := (execInterpreter _ _ _ _ (IRDone _))).
    simpl.
    euttnorm.
    rewrite @Trace.matchM with (i := step_sem_tiered _ _ _ _ (IRDone _)).
    simpl.
    reflexivity.

  - rewrite @Trace.matchM with (i := step_sem_tiered _ _ _ _ (IREnterFunction _ _)).
    Opaque bindM.
    simpl.
    Transparent bindM.
    destruct (execInterpreter ge e st MCFG (IREnterFunction fnid args)); euttnorm.
    Guarded.

  - Opaque bindM.
    rewrite @Trace.matchM with (i := step_sem_tiered _ _ _ _ (IRReturnFunction _)).
    simpl.
    Transparent bindM.
    destruct (execInterpreter ge e st MCFG (IRReturnFunction fres)); euttnorm.

    
  - Opaque bindM.
    rewrite @Trace.matchM with (i := step_sem_tiered _ _ _ _ (IRResumeFunction _)).
    simpl.
    Transparent bindM.
    destruct (execInterpreter ge e st MCFG (IRResumeFunction _)); euttnorm.
Defined.


Lemma force_exec_bb_instrs:
  forall (tds: typedefs)
    (ge: genv)
    (e: env)
    (bbid: block_id)
    (instrs: list (instr_id *instr))
    (term: terminator)
    (pt: instr_pt),
    execBBInstrs tds ge e bbid instrs term pt  ≡ 
    match instrs with
    | [] =>  Trace.mapM (BBResultFromTermResult e) (execTerm tds ge e term)
    | cons (id, i) irest =>
      'iresult <- (execInst tds ge e id i);
        match iresult with
        | IRCall fnid args retinstid instid =>
          Ret (BBRCall e fnid args retinstid pt bbid)
        | IRCallVoid fnid args instid => Ret (BBRCallVoid e fnid args pt bbid)
        | IREnvEffect e' => execBBInstrs tds ge e' bbid irest term (pt + 1)%nat
        | IRNone => execBBInstrs tds ge e bbid irest term (pt + 1)%nat
        end
    end.
Proof.
  intros.
  induction instrs; reflexivity.
Defined.
  
Lemma force_exec_function_at_bb_id: 
  forall (tds: typedefs)
    (e: env)
    (ge: genv)
    (CFG: cfg)
    (fnid: function_id)
    (bbid: block_id)
    (bb:block)
    (BLK: find_block (blks CFG) bbid = Some bb),
    execFunctionAtBBId tds ge e  CFG fnid bbid ≡
      'bbres <- execBB tds ge e bb;
        match bbres with
        | BBRBreak e' bbid' => execFunctionAtBBId tds ge e' CFG fnid bbid' 
        | BBRRet dv => Ret (FRReturn dv)
        | BBRRetVoid => Ret FRReturnVoid
        | BBRCall e' fnid args retinstid instid bbid =>
          Ret (FRCall e' fnid args retinstid (instid, bbid, fnid))
        | BBRCallVoid e' fnid args instid bbid =>
          Ret (FRCallVoid e' fnid args (instid, bbid, fnid))
        end.
Proof.
Admitted.

Ltac forcesst := do [rewrite force_step_sem_tiered |
                    rewrite force_exec_function_at_bb_id].
End StepSemanticsTiered.