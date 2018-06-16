(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

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

Module StepSemantics(A:MemoryAddress.ADDRESS)(LLVMIO:LLVM_INTERACTIONS(A)).
  
  Import LLVMIO.
  
  (* Environments ------------------------------------------------------------- *)
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


Section IN_CFG_CONTEXT.
Variable CFG:mcfg.

Definition eval_typ (t:typ) : dtyp :=
  TypeUtil.normalize_type (m_type_defs CFG) t.


Section IN_LOCAL_ENVIRONMENT.
Variable g : genv.
Variable e : env.

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

(** Define the semantics of instruction execution **)
Section INSTRUCTION.
  Inductive InstResult : Type :=
  (** Represent calling a function.
IRCall <function-to-call> <args> <instruction ID to write to> <instruction ID to write to> <instruction ID to resume from> **)
  | IRCall: function_id -> list (local_id*dvalue) -> instr_id -> instr_id -> InstResult
  | IRCallVoid: function_id -> list (local_id *dvalue) -> instr_id -> InstResult
  (** Represent modifying the environment **)
  | IREnvEffect: env  -> InstResult
  (** Is a Noop. Note that such instructions can still have memory
   effects by recording against the trace **)
  | IRNone.

  Definition execInst (ge:  genv)
             (e: env)
             (id: instr_id)
             (i: instr): Trace InstResult :=
    match id, i with
    | IId id, INSTR_Load _ t (u,ptr) _ =>
      'dv <- eval_exp ge e (Some (eval_typ u)) ptr;
        Trace.Vis (Load (eval_typ t) dv)
                  (fun dv => Ret (IREnvEffect (add_env id dv e)))
                  
    | IVoid _, INSTR_Store _ (t, val) (u, ptr) _ => 
      'dv <- eval_exp ge e (Some (eval_typ t)) val; 
        'v <- eval_exp ge e(Some (eval_typ u)) ptr;
        Trace.Vis (Store v dv) (fun _ => Ret IRNone)
    | pt, INSTR_Call (t, f) args =>
      'fv <- eval_exp ge e None f;
        'dvs <-  map_monad (fun '(t, op) => (eval_exp ge e(Some (eval_typ t)) op)) args;
        match fv with
        | DVALUE_Addr addr =>
          (* TODO: lookup fid given addr from global environment *)
          do fid <- reverse_lookup_function_id ge addr;
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
        | _ => Err  "call got non-function pointer"
        end
    |  _, _ => Err "foo"
    end.
End INSTRUCTION.

Section TERMINATOR.
  Inductive TermResult : Type :=
  | TRBreak: block_id -> TermResult
  | TRRet: dvalue -> TermResult
  | TRRetVoid: TermResult.

  Definition execTerm (ge: genv) (e: env)
             (term: terminator): Trace TermResult :=
  match term with
  | (TERM_Ret (t, op)) =>
    'dv <- eval_exp ge e (Some (eval_typ t)) op;
      Ret (TRRet dv)
        
  |  TERM_Ret_void =>Ret (TRRetVoid)
      
  | TERM_Br (t,op) br1 br2 =>
    'dv <- eval_exp ge e(Some (eval_typ t)) op; 
    'br <- match dv with 
            | DVALUE_I1 comparison_bit =>
              if Int1.eq comparison_bit Int1.one then
                mret br1
              else
                mret br2
            | _ => failwith "Br got non-bool value"
          end;
    Ret (TRBreak br)
  | _ => Err "unimplemented terminator"
  end.
End TERMINATOR.

(** Define the semantics of basic block execution **)
(** Location of the current instruction in the BB **)
Definition instr_pt := nat.
Section BASICBLOCK.
  Inductive BBResult :=
  | BBRBreak: block_id -> BBResult
  | BBRRet: dvalue -> BBResult
  | BBRRetVoid: BBResult
  (** Call a function, given the function id, arguments,
and point in the basic block to resume from **)
  | BBRCall: function_id -> list (local_id * dvalue) -> instr_id -> instr_pt -> block_id -> BBResult
  | BBRCallVoid: function_id -> list (local_id * dvalue) -> instr_pt -> block_id -> BBResult
  .

  Definition BBResultFromTermResult (tr: TermResult): BBResult :=
    match tr with
    | TRBreak bid => BBRBreak bid
    | TRRet v =>  BBRRet v
    | TRRetVoid => BBRRetVoid
    end.

  (** TODO: rewrite using `Foldable` or some such equivalent **)
  (** TODO: meditate on this a little bit and try it on a couple
  simple examples to make sure it does what I think it does **)
  (** This function executes a basic block.

    It tries to execute the
  current instruction if it exists. If this was a function call,
  then it create a `BBRCall` to propogate the function call information
  upwards. Otherwise, it recurses to execute the next instruction.

  If there is no current instruction, it executes the terminator of the
  basic block **)
  Fixpoint execBBInstrs
           (ge: genv)
           (e: env)
           (bbid: block_id)
           (instrs: list (instr_id *instr))
           (term: terminator)
           (pt: instr_pt): Trace BBResult :=
    match instrs with
    | [] =>  Trace.mapM BBResultFromTermResult (execTerm ge e term)
    | cons (id, i) irest =>
      'iresult <- (execInst ge e id i);
        match iresult with
        | IRCall fnid args retinstid instid =>
          Ret (BBRCall fnid args retinstid pt bbid)
        | IRCallVoid fnid args instid => Ret (BBRCallVoid fnid args pt bbid)
        | _ => execBBInstrs ge e bbid irest term (pt + 1)%nat
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
             

  Definition execBBAfterLoc (ge: genv) (e: env) (bb: block) (loc: nat):
    Trace BBResult := execBBInstrs ge e
                                   (blk_id bb)
                                   (findInstrsAfterInstr (blk_code bb) loc)
                                   (snd (blk_term bb))
                                   (loc + 1)%nat.
                                   

  (** TODO: add PHI nodes! **)
  (** TODO: consider if the terminator may need it's ID?**)
  Definition execBB (ge: genv) (e: env) (bb: block):
    Trace BBResult := execBBInstrs ge e
                                   (blk_id bb)
                                   (blk_code bb)
                                   (snd (blk_term bb))
                                   0%nat.
End BASICBLOCK.


Definition pc : Type := instr_pt * block_id * function_id.

(** Define semantics of executing a function **)
Section FUNCTION.
  Inductive FunctionResult :=
  | FRReturn: dvalue -> FunctionResult
  | FRReturnVoid: FunctionResult
  | FRCall: function_id -> list (local_id * dvalue) -> instr_id -> 
            pc -> FunctionResult
  | FRCallVoid: function_id -> list (local_id * dvalue) ->
                pc -> FunctionResult.


  (** To execute a function, execute a basic block.
  - If it is returning a value, return it upwards
  -  If it is performing control flow, execute the next BB
  - If it is calling a function, push this information toplevel
   *)
  CoFixpoint execFunctionAtBBId (ge: genv) (e: env)
    (CFG: cfg) (fnid: function_id) (bbid: block_id):
    Trace FunctionResult :=
    match find_block (blks CFG) bbid with
    | None => 
      Err "no block found"
    | Some bb =>
      'bbres <- execBB ge e bb;
        match bbres with
        | BBRBreak bbid' => execFunctionAtBBId ge e CFG fnid bbid' 
        | BBRRet dv => Ret (FRReturn dv)
        | BBRRetVoid => Ret FRReturnVoid
        | BBRCall fnid args retinstid instid bbid =>
          Ret (FRCall fnid args retinstid (instid, bbid, fnid))
        | BBRCallVoid fnid args instid bbid =>
          Ret (FRCallVoid fnid args (instid, bbid, fnid))
        end
    end.

  Definition execFunction (ge: genv)
             (e: env)
             (CFG: cfg)
             (fnid: function_id) : Trace FunctionResult :=
    execFunctionAtBBId ge e CFG fnid (init CFG).

  

  CoFixpoint execFunctionAtBBIdAfterLoc (ge: genv) (e: env)
    (CFG: cfg) (fnid: function_id) (bbid: block_id) (loc: instr_pt):
    Trace FunctionResult :=
    match find_block (blks CFG) bbid with
    | None => 
      Err "no block found"
    | Some bb =>
      'bbres <- execBBAfterLoc ge e bb loc;
        match bbres with
        | BBRBreak bbid' => execFunctionAtBBId ge e CFG fnid bbid' 
        | BBRRet dv => Ret (FRReturn dv)
        | BBRRetVoid => Ret FRReturnVoid
        | BBRCall fnid args retinstid instid bbid =>
          Ret (FRCall fnid args retinstid (instid, bbid, fnid))
        | BBRCallVoid fnid args instid bbid =>
          Ret (FRCallVoid fnid args (instid, bbid, fnid))
        end
    end.
    
    
End FUNCTION.


Section INTERPRETER.
  (** What is local_id?
   Ah, it's just an alias for ID **)
  Inductive frame : Type :=
  | KRet      (e:env) (retid: instr_id) (pc: pc)
  | KRet_void (e:env) (pc: pc)
  .       
  Definition stack := list frame.
  Definition InterpreterState : Type := genv * env * stack.
  
  Inductive InterpreterResult :=
  | IRDone (v: dvalue)
  | IREnterFunction (fnid: function_id) (args: list (local_id *dvalue))
  | IRReturnFunction  (fres: FunctionResult)
  | IRResumeFunction  (pc: pc)
  .


  (** TODO: the spurious tau nodes are possible a code smell,
  so I need to think about this a little more carefully **)
  CoFixpoint execInterpreter (ge: genv)
             (e: env) (s: stack) (MCFG: mcfg)
             (ir: InterpreterResult) :
    Trace InterpreterResult :=
    match ir with
    | IRDone v => Ret (IRDone v)
    | IRResumeFunction pc' =>
      let '(iid, bbid, fnid) := pc' in
      match find_function MCFG fnid with
      | Some CFGDefn =>
        'fres <- execFunctionAtBBIdAfterLoc ge e (df_instrs CFGDefn) fnid bbid iid;
          Ret (IRReturnFunction fres)
      | None => Err "unable to find function"
      end
      
    | IREnterFunction fnid args =>
      match find_function MCFG fnid with
      | Some CFGDefn =>
        let fn_env := env_of_assoc args in
        'fres <- execFunction ge fn_env (df_instrs CFGDefn) fnid;
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
            
          | FRCall callfnid args retinstid pc =>
            Tau (execInterpreter ge
                            e
                            (cons (KRet e retinstid pc) s)
                            MCFG
                            (IREnterFunction callfnid args))
          | FRCallVoid callfnid args pc =>
            Tau (execInterpreter ge
                            e
                            (cons (KRet_void e pc) s)
                            MCFG
                            (IREnterFunction callfnid args))
                     end
    end.
End INTERPRETER.