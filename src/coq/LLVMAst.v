(* {{{ LICENSE                                                              *
  * vi: set fdm=marker fdl=0:                                                *
  *                                                                          *
  * Copyright (c) 2012 Raphaël Proust <raphlalou@gmail.com>                  *
  * Copyright (c) 2012 INRIA - Raphaël Proust <raphlalou@gmail.com>          *
  * Copyright (c) 2012 ENS - Raphaël Proust <raphlalou@gmail.com>            *
  * Copyright (c) 2014 OCamlPro - Julien Sagot <ju.sagot@gmail.com>          *
  *                                                                          *
  * Permission to use, copy, modify, and distribute this software for any    *
  * purpose with or without fee is hereby granted, provided that the above   *
  * copyright notice and this permission notice appear in all copies.        *
  *                                                                          *
  * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES *
  * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF         *
  * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR  *
  * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES   *
  * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN    *
  * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF  *
  * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.           *
   }}}                                                                       *)
(*  ------------------------------------------------------------------------- *)
(* Adapted for use in Vellvm by Steve Zdancewic (c) 2017                      *)
(*  ------------------------------------------------------------------------- *)

Require Import compcert.lib.Floats.
Require Import List String Ascii ZArith.
Require Import Vellvm.Util.

Import ListNotations.
Open Scope string_scope.
Open Scope list_scope.

Definition int := Z.
Definition float := Floats.float.  (* 64-bit floating point value *)

Inductive linkage : Set :=
| LINKAGE_Private
| LINKAGE_Internal
| LINKAGE_Available_externally
| LINKAGE_Linkonce
| LINKAGE_Weak
| LINKAGE_Common
| LINKAGE_Appending
| LINKAGE_Extern_weak
| LINKAGE_Linkonce_odr
| LINKAGE_Weak_odr
| LINKAGE_External
.
      
Inductive dll_storage : Set :=
| DLLSTORAGE_Dllimport
| DLLSTORAGE_Dllexport
.      

Inductive visibility : Set :=
| VISIBILITY_Default
| VISIBILITY_Hidden
| VISIBILITY_Protected
.
    
Inductive cconv : Set :=
| CC_Ccc
| CC_Fastcc
| CC_Coldcc
| CC_Cc (cc:int)
.
        
Inductive param_attr : Set :=
| PARAMATTR_Zeroext
| PARAMATTR_Signext
| PARAMATTR_Inreg
| PARAMATTR_Byval
| PARAMATTR_Inalloca
| PARAMATTR_Sret
| PARAMATTR_Align (a:int)
| PARAMATTR_Noalias
| PARAMATTR_Nocapture
| PARAMATTR_Readonly
| PARAMATTR_Nest
| PARAMATTR_Returned
| PARAMATTR_Nonnull
| PARAMATTR_Dereferenceable (a:int)
.
                            
Inductive fn_attr : Set :=
| FNATTR_Alignstack (a:int)
| FNATTR_Alwaysinline
| FNATTR_Builtin
| FNATTR_Cold
| FNATTR_Inlinehint
| FNATTR_Jumptable
| FNATTR_Minsize
| FNATTR_Naked
| FNATTR_Nobuiltin
| FNATTR_Noduplicate
| FNATTR_Noimplicitfloat
| FNATTR_Noinline
| FNATTR_Nonlazybind
| FNATTR_Noredzone
| FNATTR_Noreturn
| FNATTR_Nounwind
| FNATTR_Optnone
| FNATTR_Optsize
| FNATTR_Readnone
| FNATTR_Readonly
| FNATTR_Returns_twice
| FNATTR_Sanitize_address
| FNATTR_Sanitize_memory
| FNATTR_Sanitize_thread
| FNATTR_Ssp
| FNATTR_Sspreq
| FNATTR_Sspstrong
| FNATTR_Uwtable
| FNATTR_String (s:string) (* "no-see" *)
| FNATTR_Key_value (kv : string * string) (* "unsafe-fp-math"="false" *)
| FNATTR_Attr_grp (g:int)
.


Inductive raw_id : Set :=
| Name (s:string)     (* Named identifiers are strings: %argc, %val, %x, @foo, @bar etc. *)  
| Anon (n:int)        (* Anonymous identifiers must be sequentially numbered %0, %1, %2, etc. *)
| Raw  (n:int)        (* Used for code generation -- serializes as %_RAW_0 %_RAW_1 etc. *)
.

Theorem raw_id_eq_dec: forall (a b: raw_id), {a = b } + {a <> b}.
Proof.
  intros.
  decide equality.
  apply Classes.eq_dec_string.
  apply Z.eq_dec.
  apply Z.eq_dec.
Qed.

Hint Resolve raw_id_eq_dec.

Inductive ident : Set :=
| ID_Global (id:raw_id)   (* @id *)
| ID_Local  (id:raw_id)   (* %id *)
.


Theorem ident_eq_dec: forall (a b: ident), {a = b } + {a <> b}.
Proof.
  intros.
  decide equality; apply raw_id_eq_dec.
Qed.

Hint Resolve ident_eq_dec.

(* auxilliary definitions for when we know which case we're in already *)
Definition local_id  := raw_id.
Definition global_id := raw_id.
Definition block_id := raw_id.
Definition function_id := global_id.


Inductive typ : Set :=
| TYPE_I (sz:int)
| TYPE_Pointer (t:typ)
| TYPE_Void
| TYPE_Half
| TYPE_Float
| TYPE_Double
| TYPE_X86_fp80
| TYPE_Fp128
| TYPE_Ppc_fp128
(* | TYPE_Label  label is not really a type *)
(* | TYPE_Token -- used with exceptions *)    
| TYPE_Metadata
| TYPE_X86_mmx
| TYPE_Array (sz:int) (t:typ)
| TYPE_Function (ret:typ) (args:list typ)
| TYPE_Struct (fields:list typ)
| TYPE_Packed_struct (fields:list typ)
| TYPE_Opaque
| TYPE_Vector (sz:int) (t:typ)     (* t must be integer, floating point, or pointer type *)
| TYPE_Identified (id:ident)
.


Inductive icmp : Set := Eq|Ne|Ugt|Uge|Ult|Ule|Sgt|Sge|Slt|Sle.
Inductive fcmp : Set := FFalse|FOeq|FOgt|FOge|FOlt|FOle|FOne|FOrd|FUno|FUeq|FUgt|FUge|FUlt|FUle|FUne|FTrue.


Inductive ibinop : Set :=
| Add (nuw:bool) (nsw:bool)
| Sub (nuw:bool) (nsw:bool)
| Mul (nuw:bool) (nsw:bool)
| Shl (nuw:bool) (nsw:bool)
| UDiv (exact:bool)
| SDiv (exact:bool)
| LShr (exact:bool)
| AShr (exact:bool)
| URem | SRem | And | Or | Xor
.

Inductive fbinop : Set :=
  FAdd | FSub | FMul | FDiv | FRem.

Inductive fast_math : Set :=
  Nnan | Ninf | Nsz | Arcp | Fast.

Inductive conversion_type : Set :=
  Trunc | Zext | Sext | Fptrunc | Fpext | Uitofp | Sitofp | Fptoui |
  Fptosi | Inttoptr | Ptrtoint | Bitcast.

Definition tident : Set := (typ * ident)%type.


(* NOTES: 
  This datatype is more permissive than legal in LLVM:
     - it allows identifiers to appear nested inside of "constant expressions"

  NOTES:
   - Integer expressions: llc parses large integer exps and converts them to some 
     internal form (based on integer size?)
   
   - Float constants: these are always parsed as 64-bit representable floats 
     using ocamls float_of_string function.  If they are used in LLVM as 32-bit 
     rather than 64-bit floats, they are converted when evaluated.

   - Hex constants: these are always parsed as 0x<16-digit> 64-bit exps and
     bit-converted to ocaml's 64-bit float representation.

   - EXP_ prefix denotes syntax that LLVM calls a "value"
   - OP_  prefix denotes syntax that requires further evaluation
 *)
Inductive exp : Set :=
| EXP_Ident   (id:ident)  
| EXP_Integer (x:int)
| EXP_Float   (f:float)
| EXP_Hex     (f:float)  (* See LLVM documentation about hex float constants. *)
| EXP_Bool    (b:bool)
| EXP_Null
| EXP_Zero_initializer
| EXP_Cstring         (s:string)
| EXP_Undef
| EXP_Struct          (fields: list (typ * exp))
| EXP_Packed_struct   (fields: list (typ * exp))
| EXP_Array           (elts: list (typ * exp))
| EXP_Vector          (elts: list (typ * exp))
| OP_IBinop           (iop:ibinop) (t:typ) (v1:exp) (v2:exp)  
| OP_ICmp             (cmp:icmp)   (t:typ) (v1:exp) (v2:exp)
| OP_FBinop           (fop:fbinop) (fm:list fast_math) (t:typ) (v1:exp) (v2:exp)
| OP_FCmp             (cmp:fcmp)   (t:typ) (v1:exp) (v2:exp)
| OP_Conversion       (conv:conversion_type) (t_from:typ) (v:exp) (t_to:typ)
| OP_GetElementPtr    (t:typ) (ptrval:(typ * exp)) (idxs:list (typ * exp))
| OP_ExtractElement   (vec:(typ * exp)) (idx:(typ * exp))
| OP_InsertElement    (vec:(typ * exp)) (elt:(typ * exp)) (idx:(typ * exp))
| OP_ShuffleVector    (vec1:(typ * exp)) (vec2:(typ * exp)) (idxmask:(typ * exp))
| OP_ExtractValue     (vec:(typ * exp)) (idxs:list int)
| OP_InsertValue      (vec:(typ * exp)) (elt:(typ * exp)) (idxs:list int)
| OP_Select           (cnd:(typ * exp)) (v1:(typ * exp)) (v2:(typ * exp)) (* if * then * else *)
.

Lemma exp_eq_dec: forall (e1 e2: exp), {e1 = e2} + {e1 <> e2}.
Proof.
Admitted.
Hint Resolve exp_eq_dec.
  

Definition texp : Set := typ * exp.

Inductive instr_id : Set :=
| IId   (id:raw_id)    (* "Anonymous" or explicitly named instructions *)
| IVoid (n:int)        (* "Void" return type, for "store",  "void call", and terminators.
                           Each with unique number (NOTE: these are distinct from Anon raw_id) *)
.

Lemma instr_id_eq_dec: forall (iid1 iid2: instr_id), {iid1 = iid2} + {iid1 <> iid2}.
Proof.
  decide equality.
  unfold int in *.
  apply Z.eq_dec.
Qed.

Hint Resolve instr_id_eq_dec.

Inductive phi : Set :=
| Phi  (t:typ) (args:list (block_id * exp))
.
       
Inductive instr : Set :=
| INSTR_Op   (op:exp)                        (* INVARIANT: op must be of the form SV (OP_ ...) *)
| INSTR_Call (fn:texp) (args:list texp)      (* CORNER CASE: return type is void treated specially *)
| INSTR_Alloca (t:typ) (nb: option texp) (align:option int) 
| INSTR_Load  (volatile:bool) (t:typ) (ptr:texp) (align:option int)       
| INSTR_Store (volatile:bool) (val:texp) (ptr:texp) (align:option int)
| INSTR_Fence
| INSTR_AtomicCmpXchg
| INSTR_AtomicRMW
| INSTR_Unreachable
| INSTR_VAArg
| INSTR_LandingPad
.

Lemma instr_eq_dec: forall (i1 i2: instr), {i1 = i2} + {i1 <> i2}.
Proof.
  intros.
Admitted.
Hint Resolve instr_eq_dec.

Inductive terminator : Set :=
(* Terminators *)
(* Types in branches are TYPE_Label constant *)
| TERM_Ret        (v:texp)
| TERM_Ret_void
| TERM_Br         (v:texp) (br1:block_id) (br2:block_id) 
| TERM_Br_1       (br:block_id)
| TERM_Switch     (v:texp) (default_dest:block_id) (brs: list (texp * block_id))
| TERM_IndirectBr (v:texp) (brs:list block_id) (* address * possible addresses (labels) *)
| TERM_Resume     (v:texp)
| TERM_Invoke     (fnptrval:tident) (args:list texp) (to_label:block_id) (unwind_label:block_id)
.

Lemma terminator_eq_dec: forall (t1 t2: terminator), {t1 = t2} + {t1 <> t2}.
Proof.
  intros.
Admitted.

Inductive thread_local_storage : Set :=
| TLS_Localdynamic
| TLS_Initialexec
| TLS_Localexec
.

Record global : Set :=
  mk_global {
      g_ident        : global_id;
      g_typ          : typ;
      g_constant     : bool;
      g_exp          : option exp;
      g_linkage      : option linkage;
      g_visibility   : option visibility;
      g_dll_storage  : option dll_storage;
      g_thread_local : option thread_local_storage;
      g_unnamed_addr : bool;
      g_addrspace    : option int;
      g_externally_initialized: bool;
      g_section      : option string;
      g_align        : option int;
}.

Record declaration : Set :=
  mk_declaration
  {
    dc_name        : function_id;  
    dc_type        : typ;    (* INVARIANT: should be TYPE_Function (ret_t * args_t) *)
    dc_param_attrs : list param_attr * list (list param_attr); (* ret_attrs * args_attrs *)
    dc_linkage     : option linkage;
    dc_visibility  : option visibility;
    dc_dll_storage : option dll_storage;
    dc_cconv       : option cconv;
    dc_attrs       : list fn_attr;
    dc_section     : option string;
    dc_align       : option int;
    dc_gc          : option string;
  }.


Definition code := list (instr_id * instr).

Record block : Set :=
  mk_block
    {
      blk_id    : block_id;
      blk_phis  : list (local_id * phi);
      blk_code  : code;
      blk_term  : instr_id * terminator;
    }.

Lemma code_eq_dec: forall (c1 c2: code), {c1 = c2} +  {c1 <> c2}.
Proof.
  decide equality.
  decide equality.
Qed.

Hint Resolve code_eq_dec.

Record definition (FnBody:Set) :=
  mk_definition
  {
    df_prototype   : declaration;
    df_args        : list local_id;
    df_instrs      : FnBody;
  }.

Arguments df_prototype {_} _.
Arguments df_args {_} _.
Arguments df_instrs {_} _.

Inductive metadata : Set :=
  | METADATA_Const  (tv:texp)
  | METADATA_Null
  | METADATA_Id     (id:raw_id)  (* local or global? *)
  | METADATA_String (str:string)
  | METADATA_Named  (strs:list string)
  | METADATA_Node   (mds:list metadata)
.

Inductive toplevel_entity (FnBody:Set) : Set :=
| TLE_Target          (tgt:string)
| TLE_Datalayout      (layout:string)
| TLE_Declaration     (decl:declaration)
| TLE_Definition      (defn:definition FnBody)
| TLE_Type_decl       (id:ident) (t:typ)
| TLE_Source_filename (s:string)
| TLE_Global          (g:global)
| TLE_Metadata        (id:raw_id) (md:metadata)
| TLE_Attribute_group (i:int) (attrs:list fn_attr)
.
Arguments TLE_Target {_} _.
Arguments TLE_Datalayout {_} _.
Arguments TLE_Declaration {_} _.
Arguments TLE_Definition {_} _.
Arguments TLE_Type_decl {_} _.
Arguments TLE_Source_filename {_} _.
Arguments TLE_Global {_} _.
Arguments TLE_Metadata {_} _.
Arguments TLE_Attribute_group {_} _ _.

Definition toplevel_entities (FnBody:Set) : Set := list (toplevel_entity FnBody).

Record modul (FnBody:Set) : Set :=
  mk_modul
  {
    m_name: option string;
    m_target: option string;
    m_datalayout: option string;
    m_type_defs: list (ident * typ);
    m_globals: list global;
    m_declarations: list declaration;
    m_definitions: list (definition FnBody);
  }.

Arguments m_name {_} _.
Arguments m_target {_} _.
Arguments m_datalayout {_} _.
Arguments m_type_defs {_} _.
Arguments m_globals {_} _.
Arguments m_declarations {_} _.
Arguments m_definitions {_} _.


