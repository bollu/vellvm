(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

;; open Platform
;; open Driver
;; open Assert
;; open Memory

(* Vellvm test cases -------------------------------------------------------- *)


let parse_pp_test path =
  let _ = Platform.verb @@ Printf.sprintf "* processing file: %s\n" path in
  let filename, ext = Platform.path_to_basename_ext path in
  let vll_file = Platform.gen_name !Platform.output_path filename ".v.ll" in
  let dot_s = Platform.gen_name !Platform.output_path filename ".s" in
  try 
    let _ = llc_parse path dot_s in
    let prog = parse_file path in
    let _ = output_file vll_file prog in
    try
      let _ = llc_parse vll_file dot_s in
      ()
    with
    PlatformError _ -> failwith (Printf.sprintf "vellvm output bad file: %s" vll_file)
  with
    PlatformError _ -> ()



let files_of_dir path : string list =
  let tmp_file = gen_name "." ".ll_files" ".tmp" in
  let cmd = Printf.sprintf "find %s -name '*.ll' -print > %s" path tmp_file in
  let () = sh cmd raise_error in 
  let fhandle = open_in tmp_file in
  let rec loop paths =
    try
      loop ((input_line fhandle)::paths)
    with
    | End_of_file -> paths
  in
  let ans = loop [] in
  close_in fhandle;
  let rm_cmd = Printf.sprintf "rm %s" tmp_file in
  let () = sh rm_cmd raise_error in
  ans

let pp_test_of_dir dir =
  Test ("Parsing files in: " ^ dir,
        List.map (fun f -> (f, fun () -> parse_pp_test f)) (files_of_dir dir))
       
let run_dvalue_test (test:SS.dvalue -> bool) path =
  if not (test (run_ll_file path)) then failwith (path ^ " test failed"); ()

let poison_tests =
  ["../tests/llvm-arith/i1/add_nsw.ll";
   "../tests/llvm-arith/i1/add_nuw.ll";
   "../tests/llvm-arith/i1/sub_nsw.ll";
   "../tests/llvm-arith/i1/sub_nuw.ll";
   "../tests/llvm-arith/i32/add_nsw.ll";
   "../tests/llvm-arith/i32/add_nuw.ll";
   "../tests/llvm-arith/i32/ashr_ex.ll";
   "../tests/llvm-arith/i32/lshr_ex.ll";
   "../tests/llvm-arith/i32/mul_nsw.ll";
   "../tests/llvm-arith/i32/mul_nuw.ll";
   "../tests/llvm-arith/i32/sdiv_ex.ll";
   "../tests/llvm-arith/i32/shl_nsw.ll";
   "../tests/llvm-arith/i32/shl_nuw.ll";
   "../tests/llvm-arith/i32/sub_nsw.ll";
   "../tests/llvm-arith/i32/sub_nuw.ll";
   "../tests/llvm-arith/i32/udiv_ex.ll";
   "../tests/llvm-arith/i64/add_nsw.ll";
   "../tests/llvm-arith/i64/add_nuw.ll";
   "../tests/llvm-arith/i64/ashr_ex.ll";
   "../tests/llvm-arith/i64/lshr_ex.ll";
   "../tests/llvm-arith/i64/mul_nsw.ll";
   "../tests/llvm-arith/i64/mul_nuw.ll";
   "../tests/llvm-arith/i64/sdiv_ex.ll";
   "../tests/llvm-arith/i64/shl_nsw.ll";
   "../tests/llvm-arith/i64/shl_nuw.ll";
   "../tests/llvm-arith/i64/sub_nsw.ll";
   "../tests/llvm-arith/i64/sub_nuw.ll";
   "../tests/llvm-arith/i64/udiv_ex.ll";]

let i1_tests : (string * int) list =
  [("../tests/llvm-arith/i1/xor.ll", 0);
   ("../tests/llvm-arith/i1/udiv.ll", 1);
   ("../tests/llvm-arith/i1/srem.ll", 0);
   ("../tests/llvm-arith/i1/or.ll", 1);
   ("../tests/llvm-arith/i1/mul.ll", 0);
   ("../tests/llvm-arith/i1/and.ll", 0);
   ("../tests/llvm-arith/i1/add_twice.ll", 1);
   ("../tests/llvm-arith/i1/urem.ll", 0);
   ("../tests/llvm-arith/i1/sub.ll", 0);
   ("../tests/llvm-arith/i1/sdiv.ll", 1);
   ("../tests/llvm-arith/i1/mul_safe.ll", 0);
   ("../tests/llvm-arith/i1/arith_combo.ll", 0);
   ("../tests/llvm-arith/i1/add_twice_named.ll", 1);
   ("../tests/llvm-arith/i1/add_safe.ll", 1)]

let i32_tests : (string * int) list =
  [  ]

let i64_tests : (string * int) list =
  [  ]
    
let parse_files =
  [  ]

let test_dirs =
  ["../tests/ll/";
   "../tests/llvm-arith/i1/";
   "../tests/llvm-arith/i32/";
   "../tests/llvm-arith/i64/"]

let poison_test = function
  | SS.DVALUE_Poison -> true
  | _ -> false

let undef_test = function
  | SS.DV (Ollvm_ast.VALUE_Undef) -> true
  | _ -> false

let i1_test (i1:StepSemantics.int1) = function
  | SS.DVALUE_I1 i2 ->
     StepSemantics.Int1.eq i1 i2
  | _ -> false

let i32_test (i1:StepSemantics.int32) = function
  | SS.DVALUE_I32 i2 ->
     StepSemantics.Int32.eq i1 i2
  | _ -> false

let i64_test (i1:StepSemantics.int64) = function
  | SS.DVALUE_I64 i2 ->
     StepSemantics.Int64.eq i1 i2
  | _ -> false

let i1_of_int i = StepSemantics.Int1.repr (Camlcoq.Z.of_sint i)

let i32_of_int i = StepSemantics.Int32.repr (Camlcoq.Z.of_sint i)

let i64_of_int i = StepSemantics.Int64.repr (Camlcoq.Z.of_sint i)
                                            
let suite = [Test ("Parsing", List.map (fun f -> (f, fun () -> parse_pp_test f)) parse_files);
             Test ("Poison", List.map (fun f ->
                                 (f, fun () -> run_dvalue_test poison_test f)) poison_tests);
             Test ("I1-arith", List.map (fun (f, i) ->
                                   (f, fun () -> run_dvalue_test (i1_test (i1_of_int i)) f))
                                        i1_tests);
             Test ("I32-arith", List.map (fun (f, i) ->
                                    (f, fun () -> run_dvalue_test (i32_test (i32_of_int i)) f))
                                         i32_tests);
             Test ("I64-arith", List.map (fun (f, i) ->
                                    (f, fun () -> run_dvalue_test (i64_test (i64_of_int i)) f))
                                         i64_tests)] @
              (List.map pp_test_of_dir test_dirs)
