(* -------------------------------------------------------------------------- *
 *                     Vellvm - the Verified LLVM project                     *
 *                                                                            *
 *     Copyright (c) 2017 Steve Zdancewic <stevez@cis.upenn.edu>              *
 *                                                                            *
 *   This file is distributed under the terms of the GNU General Public       *
 *   License as published by the Free Software Foundation, either version     *
 *   3 of the License, or (at your option) any later version.                 *
 ---------------------------------------------------------------------------- *)

Require Import Vellvm.Classes.
Require Import Vellvm.LLVMIO.
Require Import Vellvm.StepSemantics.
Require Import Vellvm.StepSemanticsTiered.
Require Import Vellvm.Memory.

Module IO := LLVMIO.Make(Memory.A).
Module M := Memory.Make(IO).
Module SS := StepSemantics(Memory.A)(IO).
Module SST := StepSemanticsTiered(Memory.A)(IO).

Import IO.
Export IO.DV.

Definition run_mcfg_with_memory (mcfg: CFG.mcfg) : Trace DV.dvalue :=
      (M.memD M.empty
      ('s <- SS.init_state mcfg "main";
         SS.step_sem mcfg (SS.Step s))).

Check (run_mcfg_with_memory).


Definition run_mcfg_with_memory_tiered (mcfg: CFG.mcfg) : Trace DV.dvalue :=
  M.memD M.empty
         (Trace.bindM (SST.init_state_tiered mcfg "main")
         (fun x => let '(ir, ge) := x in
                (SST.step_sem_tiered ge (@SST.ENV.empty dvalue) nil mcfg ir))).



Definition run_with_memory prog : option (Trace DV.dvalue) :=
  let scfg := Vellvm.AstLib.modul_of_toplevel_entities prog in
  match CFG.mcfg_of_modul scfg with
  | None => None
  | Some mcfg => Some (run_mcfg_with_memory mcfg)
  end.



Definition run_with_memory_tiered prog : option (Trace DV.dvalue) :=
  let scfg := Vellvm.AstLib.modul_of_toplevel_entities prog in
  match CFG.mcfg_of_modul scfg with
  | None => None
  | Some mcfg => Some (run_mcfg_with_memory_tiered mcfg)
  end.

