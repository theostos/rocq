(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

open Declarations

let strict_checks = ref false
let uip_allowed = ref false

let enable_strict_checks () = strict_checks := true
let allow_definitional_uip () = uip_allowed := true
let strict_checks_enabled () = !strict_checks

let validate_flags flags =
  if !strict_checks then begin
    let require enabled name =
      if not enabled then CErrors.user_err
        Pp.(str "Strict checking refuses disabled " ++ str name ++ str " checking.")
    in
    require flags.check_guarded "guard";
    require flags.check_positive "positivity";
    require flags.check_universes "universe";
    require flags.check_eliminations "elimination";
    if flags.allow_uip && not !uip_allowed then CErrors.user_err
      Pp.(str "Strict checking requires explicit -allow-uip for definitional UIP.")
  end

let set_local_flags flags env =
  validate_flags flags;
  (* Explicitly ignored flags are set to not change *)
  let envflags = Environ.typing_flags env in
  let flags = {
    (* These flags may be overridden *)
    check_guarded = flags.check_guarded;
    check_positive = flags.check_positive;
    check_universes = flags.check_universes;
    check_eliminations = flags.check_eliminations;
    conv_oracle = flags.conv_oracle;
    share_reduction = flags.share_reduction;
    unfold_dep_heuristic = flags.unfold_dep_heuristic;
    allow_uip = flags.allow_uip;
    (* These flags may not *)
    enable_VM = envflags.enable_VM;
    enable_native_compiler = envflags.enable_native_compiler;
    indices_matter = envflags.indices_matter;
    impredicative_set = envflags.impredicative_set;
    sprop_allowed = envflags.sprop_allowed;
  }
  in
  Environ.set_typing_flags flags env
