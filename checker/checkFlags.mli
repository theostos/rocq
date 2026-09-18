(************************************************************************)
(*         *      The Rocq Prover / The Rocq Development Team           *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

val enable_strict_checks : unit -> unit
(** Reject serialized declarations which disable any of guardedness,
    positivity, universe or elimination checking. This does not silently
    re-enable checks while retaining unchecked metadata in the environment. *)

val allow_definitional_uip : unit -> unit
(** Explicitly permit the definitional-UIP theory extension in strict mode. *)

val strict_checks_enabled : unit -> bool

val set_local_flags : Declarations.typing_flags -> Environ.env -> Environ.env
(** Set flags except for those ignored by the checker (see .ml file for those). *)
