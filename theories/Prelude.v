(* Copyright (c) 2026 Alan Lawrence McCann, Mashin, Inc.
   Licensed under MIT. See LICENSE file.

   The governance architecture formalized in this development is the
   subject of pending U.S. patent applications by Mashin, Inc. The
   MIT license applies to these proof sources; it does not grant
   rights under any patents. *)

(** * Prelude: Common Imports and Notation

    Shared imports for the Mashin governance formalization.
    Depends on the Interaction Trees library (coq-itree). *)

From ITree Require Export
  ITree
  ITreeFacts
  Events.State
  Events.Exception.

From ExtLib Require Export
  Structures.Monad
  Structures.MonadState.

From Coq Require Export
  Lists.List
  Strings.String
  Bool.Bool
  Arith.Arith
  Logic.FunctionalExtensionality.

Import MonadNotation.
Import ITreeNotations.

Open Scope itree_scope.
Open Scope monad_scope.
Open Scope string_scope.

(** We use [string] as a simple stand-in for identifiers,
    and [nat] for quantities throughout the formalization. *)
