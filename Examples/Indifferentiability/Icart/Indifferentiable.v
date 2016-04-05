(* --------------------------------------------------------------------
 * Copyright (c) - 2006--2012 - IMDEA Software Institute
 * Copyright (c) - 2006--2012 - Inria
 * Copyright (c) - 2006--2012 - Microsoft Coprporation
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

Require Import RO.
Require Import EC.
Require Import Padding.
Require Import Icart.

Module Icart_WE := WE_FROM_PI F PAD.B PAD.A PAD IcartEncoding Icart_PI.

Module Icart_Indifferentiable :=
 Indifferentiability F PAD.B PAD.A PAD IcartEncoding Icart_WE.

(*
Import Icart_Indifferentiable.
Check security_bound.
*)

