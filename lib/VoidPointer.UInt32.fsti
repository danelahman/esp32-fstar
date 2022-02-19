(**
  * This module exposes functions to upcast from
  * [UInt32] to [VoidPointer], and vice-versa with downcast.
  * [upcast] ensures that the value is an upcast of [UInt32],
  * and [downcast] ensures that the value is a downcast to
  * [UInt32]. It also requires that the value is a valid
  * upcast of the type.
  *)

module VoidPointer.UInt32

module B = LowStar.Buffer

module HS = FStar.HyperStack
module U32 = FStar.UInt32

module VP = VoidPointer
module VPU32 = Monotonic.VoidPointer.UInt32

open ESPST

(**
  * `upcast` takes a pointer (buffer of length 1) to UInt32, and
  * returns a VoidPointer in a STack effect. The function requires
  * that the pointer is alive in memory (i.e., not a dangling pointer),
  * and ensures that 1. the contents in memory remain unchanged, 2. the
  * resulting VoidPointer is an upcast of the UInt32 type, and that 3.
  * the downcasting of this VoidPointer results in the same, initial
  * pointer to UInt32.
  *)
let upcast (p:B.pointer U32.t) 
    : ESPST VP.t
      (requires (fun h0 -> B.live h0 p))
      (ensures (fun h0 q h1 -> h0 == h1 /\ q `VP.is_upcast_of` U32.t /\ VP.g_downcast q == p)) =
  VPU32.upcast (B.trivial_preorder U32.t) p

(**
  * `downcast` takes a VoidPointer and downcasts it back to a
  * pointer to UInt32. Like `upcast`, `downcast` requires that
  * the pointer is alive in memory, and ensures that the initial
  * and final memory spaces are exactly the same, unchanged.
  * Unlike `upcast`, it requires the VoidPointer to be an upcast
  * of a pointer to UInt32, and ensures that the resulting pointer
  * is, in fact, a downcast from a VoidPointer.
  *)
let downcast (p: VP.t)
    : ESPST (B.pointer U32.t)
      (requires (fun h0 -> p `VP.is_upcast_of` U32.t /\ B.live h0 (VP.g_downcast #U32.t p)))
      (ensures (fun h0 q h1 -> h0 == h1 /\ q == VP.g_downcast #U32.t p)) =
  VPU32.downcast (B.trivial_preorder U32.t) p


