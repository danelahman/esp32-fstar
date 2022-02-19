(**
  * This module exposes functions to upcast from
  * [UInt32] to [VoidPointer], and vice-versa with downcast.
  * [upcast] ensures that the value is an upcast of [UInt32],
  * and [downcast] ensures that the value is a downcast to
  * [UInt32]. It also requires that the value is a valid
  * upcast of the type.
  *)

module Monotonic.VoidPointer.UInt32

module G = FStar.Ghost

module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module U32 = FStar.UInt32
module VP = Monotonic.VoidPointer

open ESPST

// typedef VoidPointer_t VoidPointer_UInt32_upcast(uint32_t *p)

(**
  * `upcast` takes a pointer (buffer of length 1) to UInt32, and
  * returns a VoidPointer in a STack effect. The function requires
  * that the pointer is alive in memory (i.e., not a dangling pointer),
  * and ensures that 1. the contents in memory remain unchanged, 2. the
  * resulting VoidPointer is an upcast of the UInt32 type, and that 3.
  * the downcasting of this VoidPointer results in the same, initial
  * pointer to UInt32.
  *)
val upcast (rel:G.erased (B.srel U32.t))(p: B.mpointer U32.t rel rel)
    : ESPST VP.t
      (requires (fun h0 -> B.live h0 p))
      (ensures  (fun h0 q h1 -> 
                  h0 == h1 /\ 
                  q `VP.is_upcast_of` rel /\ 
                  VP.g_downcast rel q == p /\ 
                  VP.loc_voidpointer q == B.loc_buffer p))

// typedef uint32_t *VoidPointer_UInt32_downcast(VoidPointer_t p)

(**
  * `downcast` takes a VoidPointer and downcasts it back to a
  * pointer to UInt32. Like `upcast`, `downcast` requires that
  * the pointer is alive in memory, and ensures that the initial
  * and final memory spaces are exactly the same, unchanged.
  * Unlike `upcast`, it requires the VoidPointer to be an upcast
  * of a pointer to UInt32, and ensures that the resulting pointer
  * is, in fact, a downcast from a VoidPointer.
  *)
val downcast (rel:G.erased (B.srel U32.t)) (p: VP.t)
    : ESPST (B.mpointer U32.t rel rel)
      (requires (fun h0 -> p `VP.is_upcast_of` rel /\ B.live h0 (VP.g_downcast rel p)))
      (ensures  (fun h0 q h1 -> 
                  h0 == h1 /\ 
                  q == VP.g_downcast rel p /\
                  VP.loc_voidpointer p == B.loc_buffer q))
