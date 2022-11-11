(**
  * Type-safe upcasts from 32-bit integer pointers to void pointers, 
  * and downcasts from void pointers to 32-bit integer pointers.
  *)

module Monotonic.VoidPointer.UInt32

module G = FStar.Ghost

module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack
module U32 = FStar.UInt32
module VP = Monotonic.VoidPointer

open ESPST

(**
  * Upcasting a 32-bit integer pointer to a void pointer. 
  *
  * The upcasting function requires that:
  * - the given pointer is alive in memory;
  * and the upcasting function ensures that:
  * - the contents in memory remain unchanged, 
  * - the returned void pointer is an upcast of 32-bit integer pointer, and 
  * - downcasting the returned void pointer results in the initial integer pointer.
  *)
val upcast (rel:G.erased (B.srel U32.t))(p: B.mpointer U32.t rel rel)
    : ESPST VP.t
      (requires (fun h0 -> B.live h0 p))
      (ensures  (fun h0 q h1 -> 
                  h0 == h1 /\ 
                  q `VP.is_upcast_of` rel /\ 
                  VP.g_downcast rel q == p /\ 
                  VP.loc_voidpointer q == B.loc_buffer p))

(**
  * Downcasting a void pointer to a 32-bit integer pointer.
  *
  * The downcasting function requires that:
  * - the given void pointer is alive in memory, and
  * - the given void pointer is an upcast of a 32-bit integer pointer;
  * and the downcasting function ensures that:
  * - the contents in memory remain unchanged, and 
  * - upcasting the returned integer pointer results in the initial void pointer.
  *)
val downcast (rel:G.erased (B.srel U32.t)) (p: VP.t)
    : ESPST (B.mpointer U32.t rel rel)
      (requires (fun h0 -> p `VP.is_upcast_of` rel /\ B.live h0 (VP.g_downcast rel p)))
      (ensures  (fun h0 q h1 -> 
                  h0 == h1 /\ 
                  p `VP.is_upcast_of` rel /\
                  q == VP.g_downcast rel p /\
                  VP.loc_voidpointer p == B.loc_buffer q))
