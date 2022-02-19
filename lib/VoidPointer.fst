(**
  * This module abstracts the tpye void* from C into a verifiable
  * type.
  *)

module VoidPointer

module VP = Monotonic.VoidPointer

module B = LowStar.Buffer
module HS = FStar.HyperStack

// typedef void* VoidPointer_t
let t = VP.t

// abstract predicate stating that the void pointer originates from upcasting an a-pointer
let is_upcast_of p a = p `VP.is_upcast_of` (B.trivial_preorder a)

// spec level "safe" downcasting of void pointers we know originate from an a-pointer
let g_downcast #a p = VP.g_downcast (B.trivial_preorder a) p

// when a void pointer is live in a given heap
let is_live_in p h = VP.is_live_in p h

// abstract footprint of a void pointer
let loc_voidpointer p = VP.loc_voidpointer p
