(**
  * Instance of monotonic void pointers where the memory is allowed
  * to evolve arbitrarily (i.e., any initial-final values are related).
  *)

module VoidPointer

module VP = Monotonic.VoidPointer

module B = LowStar.Buffer
module HS = FStar.HyperStack

(**
  * Abstract void pointer type.
  *)
let t = VP.t

(**
  * Specifying that `p` originates from upcasting an `a`-typed pointer. 
  *)
let is_upcast_of p a = p `VP.is_upcast_of` (B.trivial_preorder a)

(**
  * Extracting the `a`-typed pointer from a void pointer in ghost code.
  *)
let g_downcast #a p = VP.g_downcast (B.trivial_preorder a) p

(**
  * Specifying when a void pointer is live in given memory.
  *)
noextract
let is_live_in p h = VP.is_live_in p h

(**
  * Abstract memory footprint of a void pointer.
  *)
let loc_voidpointer p = VP.loc_voidpointer p
