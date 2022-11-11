(**
  * Interface for type-safe programming with C's void pointers based
  * on F*'s notion of monotonic state and monotonic pointers (in which
  * the memory is allowed to evolve only according to a given preorder).
  *)

module Monotonic.VoidPointer

module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack

(**
  * Abstract (monotonic) void pointer type.
  *)
val t:Type0

(**
  * Specifying that `p` originates from upcasting an `a`-typed monotonic 
  * pointer, whose value is allowed to only evolve according to `rel`.
  *)
val is_upcast_of (p: t) (#a: Type0) (rel:B.srel a) : GTot prop

(**
  * Extracting the `a`-typed pointer from a void pointer in ghost code.
  *)
val g_downcast (#a: Type0) (rel:B.srel a) (p: t{p `is_upcast_of` rel}) 
  : GTot (B.mpointer a rel rel)

(**
  * Specifying when a monotonic void pointer is live in given memory.
  *)
noextract
let is_live_in (p: t) (h: HS.mem) : GTot Type0 = 
  exists a (rel:B.srel a). p `is_upcast_of` rel /\ B.live h (g_downcast rel p)

(**
  * Abstract memory footprint of a monotonic void pointer.
  *)
val loc_voidpointer (p: t) : GTot B.loc

(**
  * Disjoint memory modifications preserve liveness of void pointers.
  *)
val lemma_voidpointer_disjoint_elim (p: t) (l: B.loc) (h0 h1: HS.mem)
  : Lemma
    (requires (B.loc_disjoint (loc_voidpointer p) l /\ p `is_live_in` h0 /\ B.modifies l h0 h1))
    (ensures (p `is_live_in` h1))
    [SMTPat (p `is_live_in` h0);
     SMTPat (B.loc_disjoint (loc_voidpointer p) l);
     SMTPat (p `is_live_in` h1)]
