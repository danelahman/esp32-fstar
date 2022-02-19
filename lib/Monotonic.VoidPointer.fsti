(**
  * This module abstracts the tpye void* from C into a verifiable
  * type.
  *)

module Monotonic.VoidPointer

module B = LowStar.Monotonic.Buffer
module HS = FStar.HyperStack

// typedef void* VoidPointer_t
val t:Type0

// abstract predicate stating that the void pointer originates from upcasting an a-pointer
val is_upcast_of (p: t) (#a: Type0) (rel:B.srel a) : GTot prop

// spec level "safe" downcasting of void pointers we know originate from an a-pointer
val g_downcast (#a: Type0) (rel:B.srel a) (p: t{p `is_upcast_of` rel}) : GTot (B.mpointer a rel rel)

// when a void pointer is live in a given heap
let is_live_in (p: t) (h: HS.mem) : GTot Type0 = exists a (rel:B.srel a). p `is_upcast_of` rel /\ B.live h (g_downcast rel p)

// abstract footprint of a void pointer
val loc_voidpointer (p: t) : GTot B.loc

// disjoint memory modifications preserve liveness of void pointers
val lemma_voidpointer_disjoint_elim (p: t) (l: B.loc) (h0 h1: HS.mem)
: Lemma
  (requires (B.loc_disjoint (loc_voidpointer p) l /\ p `is_live_in` h0 /\ B.modifies l h0 h1))
  (ensures (p `is_live_in` h1))
  [SMTPat (p `is_live_in` h0);
   SMTPat (B.loc_disjoint (loc_voidpointer p) l);
   SMTPat (p `is_live_in` h1)]
