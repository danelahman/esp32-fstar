module ESPST

module HS = FStar.HyperStack
module MHS = FStar.Monotonic.HyperStack

module B = LowStar.Monotonic.Buffer
module VP = Monotonic.VoidPointer

module U32 = FStar.UInt32

open FStar.Ghost

module M = FStar.Map

open GPIO.Constants

include FStar.HyperStack.ST

open LowStar.BufferOps

(**
  * Ghost state that tracks: 
  * - if the ISR handler service has been installed (using `option` type); and
  * - the arguments/resources held by individual installed ISR handlers
  *   (using a map from GPIO pins to void pointers denoting these resources).
  *
  * This way we ensure that one cannot deallocate the given argument/resource 
  * before any associated ISR handlers have been uninstalled.
  *
  * Assumed via a `let` and `admit ()` as opposed to an `assume val` so as to
  * avoid the `isr_map` name being extracted to `ESPST.h` header file.
  *) 
noextract
let isr_map_erased (_:unit) 
  : Tot (r:ref (erased (option (M.t gpio_num_t VP.t))){HS.frameOf r == HS.root}) 
  = admit ()

noextract
let isr_map = isr_map_erased ()

(**
  * Various predicates concerning the ghost state, and the 
  * arguments/resources the ghost state maps GPIO pins to.
  *)
noextract
let isr_live_in (h: HS.mem) : GTot Type0 =
  h `HS.contains` isr_map /\
  (Some? (HS.sel h isr_map) ==>
   (let m = Some?.v (HS.sel h isr_map) in
     forall n. m `M.contains` n ==> VP.is_live_in (M.sel m n) h))

noextract
let isr_installed (h: HS.mem) : GTot Type0 = Some? (MHS.sel h isr_map)

noextract
let isr_empty (h: HS.mem) : GTot Type0 = 
  match reveal (MHS.sel h isr_map) with
  | None -> False
  | Some m ->  M.domain m == FStar.Set.empty

noextract
let isr_contains (h: HS.mem) (n: gpio_num_t) : GTot Type = 
  match reveal (MHS.sel h isr_map) with
  | None -> False
  | Some m -> m `M.contains` n

noextract
let isr_sel (h: HS.mem) (n: gpio_num_t{h `isr_contains` n}) : GTot VP.t =
  match reveal (MHS.sel h isr_map) with
  | Some m -> M.sel m n

noextract
let isr_unmodified (h0 h1: HS.mem) : GTot Type0 = 
  MHS.sel h1 isr_map == MHS.sel h0 isr_map

noextract
let isr_updated_with (h0 h1: HS.mem) (n: gpio_num_t) (p: VP.t) : GTot Type0 =
  match reveal (MHS.sel h0 isr_map) with
  | None -> False
  | Some m -> MHS.sel h1 isr_map == hide (Some (M.upd m n p))

noextract
let isr_disjoint_from #a #rrel #rel (p: B.mpointer a rrel rel) : GTot Type0 =
  B.loc_disjoint (B.loc_addr_of_buffer p) (B.loc_mreference isr_map)

noextract
let isr_disjoint_from_resources #a #rrel #rel (h: HS.mem) (p: B.mpointer a rrel rel) : GTot Type0 =
  h `HS.contains` isr_map /\
  (Some? (HS.sel h isr_map) ==>
   (let m = Some?.v (HS.sel h isr_map) in
     forall n. m `M.contains` n ==> B.loc_disjoint (B.loc_addr_of_buffer p) (VP.loc_voidpointer (M.sel m n))))

(*
let isr_not_modified (h0 h1: HS.mem) : GTot Type0 =
  (forall n . h0 `isr_contains` n /\ h1 `isr_contains` n /\ isr_sel h0 n == isr_sel h1 n ==> 
    (let p = isr_sel h1 n in
     forall a (rel:B.srel a). p `VP.is_upcast_of` rel ==> B.get h0 (VP.g_downcast rel p) 0 == B.get h1 (VP.g_downcast rel p) 0))
*)

(**
  * An effect for programming ESP computations. As part of its precondition, 
  * it requires the arguments/resources mapped by the ghost state to live before
  * running an ESPST-computation; As part of its postcondition, it ensures 
  * that the arguments/resources mapped by the ghost state remain live after
  * running an ESPST-computation. Importantly, the value of the ghost state 
  * can change during an ESPST-computation, e.g., when installing an ISR handler.
  *)
noextract
let wp_monotonic #a (wp:st_wp a) : Type0 =
  forall p1 p2 h0. (forall x h1. p1 x h1 ==> p2 x h1) ==> wp p1 h0 ==> wp p2 h0

noextract
type espst_wp a = wp:(st_wp a){wp_monotonic wp}

let espst_repr (a:Type) (wp:espst_wp a) =
  unit -> STATE a (fun p h0 -> wp (fun x h1 -> isr_live_in h1 ==> p x h1) h0 /\ isr_live_in h0)

noextract
unfold
let espst_return_wp a x : espst_wp a =
  fun p h0 -> p x h0

inline_for_extraction
let espst_return a x : espst_repr a (espst_return_wp a x) =
  fun _ -> x

noextract
unfold
let espst_bind_wp a b 
  (wp1:espst_wp a) 
  (wp2:a -> espst_wp b)
  : espst_wp b =
  fun p h0 -> wp1 (fun x h1 -> wp2 x p h1) h0

inline_for_extraction
let espst_bind a b 
  (wp1:espst_wp a) (wp2:a -> espst_wp b)
  (c1:espst_repr a wp1)
  (c2:(x:a -> espst_repr b (wp2 x)))
  : espst_repr b (espst_bind_wp a b wp1 wp2) =
  fun _ -> let x = c1 () in 
        c2 x ()

inline_for_extraction
let espst_subcomp a
  (wp1:espst_wp a) (wp2:espst_wp a)
  (c:espst_repr a wp1)
  : Pure (espst_repr a wp2)
      (requires (forall p h0. wp2 p h0 ==> wp1 p h0))
      (ensures  (fun _ -> True)) = 
  c

noextract
unfold
let espst_if_then_else_wp a b
  (wp1:espst_wp a) (wp2:espst_wp a)
  : espst_wp a =
  fun p h0 -> (b ==> wp1 p h0) /\ ((~b) ==> wp2 p h0)

inline_for_extraction
let espst_if_then_else a
  (wp1:espst_wp a) (wp2:espst_wp a)
  (f:espst_repr a wp1)
  (g:espst_repr a wp2)
  (b:bool)
  : Type = 
  espst_repr a (espst_if_then_else_wp a b wp1 wp2)

reifiable 
reflectable
layered_effect {
  ESPSTATE : a:Type -> wp:espst_wp a -> Effect
  with repr         = espst_repr;
       return       = espst_return;
       bind         = espst_bind;
       subcomp      = espst_subcomp;
       if_then_else = espst_if_then_else
}

unfold
let lift_div_wp (a:Type) (wp:pure_wp a) : espst_wp a = 
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  fun p h0 -> wp (fun x -> p x h0)

inline_for_extraction
let lift_div_espst (a:Type) (wp:pure_wp a) (c:eqtype_as_type unit -> DIV a wp)
  : espst_repr a (lift_div_wp a wp) = 
  FStar.Monotonic.Pure.elim_pure_wp_monotonicity wp;
  fun _ -> c ()

sub_effect DIV ~> ESPSTATE = lift_div_espst

effect ESPST (a:Type) (pre:st_pre) (post:(h0: HS.mem -> Tot (st_post a))) =
  ESPSTATE a (fun p h0 -> pre h0 /\ isr_live_in h0 /\ (forall x h1 . pre h0 /\ post h0 x h1 /\ equal_stack_domains h0 h1 /\ isr_live_in h1 ==> p x h1))


(**
  * Reification and extraction of the ESPST effect.
  *)
effect ESPST_Extract (a:Type) (pre:st_pre) (post:(h0: HS.mem -> Tot (st_post a))) =
  ST a (requires (fun h0 -> pre h0 /\ isr_live_in h0)) 
       (ensures  (fun h0 x h1 -> post h0 x h1 /\ isr_live_in h1))

inline_for_extraction
let extract_st #a #pre #post ($c:unit -> ESPST a pre post)
  : ESPST_Extract a (requires pre) 
                    (ensures  post) =  
  reify (c ()) () 

inline_for_extraction
let unextract_st #a #pre #post ($c:unit -> ESPST_Extract a pre post)
  : ESPST a (requires pre) (ensures  post) =
  ESPSTATE?.reflect (fun _ -> c ())



(**
  * ***********************************************
  * ******* Lifting ST operations to ESPST. *******
  * 
  * The auxiliary effects defined below mimic those 
  * in the underlying hyperstack memory mode.
  * ***********************************************
  *)

(**
  * Pushing and popping frames on and off the stack.
  *)
effect ESPST_Unsafe (a:Type) (pre:st_pre) (post:(h0: HS.mem -> Tot (st_post a))) =
  ESPSTATE a (fun p h0 -> pre h0 /\ isr_live_in h0 /\ (forall x h1 . pre h0 /\ post h0 x h1 /\ isr_live_in h1 ==> p x h1))

noextract
inline_for_extraction
let push_frame () 
  : ESPST_Unsafe unit (requires (fun _ -> True)) 
                      (ensures  (fun h0 _ h1 -> HS.fresh_frame h0 h1 /\ isr_unmodified h0 h1)) =
  ESPSTATE?.reflect (fun _ -> push_frame ())

noextract
inline_for_extraction
let pop_frame ()
  : ESPST_Unsafe unit (requires (fun h0 -> HS.poppable h0 /\
                                        (isr_live_in (HS.pop h0))))
                      (ensures  (fun h0 _ h1 -> HS.poppable h0 /\ h1 == HS.pop h0 /\ HS.popped h0 h1 /\ isr_unmodified h0 h1)) =
  ESPSTATE?.reflect (fun _ -> pop_frame ())

(**
  * Allocate a pointer on the stack.
  *)
effect ESPST_Inline (a:Type) (pre:st_pre) (post:(h0: HS.mem -> Tot (st_post a))) =
  ESPSTATE a (fun p h0 -> 
               pre h0 /\ HS.is_stack_region (HS.get_tip h0) /\ isr_live_in h0 /\ 
               (forall x h1 . pre h0 /\ post h0 x h1 /\ inline_stack_inv h0 h1 /\ isr_live_in h1 ==> p x h1))
   
noextract
inline_for_extraction
let malloca (#a:Type0) (#rrel:B.srel a)
  (init:a) (len:U32.t)
  : ESPST_Inline (B.mpointer a rrel rrel)
          (requires (fun _ -> B.alloca_pre 1ul))
          (ensures  (fun h0 b h1 -> B.alloc_post_mem_common b h0 h1 (Seq.create 1 init) /\
		                 B.frameOf b == HS.get_tip h0)) =
  ESPSTATE?.reflect (fun _ -> recall isr_map;
                           B.malloca #a #rrel init 1ul)

(**
  * Allocate a pointer on the heap.
  *)
noextract
inline_for_extraction
let mmalloc (#a:Type0) (#rrel:B.srel a)
  (r:HS.rid) (init:a)
  : ESPST (b:B.mpointer a rrel rrel{B.frameOf b == r /\ B.freeable b})
          (requires (fun _ -> B.malloc_pre r 1ul))
          (ensures  (fun h0 b h1 -> B.alloc_post_mem_common b h0 h1 (Seq.create 1 init))) =
  ESPSTATE?.reflect (fun _ -> recall isr_map;
                           B.mmalloc #a #rrel r init 1ul)


(**
  * Freeing a heap-allocated pointer.
  *)
let lemma_free_preserves_isr_inv (#a:Type0) (#rrel #rel:B.srel a) (b:B.mpointer a rrel rel) (h0 h1:HS.mem)
  : Lemma (requires (
            B.live h0 b /\
            B.freeable b /\ 
            (not (B.g_is_null b)) /\
            Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
            (HS.get_tip h1) == (HS.get_tip h0) /\
            B.modifies (B.loc_addr_of_buffer b) h0 h1 /\
            HS.live_region h1 (B.frameOf b) /\
            isr_live_in h0 /\ 
            isr_disjoint_from b /\
            isr_disjoint_from_resources h0 b))
          (ensures (
            isr_live_in h1))
          [SMTPat (B.freeable #a #rrel #rel b);
           SMTPat (isr_live_in h0);
           SMTPat (isr_live_in h1)] =
  B.modifies_mreference_elim isr_map (B.loc_addr_of_buffer b) h0 h1

noextract
inline_for_extraction
let free (#a:Type0) (#rrel #rel:B.srel a) (b:B.mpointer a rrel rel)
  : ESPST unit (requires (fun h0 -> B.live h0 b /\ 
                                 B.freeable b /\ 
                                 isr_disjoint_from b /\
                                 isr_disjoint_from_resources h0 b))
               (ensures  (fun h0 _ h1 -> (not (B.g_is_null b)) /\
                                      Map.domain (HS.get_hmap h1) `Set.equal` Map.domain (HS.get_hmap h0) /\
                                      (HS.get_tip h1) == (HS.get_tip h0) /\
                                      B.modifies (B.loc_addr_of_buffer b) h0 h1 /\
                                      HS.live_region h1 (B.frameOf b))) = 
  ESPSTATE?.reflect (fun _ -> B.free b)


(**
  * Looking up a pointer.
  *)
noextract
inline_for_extraction
let ( !* ) (#a:Type0) (#rrel #rel:B.srel a) (p:B.mpointer a rrel rel):
  ESPST a (requires (fun h -> B.live h p))
          (ensures  (fun h0 x h1 -> B.live h1 p /\ x == B.get h0 p 0 /\ h1 == h0)) =
  ESPSTATE?.reflect (fun _ -> !* p)

(**
  * Updating a pointer.
  *)
noextract
inline_for_extraction
let ( *= ) (#a:Type0) (#rrel #rel:B.srel a) (p:B.mpointer a rrel rel) (v:a) 
  : ESPST unit (requires (fun h -> 
                 B.live h p /\ 
                 rel (B.as_seq h p) (Seq.upd (B.as_seq h p) 0 v) /\ 
                 isr_disjoint_from p))
               (ensures (fun h0 _ h1 ->
                 B.live h1 p /\
                 B.as_seq h1 p `Seq.equal` Seq.create 1 v /\
                 B.modifies (B.loc_buffer p) h0 h1)) = 
  ESPSTATE?.reflect (fun _ -> recall isr_map; p *= v)

(**
  * Reading the (erased) contents of the memory for stateful asserts.
  *)
noextract
inline_for_extraction
let get ()
  : ESPST (erased HS.mem) (requires (fun _ -> True))
                          (ensures  (fun h0 x h1 -> h0 == reveal x /\ h1 == h0)) =
  ESPSTATE?.reflect (fun _ -> let h = get () in hide h)

(**
  * Recalling the containment of non-manually managed memory references.
  *)
noextract
inline_for_extraction
let recall (#a:Type) (#rel:FStar.Preorder.preorder a) (r:mreference a rel{not (HS.is_mm r)})
  : ESPST unit (requires (fun m -> is_eternal_region (HS.frameOf r)))
               (ensures  (fun m0 _ m1 -> m0 == m1 /\ m1 `HS.contains` r)) =
  ESPSTATE?.reflect (fun _ -> recall r)

(**
  * Witnessing stable properties of monotonic state.
  *)
noextract
inline_for_extraction
let witness_p (#a:Type0) (#rrel #rel:B.srel a) (b:B.mbuffer a rrel rel) (p:B.spred a)
  : ESPST unit (requires (fun h0 -> p (B.as_seq h0 b) /\ p `B.stable_on` rel))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ b `B.witnessed` p)) =
  ESPSTATE?.reflect (fun _ -> B.witness_p b p)

(**
  * Recalling stable properties of monotonic state.
  *)
noextract
inline_for_extraction
let recall_p (#a:Type0) (#rrel #rel:B.srel a) (b:B.mbuffer a rrel rel) (p:B.spred a)
  : ESPST unit (requires (fun h0 -> (B.recallable b \/ B.live h0 b) /\ b `B.witnessed` p))
               (ensures  (fun h0 _ h1 -> h0 == h1 /\ B.live h0 b /\ p (B.as_seq h0 b))) =
  ESPSTATE?.reflect (fun _ -> B.recall_p b p)
