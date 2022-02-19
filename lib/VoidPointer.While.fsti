(**
  * This module presents an abstraction upon
  * while loops to be used in the main function
  * in Main.fst.
  *)

module VoidPointer.While

module HS = FStar.HyperStack
module VP = VoidPointer

module VPW = Monotonic.VoidPointer.While

open ESPST

open FStar.Ghost

(**
  * A function that gets extracted to an while loop in C that
  * calls its `body` on the given arguments `args` infinite
  * amount of times, thus also the postcondition `False`.
  *
  * The C implementation looks simply as follows:
  *
  *  while (1) {
  *    body args;
  *  }
  *)
val while_true
      (#pre: erased (VP.t -> HS.mem -> Type0))
      (#post: erased (VP.t -> HS.mem -> unit -> HS.mem -> Type0))
      (body: (p: VP.t -> ESPST unit (requires (reveal pre p)) (ensures (reveal post p))))
      (args: VP.t)
    : ESPST unit
      (requires
        (fun h0 ->
            reveal pre args h0 /\
            (forall h1 h2. reveal pre args h1 /\ reveal post args h1 () h2 ==> reveal pre args h2) /\
            (forall h0 h1 h2.
                reveal post args h0 () h1 /\ reveal post args h1 () h2 ==> reveal post args h0 () h2
            )))
      (ensures (fun h0 x h1 -> False))

