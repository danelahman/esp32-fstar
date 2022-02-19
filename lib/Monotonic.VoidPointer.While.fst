module Monotonic.VoidPointer.While

let rec while_true #pre #post body args =
  ESPST.unextract_st (fun _ -> body args);
  while_true #pre #post body args

let rec while_true2 #pre #post body args1 args2 =
  ESPST.unextract_st (fun _ -> body args1 args2);
  while_true2 #pre #post body args1 args2
