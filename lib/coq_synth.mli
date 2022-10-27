open Base

val debug : bool ref

val load : logical_dir:string -> physical_dir:string -> module_name:string
  -> Stateid.t

val synthesize : sid:Stateid.t -> hole_type:string
  -> params:(string * string) list -> extra_exprs:string list
  -> examples:(string list * string) list -> k:int option -> levels:int option
  -> string Sequence.t
