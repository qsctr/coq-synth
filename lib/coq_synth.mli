val debug : bool ref

val load : logical_dir:string -> physical_dir:string -> module_name:string
  -> Stateid.t

val synthesize : sid:Stateid.t -> hole_type:string -> max_depth:int ->
  params:(string * string) list -> extra_vars:string list
  -> examples:(string list * string) list -> string list