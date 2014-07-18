structure FindEscape : sig val findEscape: Absyn.exp -> unit
                       end =
struct
  type depth = int
  type escEnv = (depth * bool ref) Symbol.table
  fun traverseVar(env:escEnv, d:depth, s:Absyn.var): unit = ()
  fun traverseExp(env:escEnv, d:depth, s:Absyn.var): unit = ()
  fun traverseDecs(env:escEnv, d:depth, s:Absyn.var): unit = ()

  fun findEscape(prog: Absyn.exp): unit = ()
end
