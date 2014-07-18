signature ENV =
sig
	type access
	type ty
	datatype enventry = VarEntry of {access: Translate.access, ty: Types.ty}
                    | FunEntry of {level: Translate.level, label: Temp.label,
                                   formals: Types.ty list, result: Types.ty}
	val base_tenv : Types.ty Symbol.table (* predefined types *)
	val base_venv : enventry Symbol.table (* predefined functions *)
end

structure Env: ENV = struct
    type access = unit ref
    type ty = Types.ty
    datatype enventry = VarEntry of {access: Translate.access, ty: Types.ty}
                      | FunEntry of {level: Translate.level, label: Temp.label,
                                     formals: ty list, result: ty}

    fun enterentry ((symbol,entry),env) = Symbol.enter(env, symbol, entry)

    val base_tenv = foldr enterentry
        Symbol.empty [(Symbol.symbol("int"),Types.INT),
        (Symbol.symbol("string"),Types.STRING)]

    val base_venv = foldr enterentry Symbol.empty [
      (Symbol.symbol("print"),
          FunEntry {level=Translate.outermost, label=Temp.newlabel(), formals=[Types.STRING], result=Types.UNIT}),
      (Symbol.symbol("flush"),
          FunEntry {level=Translate.outermost, label=Temp.newlabel(), formals=[], result=Types.UNIT}),
      (Symbol.symbol("getchar"),
          FunEntry {level=Translate.outermost, label=Temp.newlabel(), formals=[], result=Types.STRING}),
      (Symbol.symbol("ord"),
          FunEntry {level=Translate.outermost, label=Temp.newlabel(), formals=[Types.STRING], result=Types.INT}),
      (Symbol.symbol("chr"),
          FunEntry {level=Translate.outermost, label=Temp.newlabel(), formals=[Types.INT], result=Types.STRING}),
      (Symbol.symbol("size"),
          FunEntry {level=Translate.outermost, label=Temp.newlabel(), formals=[Types.STRING], result=Types.INT}),
      (Symbol.symbol("substring"),
          FunEntry {level=Translate.outermost, label=Temp.newlabel(), formals=[Types.STRING,Types.INT,Types.INT], result=Types.STRING}),
      (Symbol.symbol("concat"),
          FunEntry {level=Translate.outermost, label=Temp.newlabel(), formals=[Types.STRING,Types.STRING], result=Types.STRING}),
      (Symbol.symbol("not"),
          FunEntry {level=Translate.outermost, label=Temp.newlabel(), formals=[Types.INT], result=Types.INT}),
      (Symbol.symbol("exit"),
          FunEntry {level=Translate.outermost, label=Temp.newlabel(), formals=[Types.INT], result=Types.UNIT})
    ]
end



