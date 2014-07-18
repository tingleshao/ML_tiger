structure Types =
struct

  type unique = unit ref

  datatype ty = RECORD of (Symbol.symbol * ty) list * unique
              | NIL
              | INT
              | STRING
              | ARRAY of ty * unique
              | NAME of Symbol.symbol * ty option ref
              | UNIT

  fun typ_to_str(RECORD(fields, uniq)) = "RECORD"
    | typ_to_str(ARRAY(typ, uniq)) = "ARRAY: " ^ (typ_to_str typ)
    | typ_to_str(NAME(sym, typ)) = "NAME: " ^ Symbol.name sym
    | typ_to_str(NIL) = "NIL"
    | typ_to_str(INT) = "INT"
    | typ_to_str(STRING) = "STRING"
    | typ_to_str(UNIT) = "UNIT"
end

