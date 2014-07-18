signature TREE =
sig
  type label = Temp.label
  type size

  datatype stm = SEQ of stm * stm
               | LABEL of label
               | JUMP of exp * label list
               | CJUMP of relop * exp * exp * label * label
               | MOVE of exp * exp
               | EXP of exp

       and exp = BINOP of binop * exp * exp
               | MEM of exp
               | TEMP of Temp.temp
               | ESEQ of stm * exp
               | NAME of label
               | CONST of int
               | CALL of exp * exp list

        and binop = PLUS | MINUS | MUL | DIV
                   | AND | OR | LSHIFT | RSHIFT | ARSHIFT | XOR

        and relop = EQ | NE | LT | GT | LE | GE
                 | ULT | ULE | UGT | UGE

			(*  val notRel : relop -> relop
			    val commute: relop -> relop *)
  val stm_to_str : stm -> string
  val exp_to_str : exp -> string
  val binop_to_str : binop -> string
  val relop_to_str : relop -> string
  
  val notRel : relop -> relop

end

structure Tree : TREE =
struct
  type label=Temp.label
  type size = int

  datatype stm = SEQ of stm * stm
               | LABEL of label
               | JUMP of exp * label list
               | CJUMP of relop * exp * exp * label * label
               | MOVE of exp * exp
               | EXP of exp

      and exp = BINOP of binop * exp * exp
               | MEM of exp
               | TEMP of Temp.temp
               | ESEQ of stm * exp
               | NAME of label
               | CONST of int
               | CALL of exp * exp list

      and binop = PLUS | MINUS | MUL | DIV
                | AND | OR | LSHIFT | RSHIFT | ARSHIFT | XOR

      and relop = EQ | NE | LT | GT | LE | GE
	        | ULT | ULE | UGT | UGE

  fun stm_to_str(SEQ(stm1, stm2)) =
        "SEQ("^stm_to_str(stm1)^", "^stm_to_str(stm2)^")"
    | stm_to_str(LABEL(lab)) =
        "LABEL("^(Symbol.name lab)^")"
    | stm_to_str(JUMP(exp, lab1::l)) =
        "JUMP("^exp_to_str(exp)^", ["^
          (foldl (fn (lab,ans)=>ans^", "^(Symbol.name lab)) (Symbol.name lab1) l) ^ "])"
    | stm_to_str(JUMP(exp, [])) =
        "JUMP("^exp_to_str(exp)^", [])"
    | stm_to_str(CJUMP(relop, exp1, exp2, t, f)) =
        "CJUMP(" ^ relop_to_str(relop) ^ ", " ^ exp_to_str(exp1) ^ ", " ^
        exp_to_str(exp2) ^ ", " ^ (Symbol.name t) ^ ", " ^ (Symbol.name f) ^ ")"
    | stm_to_str(MOVE(exp1, exp2)) =
        "MOVE("^exp_to_str(exp1)^", "^exp_to_str(exp2)^")"
    | stm_to_str(EXP(exp)) =
        "EXP("^exp_to_str(exp)^")"

  and exp_to_str(BINOP(binop, exp1, exp2)) =
        "BINOP("^binop_to_str(binop)^", "^exp_to_str(exp1)^", "^exp_to_str(exp2)^")"
    | exp_to_str(MEM(exp)) =
        "MEM("^exp_to_str(exp)^")"
    | exp_to_str(TEMP(temp)) =
        "TEMP("^(Temp.makestring temp)^")"
    | exp_to_str(ESEQ(stm, exp)) =
        "ESEQ("^stm_to_str(stm)^", "^exp_to_str(exp)^")"
    | exp_to_str(NAME(lab)) =
        "NAME("^(Symbol.name lab)^")"
    | exp_to_str(CONST(i)) =
        "CONST("^(Int.toString i)^")"
    | exp_to_str(CALL(exp1, e0::l)) =
        "CALL("^exp_to_str(exp1)^", [" ^
          (foldl (fn (e,ans)=>ans^", "^exp_to_str(e)) (exp_to_str e0) l) ^ "])"
    | exp_to_str(CALL(exp1, [])) =
        "CALL("^exp_to_str(exp1)^", [])"


  and binop_to_str(PLUS) = "PLUS"
    | binop_to_str(MINUS) = "MINUS"
    | binop_to_str(MUL) = "MUL"
    | binop_to_str(DIV) = "DIV"
    | binop_to_str(AND) = "AND"
    | binop_to_str(OR) = "OR"
    | binop_to_str(LSHIFT) = "LSHIFT"
    | binop_to_str(RSHIFT) = "RSHIFT"
    | binop_to_str(ARSHIFT) = "ARSHIFT"
    | binop_to_str(XOR) = "XOR"

  and relop_to_str(EQ) = "EQ"
    | relop_to_str(NE) = "NE"
    | relop_to_str(LT) = "LT"
    | relop_to_str(GT) = "GT"
    | relop_to_str(LE) = "LE"
    | relop_to_str(GE) = "GE"
    | relop_to_str(ULT) = "ULT"
    | relop_to_str(ULE) = "ULE"
    | relop_to_str(UGT) = "UGT"
    | relop_to_str(UGE) = "UGE"


  fun notRel EQ = NE 
    | notRel NE = EQ
    | notRel LT = GE
    | notRel GT = LE 
    | notRel LE = GT
    | notRel GE = LT
    | notRel ULT = UGE
    | notRel ULE = UGT 
    | notRel UGT = ULE
    | notRel UGE = ULT

end

