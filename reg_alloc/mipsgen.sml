signature CODEGEN = sig
	structure Frame : FRAME
	val codegen : Frame.frame -> Tree.stm -> Assem.instr list
end

structure mipsGen : CODEGEN = struct
structure Frame : FRAME = MipsFrame
structure T = Tree
structure S = Symbol
structure A = Assem
structure F = Frame

fun codegen(frame) (stm: Tree.stm) : Assem.instr list =
let
val DEBUG_ON = ref 1 (* Toggle debug printing *)

val ilist = ref (nil: A.instr list)

fun emit x = ilist := x :: (!ilist)

fun result(gen) =
  let val t = Temp.newtemp()
  in gen t; t
  end

fun debug_print str =
  if !DEBUG_ON=1 then (print str)
  else ()

fun int (i) =
  if i >= 0 then Int.toString i
  else "-" ^ Int.toString(~i)

fun operToJump oper =
  case oper
    of T.EQ => "beq"
     | T.NE => "bne"
     | T.LT => "blt"
     | T.GT => "bgt"
     | T.LE => "ble"
     | T.GE => "bge"
     | _ => ErrorMsg.impossible("Bad branch operator!")

fun result(gen) =
  let val t = Temp.newtemp()
  in gen t; t
  end

fun munchStm(T.SEQ(a,b)) =
    (munchStm a;
    munchStm b)

  | munchStm(T.JUMP(T.NAME(lab), llst)) =
    (debug_print "->JUMP";
    emit(A.OPER{assem = "j " ^ (Symbol.name lab) ,
                src=[],
                dst=[],
                jump=SOME[Temp.namedlabel(Symbol.name lab)]}))

  (*| munchStm(T.JUMP(e, l)) =
    (debug_print "->JUMP";
    emit(A.OPER{assem = "jr `s0"
                src=[munchExp e],
                dst=[],
                jump=SOME l}))*)

  | munchStm (T.JUMP a) =
    (debug_print "->BADJUMP";
    emit(A.OPER{assem="JUMP : bad munch stm!", src=[], dst=[], jump=NONE}))

  | munchStm(T.LABEL lab) =
    (debug_print "->LABEL";
    emit(A.LABEL{ assem=Symbol.name(lab) ^ ":\n", lab=lab}))

  | munchStm(T.CJUMP(oper, T.CONST i, e1, lab1, lab2)) =
    (debug_print "->CJUMP1";
    emit(A.OPER{assem=((operToJump (oper)) ^ " `s0," ^ int i ^ "," ^
                        Symbol.name(lab1)),
                src=[munchExp e1],
                dst=[],
                jump=SOME([lab1])});
    emit(A.OPER{assem="j "^(Symbol.name lab2), src=[], dst=[], jump=SOME([lab2])}))

  | munchStm(T.CJUMP(oper, e1, T.CONST i, lab1, lab2)) =
    (debug_print "->CJUMP2";
    emit(A.OPER{assem=((operToJump oper) ^ " `s0," ^ int i ^ "," ^
                        Symbol.name(lab1)),
                src=[munchExp e1],
                dst=[],
                jump=SOME([lab1])});

    emit(A.OPER{assem="j "^(Symbol.name lab2), src=[], dst=[], jump=SOME([lab2])}))

  | munchStm(T.CJUMP(oper, e1, e2, lab1, lab2)) =
    (debug_print "->CJUMP3";
    emit(A.OPER{assem=((operToJump oper) ^ " `s0,`s1," ^ Symbol.name(lab1)),
                src=[munchExp e1, munchExp e2],
                dst=[],
                jump=SOME([lab1])});
    emit(A.OPER{assem="j "^(Symbol.name lab2), src=[], dst=[], jump=SOME([lab2])}))



  (* External calls*)
  | munchStm(T.MOVE(T.TEMP t, T.CALL(T.NAME(l),args))) =
    (emit(A.OPER{assem="jal " ^ Symbol.name(l) ,
                src=munchArgs(0,args),
                dst=F.calldefs,
                jump=NONE});
    emit(A.OPER{assem="add `d0,`s0, $zero",
                src=[F.v0], dst=[t], jump=NONE}))

	| munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP FP, T.CONST i)), e2)) =
							    (debug_print ">-MOVE1";
							    emit(A.OPER{assem="sw `s0, " ^ int i ^ "($fp)",
							    src=[munchExp e2],
							    dst=[],
							    jump=NONE}))

	| munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS, e1, T.CONST i)), e2)) =
							    (debug_print ">-MOVE1";
							    emit(A.OPER{assem="sw `s0, " ^ int i ^ "(`s1)",
							    src=[munchExp e2, munchExp e1],
							    dst=[],
							    jump=NONE}))

  | munchStm(T.MOVE(T.MEM(T.BINOP(T.PLUS,T.CONST i, e1)),e2)) =
								    (debug_print "->MOVE2";
								    emit(A.OPER{assem="sw `s0, " ^ (int i) ^"(`s1)",
								                src=[munchExp e2, munchExp e1],
								                dst=[],
								                jump=NONE}))

  | munchStm (T.MOVE (T.MEM (T.BINOP (T.MINUS, e1, T.CONST i)),
					                              e2)) =
										 (debug_print "->MOVE2.5";
					          emit (A.OPER {assem="sw `s0, " ^ (int (~i)) ^ "(`s1)",
					                        dst=[],
					                        src=[munchExp e2, munchExp e1],
					                        jump=NONE}))


  | munchStm(T.MOVE(T.MEM(T.CONST i),e2)) =
    (debug_print "->MOVE3";
    emit(A.OPER{assem="sw `s0, " ^ (int i) ^ "($zero)",
                src=[munchExp e2],
                dst=[],
                jump=NONE}))

  | munchStm(T.MOVE(T.MEM(e1),e2)) =
    (debug_print "->MOVE4";
    emit(A.OPER{assem="sw `s1, 0(`s0)",
                src=[munchExp e2, munchExp e1],
                dst=[],
                jump=NONE}))

  | munchStm(T.MOVE(T.TEMP i, e2)) =
    (debug_print "->MOVE5";
    emit(A.MOVE{assem="move `d0, `s0",
                src=munchExp e2,
                dst=i}))

  | munchStm(T.EXP(T.CALL(T.NAME(lab),args))) =
    (debug_print "->EXPCALL";
    emit(A.OPER{assem="jal " ^ Symbol.name(lab) ,
                src=munchArgs(0,args),
                dst=F.calldefs,
                jump=NONE}))

  | munchStm (T.EXP exp) =
    (debug_print "->STMTOEXP";munchExp exp; ())

  | munchStm (T.MOVE a) =
    (debug_print "->BADMOVE";
    emit(A.MOVE{assem="MOVE : bad munch stm!", src=Temp.newtemp (), dst=Temp.newtemp ()}))

and munchArgs(i,[]) = []
  | munchArgs(i,eh::et) =
    if(i > 0 andalso i < 5) then
      let
        val reg = "$a" ^ int (i-1)
        val r = List.nth(F.argregs,(i-1))
      in
        (emit(A.MOVE{assem="addi " ^ reg ^ ",`s0,0",
        src=munchExp eh, dst=r});
        r::munchArgs(i+1,et))
      end
    else
      munchArgs(i+1,et)

and munchExp(T.MEM(T.BINOP(T.PLUS,e1,T.CONST i))) =
    (debug_print "=>MEM1";
    result(fn r => emit(A.OPER{assem="lw `d0, " ^ int i ^ "(`s0)",
                              src=[munchExp e1],
                              dst=[r],
                              jump=NONE})))

  | munchExp(T.MEM(T.BINOP(T.PLUS,T.CONST i, e1))) =
    (debug_print "=>MEM2";
    result(fn r => emit(A.OPER{assem="lw `d0, " ^ int i ^ "(`s0)",
                              src=[munchExp e1],
                              dst=[r],
                              jump=NONE})))

 | munchExp (T.MEM (T.BINOP (T.MINUS, e1, T.CONST i))) =
 (debug_print "=>MEM2.5";
		result (fn r =>
		emit (A.OPER {assem="lw `d0, " ^ int (~i) ^ "(`s0)",
											       dst=[r],
											       src=[munchExp e1],
											       jump=NONE})))
	| munchExp(T.MEM e) =
		 (debug_print "=>MEM3";
		result(fn r => emit(A.OPER{assem="lw `d0, (`s0)",
													src=[munchExp e],
															dst=[r],
														jump=NONE})))

  | munchExp(T.BINOP(T.PLUS,e1,T.CONST i)) =
    (debug_print "=>PLUS1";
    result(fn r => emit(A.OPER{assem="addi `d0, `s0, " ^ int i ,
                              src=[munchExp e1],
                              dst=[r],
                              jump=NONE})))

  | munchExp(T.BINOP(T.PLUS,T.CONST i,e1)) =
    (debug_print "=>PLUS2";
    result(fn r => emit(A.OPER{assem="addi `d0, `s0, " ^ int i ,
                              src=[munchExp e1],
                              dst=[r],
                              jump=NONE})) )

  | munchExp(T.BINOP(T.PLUS,e1,e2)) =
    (debug_print "=>PLUS3";
    result(fn r => emit(A.OPER{assem="add `d0, `s0, `s1",
                              src=[munchExp e1, munchExp e2],
                              dst=[r],
                              jump=NONE})) )

  | munchExp(T.BINOP(T.MINUS,e1,T.CONST i)) =
    (debug_print "=>MINUS1";
    result(fn r => emit(A.OPER{assem="addi `d0, `s0, " ^ int (~i) ,
                              src=[munchExp e1],
                              dst=[r],
                              jump=NONE})))

  | munchExp (T.BINOP (T.MINUS, T.CONST 0, e)) =
    (debug_print "=>ZMINUS2";
    result(fn r => emit(A.OPER{assem="neg `d0, `s0",
                              dst=[r],
                              src=[munchExp e],
                              jump=NONE})))

  | munchExp(T.BINOP(T.MINUS,T.CONST i,e1)) =
    (debug_print "=>MINUS2";
    result(fn r => emit(A.OPER{assem="addi `d0, `s0, " ^ int i ,
                              src=[munchExp ((T.BINOP(T.MINUS,T.CONST 0,e1)))],
                              dst=[r],
                              jump=NONE})))

  | munchExp(T.BINOP(T.MINUS,e1,e2)) =
    (debug_print "=>MINUS3";
    result(fn r => emit(A.OPER{assem="sub `d0, `s0, `s1",
                              src=[munchExp e1, munchExp e2], dst=[r],
                              jump=NONE})))

  | munchExp(T.BINOP(T.MUL,e1,e2)) =
    (debug_print "=>MUL1";
    result(fn r => (emit(A.OPER{assem="mult `s0, `s1",
                              src=[munchExp e1, munchExp e2],
                              dst=[],
                              jump=NONE});
                    emit(A.OPER{assem="mflo `d0",
                                src=[], dst=[r], jump=NONE}))))

  (*TODO:optimize divide using shift*)
  | munchExp(T.BINOP(T.DIV,e1,e2)) =
    (debug_print "=>DIV1";
    result(fn r => (emit(A.OPER{assem="div `s0, `s1",
                              src=[munchExp e1, munchExp e2],
                              dst=[],
                              jump=NONE});
                    emit(A.OPER{assem="mflo `d0",
                                src=[], dst=[r], jump=NONE}))))


  | munchExp(T.BINOP(T.AND,e1,T.CONST i)) =
    (debug_print "=>AND1";
    result(fn r => emit(A.OPER{assem="andi `d0, `s0, " ^ int i ,
                              src=[munchExp e1],
                              dst=[r],
                              jump=NONE})))

  | munchExp(T.BINOP(T.AND,T.CONST i,e1)) =
    (debug_print "=>AND2";
    result(fn r => emit(A.OPER{assem="andi `d0, `s0, " ^ int i ,
                              src=[munchExp e1],
                              dst=[r],
                              jump=NONE})))

  | munchExp(T.BINOP(T.AND,e1,e2)) =
    (debug_print "=>AND3";
    result(fn r => emit(A.OPER{assem="and `d0, `s0, `s1",
                              src=[munchExp e1, munchExp e2],
                              dst=[r],
                              jump=NONE})))

  | munchExp(T.BINOP(T.OR,e1,T.CONST i)) =
    (debug_print "=>OR1";
    result(fn r => emit(A.OPER{assem="ori `d0, `s0, " ^ int i ,
                              src=[munchExp e1],
                              dst=[r],
                              jump=NONE})))

  | munchExp(T.BINOP(T.OR,T.CONST i,e1)) =
    (debug_print "=>OR2";
    result(fn r => emit(A.OPER{assem="ori `d0, `s0, " ^ int i ,
                              src=[munchExp e1],
                              dst=[r],
                              jump=NONE})))

  | munchExp(T.BINOP(T.OR,e1,e2)) =
    (debug_print "=>OR3";
    result(fn r => emit(A.OPER{assem="or `d0, `s0, `s1",
                              src=[munchExp e1, munchExp e2],
                              dst=[r],
                              jump=NONE})))

  | munchExp(T.NAME n) =
    (debug_print "=>NAME";
    result(fn r => emit(A.OPER{assem="la `d0" ^ (S.name n) ,
                              src=[],
                              dst=[r],
                              jump=NONE})))

  | munchExp(T.TEMP t) =
    (debug_print "=>TEMP";
    t)

  | munchExp (T.CONST n) =
    result(fn r => emit(A.OPER{assem="li `d0, " ^ (int n) ,
                              dst=[r],
                              src=[],
                              jump=NONE}))

  | munchExp(T.CALL(exp,args)) =
    let
      val _ = debug_print "=>CALL"
      val saves = map (fn _ => Temp.newtemp ()) F.callersaves
      val numArgTemps = length F.argregs
      val registerArgs =
        if length args > numArgTemps then
          List.take (args, numArgTemps)
        else args

      val srcs = ListPair.map (fn (_, argReg) => argReg) (registerArgs, F.argregs)

      val registerArgTemps = map (fn _ => Temp.newtemp ()) registerArgs

      val stackArgs =
        if length args > numArgTemps then
          List.drop (args, numArgTemps)
        else []

      fun updateSp i = munchStm (T.MOVE (T.TEMP Frame.SP,T.BINOP
              (T.MINUS, T.TEMP F.SP,T.CONST (Frame.wordSize * i))))

      val numStackArgs = length stackArgs

      fun pushStackArg (exp, i) =
        (munchStm (T.MOVE (T.MEM (T.BINOP (T.PLUS, T.TEMP F.SP, T.CONST (i * Frame.wordSize))), exp));
        i+1)

    in
      ListPair.app (fn (tmp, exp) =>
      munchStm (T.MOVE (T.TEMP tmp,
      exp)))
      (registerArgTemps, registerArgs);

      updateSp numStackArgs;

      foldl pushStackArg 1 stackArgs;

      ListPair.map (fn (argReg, argTmp) =>
      munchStm (T.MOVE (T.TEMP argReg,
      T.TEMP argTmp)))
      (F.argregs, registerArgTemps);
      emit (callInstr (exp, srcs));
      updateSp (~numStackArgs);

      F.v0
    end
  | munchExp(_) = result(fn _ => emit(A.OPER{assem="bad munch exp!", src=[], dst=[], jump=NONE}))

  and callInstr (T.NAME label, srcs) =
    A.OPER {assem="jal " ^ S.name label ,
    dst=[F.v0] @ F.callersaves @ F.argregs,
    src=srcs @ [F.SP],
    jump=NONE}
  | callInstr (exp, srcs) =
    A.OPER {assem="jalr `s0 ",
    dst=[F.v0] @ F.callersaves @ F.argregs,
    src=[munchExp exp, F.SP] @ srcs,
    jump=NONE}
in
  munchStm stm;
  rev(!ilist)
end

end
