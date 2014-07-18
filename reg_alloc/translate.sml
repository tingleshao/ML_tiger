signature TRANSLATE =
sig
  datatype exp = Ex of Tree.exp
               | Nx of Tree.stm
               | Cx of Temp.label * Temp.label -> Tree.stm

  val exp_to_str : exp -> string

  type frag;
  type unique
  type level
  val newLevel : {parent: level, name: Temp.label,
                  formals: bool list} -> level
  val outermost : level

  type access

  val formals : level -> access list
  val allocLocal : level -> bool -> access

  val procEntryExit : {level: level, body: exp} -> unit
  val getResult : unit -> Frame.frag list

  val SimpleVar : access * level -> exp
  val SubscriptVar : exp * exp -> exp
  val FieldVar : exp * int -> exp
  val IntExp : int -> exp
  val OpExp: Absyn.oper * exp * exp -> exp
  val StringExp: string -> exp
  val ArrayExp: exp * exp -> exp
  val AssignExp: exp * exp -> exp
  val RecordExp: exp list -> exp
  val ForExp: Temp.label * Temp.label * exp * exp * exp -> exp
  val WhileExp: Temp.label * Temp.label * exp * exp -> exp
  val SeqExp: exp list -> exp
  val LetExp: exp list * exp -> exp
  val CallExp: Symbol.symbol * Temp.label * level * level * exp list -> exp
  val IfExp: exp * exp * exp option -> exp
  val BreakExp: Temp.label -> exp
  val InitVarExp: access * exp -> exp

  val unEx : exp -> Tree.exp
  val unNx : exp -> Tree.stm
  val unCx : exp -> (Temp.label * Temp.label -> Tree.stm)

  val NilExp : unit -> exp
end

structure Translate : TRANSLATE =
struct
  structure Frame : FRAME = MipsFrame
  structure A = Absyn
  structure T = Tree

  datatype exp = Ex of T.exp
               | Nx of T.stm
               | Cx of Temp.label * Temp.label -> T.stm

  val impossible = ErrorMsg.impossible

  type unique = unit ref

  datatype level = ROOT
                 | CHILD of {frame: Frame.frame, parent: level} * unique

  fun newLevel({parent=level, name=f, formals=l}) =
        (CHILD ({frame=Frame.newFrame {name=f, formals=true::l},
                parent=level}, ref()))

  val outermost = newLevel({parent=ROOT, name=Temp.newlabel(), formals=[]})

  type access = level * Frame.access

  fun formals(ROOT) = []
    | formals(lev as CHILD({frame, parent}, uniq)) =
        let val formals = (Frame.formals(frame))
            val _::formals' = formals
        in map (fn (h) => (lev, h)) formals'
        end

  fun allocLocal (ROOT) =
        ((print "allocate local variable at top scope");
        impossible("cannot allocate a local variable at the top scope"))
    | allocLocal (lev as CHILD({frame, parent}, uniq)) =
        (fn(esc) => (lev, Frame.allocLocal(frame)(esc)))

  fun seq([]) = T.EXP(T.CONST 0)
    | seq([s]) = s
    | seq(h::t) = T.SEQ(h, seq(t))

  fun unEx (Ex e) = e
    | unEx (Nx s) = T.ESEQ(s, T.CONST 0)
    | unEx (Cx genstm) =
        let
          val r = Temp.newtemp()
          val t = Temp.newlabel() and f = Temp.newlabel()
          val s = seq[T.MOVE(T.TEMP r, T.CONST 1),
                      genstm(t, f), T.LABEL f,
                      T.MOVE(T.TEMP r, T.CONST 0),
                      T.LABEL t]
        in
          T.ESEQ(s, T.TEMP r)
        end

  fun unCx (Ex(T.CONST 0)) = (fn (t, f) => T.JUMP(T.NAME f, [f]))
    | unCx (Ex(T.CONST _)) = (fn (t, f) => T.JUMP(T.NAME t, [t]))
    | unCx (Ex e) = (fn (t, f) => T.CJUMP(T.EQ, e, T.CONST 1, t, f))
    | unCx (Cx genstm) = genstm
    | unCx (Nx stm) = ((print ("unCx an Nx " ^ (T.stm_to_str stm)));
                      (impossible("No Result exp cannot be " ^
                                 "converted to a conditional.")))

  fun unNx (Ex e) = T.EXP e
    | unNx (Cx genstm) =
        let val t = Temp.newlabel() and f = Temp.newlabel()
        in T.SEQ(genstm(t, f), T.LABEL t)
        end
    | unNx (Nx s) = s

  fun exp_to_str(exp) = T.exp_to_str((unEx exp))

  fun SimpleVar(access, curr_lev)=
    let
      val (def_lev, frame_access) = access

      fun get_def_fp(curr_lev, def_lev) =
        let
          val CHILD ({frame=curr_frame, parent=curr_parent}, curr_uniq) = curr_lev
          val CHILD ({frame=def_frame, parent=def_parent}, def_uniq) = def_lev
        in
          if (curr_uniq = def_uniq) then
            T.TEMP(Frame.FP)
          else
            T.MEM(T.BINOP(T.PLUS,
                          T.CONST(Frame.staticlink(curr_frame)),
                          get_def_fp(curr_parent, def_lev)))
        end
    in
      Ex(Frame.exp (frame_access) (get_def_fp(curr_lev, def_lev)))
    end

      (* TODO: Check for out of bounds and nil pointers *)
      (* exp(lvalue) * exp(index) -> exp *)
  fun SubscriptVar(record, index) = Ex(T.MEM(T.BINOP(
        T.PLUS,
        unEx record,
        T.BINOP(T.MUL, unEx index, T.CONST(Frame.wordSize)))))

      (* exp(record) * int(index) -> exp  *)
  fun FieldVar(var, index) = Ex(T.MEM(T.BINOP(
        T.PLUS,
        unEx var,
        T.CONST(index * Frame.wordSize))))

  fun IntExp(x) = Ex(T.CONST(x))

  fun NilExp() = IntExp(0)

  fun binopExp (oper, left, right) = Ex(T.BINOP(oper, unEx left, unEx right))

  fun relopExp (oper, left, right) =
        Cx (fn (t, f) => T.CJUMP(oper, unEx left, unEx right, t, f))

  fun OpExp (A.PlusOp, left, right) = binopExp (T.PLUS, left, right)
    | OpExp (A.MinusOp, left, right) = binopExp (T.MINUS, left, right)
    | OpExp (A.TimesOp, left, right) = binopExp (T.MUL, left, right)
    | OpExp (A.DivideOp, left, right) = binopExp (T.DIV, left, right)
    | OpExp (A.EqOp, left, right) = relopExp (T.EQ, left, right)
    | OpExp (A.NeqOp, left, right) = relopExp (T.NE, left, right)
    | OpExp (A.LtOp, left, right) = relopExp (T.LT, left, right)
    | OpExp (A.LeOp, left, right) = relopExp (T.LE, left, right)
    | OpExp (A.GtOp, left, right) = relopExp (T.GT, left, right)
    | OpExp (A.GeOp, left, right) = relopExp (T.GE, left, right)

      (* If Then Else Exp with zero expressions *)
  fun IfExp(test, Nx then_stm, SOME(Nx else_stm)) =
        let
          val t = Temp.newlabel() and f = Temp.newlabel() and j = Temp.newlabel()
        in
          Nx(seq[T.CJUMP(T.EQ, T.CONST(1), unEx test, t, f),
                 T.LABEL t,
                 then_stm,
                 T.JUMP(T.NAME j, [j]),
                 T.LABEL f,
                 else_stm,
                 T.LABEL j])
        end

      (* If Then Else Exp with nonzero expressions *)
    | IfExp(test, then_exp, SOME(else_exp)) =
        let
          val r = Temp.newtemp()

          val t = Temp.newlabel()
          and f = Temp.newlabel()
          and j = Temp.newlabel()
        in
          Ex(T.ESEQ(seq[T.CJUMP(T.EQ, T.CONST(1), unEx test, t, f),
                        T.LABEL t,
                        T.MOVE(T.TEMP r, unEx then_exp),
                        T.JUMP(T.NAME j, [j]),
                        T.LABEL t,
                        T.MOVE(T.TEMP r, unEx else_exp),
                        T.LABEL j],
              T.TEMP r))
        end

      (* If Then Exp *)
    | IfExp(test, then_exp, NONE) =
        let
          val t = Temp.newlabel() and f = Temp.newlabel()
        in
          Nx(seq[T.CJUMP(T.EQ, T.CONST(1), unEx test, t, f),
                 T.LABEL t,
                 unNx then_exp,
                 T.LABEL f])
        end

  type frag = Frame.frag
  val result = ref([]: frag list)

  fun getResult() = !result

  fun StringExp (str) =
    let val lab = Temp.newlabel()
    in
       ((result := Frame.STRING (lab, str) :: !result);
       Ex (T.NAME lab))
    end

  (* Moves exp into var *)
  fun AssignExp (var, exp) =
    let
      val var = unEx var
      val exp = unEx exp
    in
      Nx (T.MOVE (var, exp))
    end

  fun InitVarExp ((_,frameAccess),init) =
  	let
      fun helper(t as T.CONST(_)) =
            (T.MOVE(T.MEM(T.BINOP(T.PLUS,T.TEMP(Frame.FP),t)),unEx(init)))
  		  | helper(t as T.TEMP(_)) = (T.MOVE(t,unEx(init)))
  	in
  		Nx(helper(Frame.offsetOf(frameAccess)))
  	end

  fun LetExp ([], body) = (body)
    | LetExp (decs, body) = (Ex(T.ESEQ (seq (map unNx decs), unEx body)))

  fun procEntryExit {level = CHILD ({frame, parent}, uref), body} =
        let
          val body_stm = Frame.procEntryExit1(frame,
                            T.MOVE ((T.TEMP Frame.v0), (unEx body)))
          val fragment = Frame.PROC {body=body_stm, frame=frame}
        in
          result := fragment::(!result)
        end
    | procEntryExit ({level=ROOT, body=_}) =
        impossible ("Cannot call procEntryExit at ROOT level")

  fun RecordExp(fields) =
    let
      val r = Temp.newtemp()
      fun helper([], i) = T.EXP(T.CONST(0))
        | helper(field::[], i) = T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP(r),
              T.CONST(i*Frame.wordSize))), unEx field)
        | helper(field::l, i) = T.SEQ(T.MOVE(
            T.MEM(T.BINOP(T.PLUS, T.TEMP(r), T.CONST(i*Frame.wordSize))),
            unEx field), helper(l, i+1))
    in
      Ex(T.ESEQ(T.SEQ(T.MOVE(T.TEMP(r),
              Frame.externalCall("malloc",
                  [T.CONST(List.length(fields)*Frame.wordSize)])),
            helper(fields, 0)),
           T.TEMP(r)))
    end

  (*fun ArrayExp(size, init) =
    let
      val r = Temp.newtemp()
      val n = Temp.newtemp()
      val size' = T.BINOP(T.MINUS, unEx(size), T.CONST(1))
      val lab1 = Temp.newlabel()
      and lab2 = Temp.newlabel()
    in
      Ex(T.ESEQ(T.SEQ(T.MOVE(T.TEMP(r), Frame.externalCall("malloc",
                [T.BINOP(T.MUL, T.CONST(Frame.wordSize), unEx(size))])),
              seq[T.MOVE(T.TEMP(n), T.CONST(~1)),
                  T.CJUMP(T.EQ, size', T.TEMP(n), lab2, lab1),
                  T.LABEL(lab1),
                  T.MOVE(T.TEMP(n), T.BINOP(T.PLUS, T.TEMP(n), T.CONST(1))),
                  T.MOVE(T.MEM(T.BINOP(T.PLUS, T.TEMP(r), T.BINOP(T.MUL, T.TEMP(n),
                      T.CONST(Frame.wordSize)))), unEx init),
                  T.CJUMP(T.EQ, size', T.TEMP(n), lab2, lab1),
                  T.LABEL(lab2)]),
            T.TEMP(r)))
    end*)
  fun ArrayExp(size, init) =
    let
      val lab = Temp.newtemp()
      val args = [unEx size, unEx init]
      val arr = T.MOVE(T.TEMP lab, Frame.externalCall("tig_initArray", args))
    in
      Ex(T.ESEQ(arr, T.TEMP lab))
    end

  fun WhileExp(test_label, done_label, test, body) =
    let
      val body_label = Temp.newlabel()
    in
      Nx(seq[T.LABEL test_label,
             T.CJUMP(T.EQ, T.CONST(1), unEx test, body_label, done_label),
             T.LABEL body_label,
             unNx body,
             T.JUMP(T.NAME test_label, [test_label]),
             T.LABEL done_label])
    end

  fun ForExp(test_label, done_label, lo, hi, body) =
    let
      val i = Temp.newtemp()
      val limit = Temp.newtemp()
      val t = Temp.newlabel()
    in
      Nx(seq[T.MOVE(T.TEMP i, unEx lo),
             T.MOVE(T.TEMP limit, unEx hi),
             T.LABEL test_label,
             T.CJUMP(T.LE, T.TEMP i, T.TEMP limit, t, done_label),
             T.LABEL t,
             unNx body,
             T.MOVE(T.TEMP i, T.BINOP(T.PLUS, T.TEMP i, T.CONST 1)),
             T.JUMP(T.NAME test_label, [test_label]),
             T.LABEL done_label])
    end

      (* Jump to the done_label of a while/for exp *)
  fun BreakExp(done_label) = Nx(T.JUMP(T.NAME done_label, [done_label]))

  fun relopStrExp (oper, left, right, str) =
        Ex (Frame.externalCall (str, [unEx left, unEx right]))

  fun stringOpExp(A.EqOp, left, right) = relopStrExp(T.EQ, left, right, "stringEqual")
    | stringOpExp(A.NeqOp, left, right) = relopStrExp(T.EQ, left, right, "stringNotEqual")
    | stringOpExp(A.LtOp, left, right) = relopStrExp(T.EQ, left, right, "stringLessThan")
    | stringOpExp(A.LeOp, left, right) = relopStrExp(T.EQ, left, right, "stringLessThanOrEqual")
    | stringOpExp(A.GtOp, left, right) = relopStrExp(T.EQ, left, right, "stringGreaterThan")
    | stringOpExp(A.GeOp, left, right) = relopStrExp(T.EQ, left, right, "stringGreaterThanOrEqual")
    | stringOpExp(_, _, _) = ((print " illegal operation on string "); impossible("illegal operation on strings"))

  fun SeqExp (exps) = Nx(seq(map unNx exps))

  fun CallExp(funSymbol, funlabel, funlev, lev, []) = NilExp()
    | CallExp(funSymbol, funlabel, funlev, lev, eList) =
        let
          fun staticLink(CHILD({frame, parent}, uref1), lf as CHILD(_, uref2), stackFrame) =
            let
              val formals = Frame.formals(frame)
              val formal1::_ = formals
            in
              if uref1 = uref2 then
                stackFrame
              else
                staticLink(parent, lf, T.MEM(T.BINOP( T.PLUS,
                    Frame.offsetOf(formal1), stackFrame)))
            end
            | staticLink(_,ROOT,_) =
                (print("problem in static links for CallExp("^
                (Symbol.name funSymbol)^") ROOT");
                impossible("reached Root level"))
            | staticLink(_, _, _) =
                (print("problem in static links for CallExp");
                impossible("Something went wrong!"))


          val CHILD({frame,parent=funparent},_) = funlev
          val stLnk = (case funparent
                         of ROOT => staticLink(lev, funlev, T.TEMP(Frame.FP))
                         (*to remove work around replace funlev with funparent*)
                          | CHILD({frame=frame',parent=parent'},_) => staticLink(lev, funparent, T.TEMP(Frame.FP)))
        in
          Ex(T.CALL(T.NAME(funlabel), stLnk::(map unEx eList)))
        end
end
