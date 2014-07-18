structure MipsFrame : FRAME =
struct
  structure A = Assem
  structure T = Temp
  structure Tr = Tree

  datatype access = InFrame of int
                  | InReg of T.temp

  type frame = {name : T.label, formals: access list, offset: int ref}

  datatype frag = PROC of {body: Tr.stm, frame: frame}
                | STRING of T.label * string

  val wordSize = 4

  type register = string

      (* Converts bool list to access list *)
  fun bools_to_acclist(formals : bool list) =
    let
      val sp = ref 0
      fun bool_to_acc(true) =
            let
              val my_sp = !sp
              val _ = (sp:= !sp - wordSize)
            in
              InFrame(my_sp)
            end
        | bool_to_acc(false) = InReg(T.newtemp())
    in
      (map bool_to_acc formals)
    end

    (* Generate a new frame *)
  fun newFrame ({name : T.label, formals : bool list}) =
    {name=name,
    formals= (bools_to_acclist formals),
    offset = ref (0-wordSize*length(formals))}

      (* Get name of a frame *)
  fun name (f : frame) = #name f

      (* Get formals of a frame in the form of an access list*)
  fun formals (f : frame) = #formals f

      (* returns the right access based on whether the formal escapes *)
  fun allocLocal (f : frame) true =
      let val fp = #offset f
      in
        fp := !fp - wordSize;
        InFrame(!fp)
      end
    | allocLocal (f : frame) false = InReg(T.newtemp())

      (* Returns statick link (temp/int) of a frame *)
  fun staticlink (f) =
    let
      val formals' = formals(f)
      fun check([]) = ErrorMsg.impossible("frame has empty formals list, no static link")
        | check(_) = ()
      val _ = check(formals')
    in
      case hd(formals')
        of InFrame(pc) => pc
         | InReg(_) => ErrorMsg.impossible "Static link in a register"
    end

      (* Converts a tiger string fragment to its version in MIPS *)
  fun string (label, str) = (Symbol.name label ^ ": .asciiz \"" ^ str ^ "\"\n")

      (* List of all registers on the machine. *)
  val registers = ["zero", "v0", "gp", "sp", "fp", "ra",
                  "a0", "a1", "a2","a3",
                  "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7", "t8", "t9",
                  "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7",
                   "v1"]

	val availableregisters =  [

                  "t0", "t1", "t2", "t3", "t4", "t5", "t6", "t7", "t8", "t9",
                  "s0", "s1", "s2", "s3", "s4", "s5", "s6", "s7"]

  val ZERO = T.newtemp()
  val FP = T.newtemp()
  val RA = T.newtemp()
  val GP = T.newtemp()
  val SP = T.newtemp()
  val v0 = T.newtemp()
  val specialregs = [ZERO, v0, GP, SP, FP, RA]

  val a0 = T.newtemp()
  val a1 = T.newtemp()
  val a2 = T.newtemp()
  val a3 = T.newtemp()
  val argregs = [a0, a1, a2, a3]

  val t0 = T.newtemp()
  val t1 = T.newtemp()
  val t2 = T.newtemp()
  val t3 = T.newtemp()
  val t4 = T.newtemp()
  val t5 = T.newtemp()
  val t6 = T.newtemp()
  val t7 = T.newtemp()
  val t8 = T.newtemp()
  val t9 = T.newtemp()
  val callersaves = [t0, t1, t2, t3, t4, t5, t6, t7, t8, t9]

  val s0 = T.newtemp()
  val s1 = T.newtemp()
  val s2 = T.newtemp()
  val s3 = T.newtemp()
  val s4 = T.newtemp()
  val s5 = T.newtemp()
  val s6 = T.newtemp()
  val s7 = T.newtemp()
  val calleesaves = [s0, s1, s2, s3, s4, s5, s6, s7]

 (* val AT = T.newtemp() *)
  val v1 = T.newtemp()
 (* val reg_temps = specialregs @ argregs @ callersaves @ calleesaves @ [AT,v1] *)

  val calldefs = [v0,RA] @ callersaves
  val reg_temps = specialregs @ argregs @ callersaves @ calleesaves @ [v1]

  val colorable = calleesaves @ callersaves


  fun nameRegs label regs =
      let
        val (labels, _) =
            foldl (fn (r, (rs, n)) =>
                      ((r, label ^ Int.toString n) :: rs, n+1))
                  ([], 0)
                  regs
      in
        labels
      end

(*  val tempMap = foldr Temp.Table.enter' Temp.Table.empty
                      ([(FP, "fp"),
                      (GP, "gp"),
                      (RA, "ra"),
                      (v0,"v0"),
                        (SP, "sp"),
                        (ZERO, "zero")] @
                       nameRegs "a" argregs @
                       nameRegs "s" calleesaves @
                       nameRegs "t" callersaves) *)


  val tempMap = ListPair.foldl (fn (temp, reg, table) =>
                                    T.Table.enter(table, temp, reg))
                  T.Table.empty (reg_temps, registers)

  fun get_reg (temp : T.temp) =
    case T.Table.look (tempMap, temp)
      of SOME register => register
       | NONE => T.makestring temp

  fun move (dst, src) = Tr.MOVE (Tr.TEMP dst, Tr.TEMP src)

  fun seq [] = Tr.EXP (Tr.CONST 0)
    | seq [exp] = exp
    | seq (h::l) = Tr.SEQ (h, seq l)

      (* Call an external function (included in stdlib)*)
  fun externalCall(name, args) = Tr.CALL(Tr.NAME(T.namedlabel(name)), args)

  fun offsetOf(InFrame(k)) = Tr.CONST(k)
    | offsetOf(InReg(t)) = Tr.TEMP(t)

  fun exp (InFrame k) fp = Tr.MEM(Tr.BINOP(Tr.PLUS, fp, (Tr.CONST k)))
    | exp (InReg t) fp = Tr.TEMP t

      (* ViewShift
      * Saving/restoring callee-save registers (and RA) *)
  fun procEntryExit1 (frame, stm) =
    let
      val viewShift = seq (
          ListPair.map (fn(arg, access) =>
              Tr.MOVE ((exp access (Tr.TEMP FP)), Tr.TEMP arg))
              (argregs, formals frame))

      val to_save = RA :: calleesaves

      fun save_reg(src, (acc_list, save_stm)) =
        let
          val acc = allocLocal frame true
          val dst = exp (acc) (Tr.TEMP FP)
          val move_stm = Tr.MOVE(dst, Tr.TEMP src)
        in
          (acc_list @ [acc], save_stm @ [move_stm])
        end
      val (acc_list, save_stm) = foldl save_reg ([],[]) to_save

      fun restore_reg(acc, dst) = Tr.MOVE(Tr.TEMP dst, (exp acc (Tr.TEMP FP)))
      val restore_stm = ListPair.map restore_reg (acc_list, to_save)

            (* Disabled callee-save of registers since spilling is imelpmented*)
      val stm' = seq ([viewShift] @
                        save_stm @ [stm] @ restore_stm)

      (* val stm' = seq ([viewShift] @ [stm]) *)
    in
      stm'
    end

      (* Appends a sink instruction for regalloc. (Which registers are alive at
      * procedure exit). *)
  fun procEntryExit2 (frame, body) =
			body @ [A.OPER{assem="#SINK",
                    src=specialregs @ calleesaves,
                    dst=[],
                    jump=SOME([])}]

  fun int (i) =
    if i >= 0 then Int.toString i
    else "-" ^ Int.toString(~i)


      (* Creates procedure prolouge/epilogue ASM instrs. Namely, it handles
      * pseudo instructions to announce beginning of the function, insn to
      * create a new frame, and an insn to deallocate the frame *)
 fun procEntryExit3 (frame, body) =
       {prolog= (Symbol.name (name frame)) ^ ":\t#Procedure\n"^
                "#\tFrame size: " ^ (int(!(#offset frame) - wordSize)) ^ "\n" ^
                "\tsw $fp, " ^ (int(!(#offset frame))) ^ "($sp)\n" ^
                "\tmove $fp, $sp\n" ^
                "\taddi $sp, $fp, " ^ (int(!(#offset frame))) ^ "\n",
        body=body,
        epilog="\taddi $sp, $sp, " ^ int(0-(!(#offset frame))) ^ "\n" ^
               "\tlw $fp, " ^ int(!(#offset frame)) ^ "($sp)\n"^
               "\tjr $ra # End\n"}
	
end
structure Frame : FRAME = MipsFrame
