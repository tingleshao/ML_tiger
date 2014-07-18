
structure Main = struct

   structure Tr = Translate
   structure F : FRAME = MipsFrame
   (*structure R = RegAlloc*)

 fun appendFiles out =
    let
      val str1 = TextIO.inputAll(TextIO.openIn("runtimele.s"))
      val str2 = TextIO.inputAll(TextIO.openIn("sysspim.s"))
      val str = str1 ^ str2
    in
      TextIO.output(out,str)
    end

 fun emitproc out (F.PROC{body,frame}) =
    let
    (* val _ = print ("emit " ^ Symbol.name(Frame.name frame) ^ "\n") *)
    (* val _ = Printtree.printtree(out,body); *)
      val stms = Canon.linearize body (* outputs a Tree.stm list*)
    (* val _ = app (fn s => Printtree.printtree(out,s)) stms; *)
      val stms' = Canon.traceSchedule(Canon.basicBlocks stms)  (* outputs a Tree.stm list*)
    (* val _ = (print (" stm primes: "^String.concat(map Tree.stm_to_str
          stms)^"\n")); *)

      val instrs = F.procEntryExit2(frame, List.concat(map (mipsGen.codegen frame) stms'))
      val _ = (print ("\ninstrs:"^String.concat(map (Assem.instr_str) instrs)))

      val {prolog, body=instrs', epilog} = F.procEntryExit3(frame,instrs)

      val _ = (print ("\ninstrs2:"^String.concat(map (Assem.instr_str) instrs')))

      val (instrs'', frame, allocation) = RegAlloc.alloc(instrs',frame)

      val format0 = Assem.format(Temp.makestring)
      val format1 = Assem.format(fn (t)=> ("$" ^ valOf(Temp.Table.look(allocation, t))))
    in
      TextIO.output(out, prolog);
      (app (fn i => TextIO.output(out,format1 i)) instrs'');
      TextIO.output(out, epilog)
    end

  | emitproc out (F.STRING(lab,s)) =
    TextIO.output(out, s)

  fun withOpenFile fname f =
    let val out = TextIO.openOut fname
    in (appendFiles out before f out before TextIO.closeOut out)
          handle e => (TextIO.closeOut out; raise e)
    end

  fun compile (filename, outfilename) =
    let
      val absyn = Parse.parse (filename)
      val frags = ((*FindEscape.prog absyn;*) Semant.transProg absyn)
    in
      (* (print ("length of frags: " ^(Int.toString (length (#expx frags))) ^
      * "\n"));*)
      withOpenFile outfilename (fn out => (app (emitproc out) (#expx frags)))
    end

end



