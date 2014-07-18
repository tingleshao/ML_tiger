signature REG_ALLOC =
sig
	structure F : FRAME
	type allocation = Frame.register Temp.Table.table
	val alloc : Assem.instr list * Frame.frame -> Assem.instr list * Frame.frame * allocation
end

structure RegAlloc : REG_ALLOC =
struct
	structure F : FRAME = MipsFrame

	structure G = Flow.Graph
	structure T = Temp

	type allocation = F.register Temp.Table.table

	datatype igraph =
	IGRAPH of {graph: G.graph,
	tnode: T.temp -> G.node,
	gtemp: G.node -> T.temp,
	moves: (G.node * G.node) list}

	fun redo (instrs, frame, spills) =

	let
		fun eq a b = a = b

		fun spill (temp, instrs) =
      let
        val access = Frame.allocLocal frame true
        val accessExp = F.exp access (Tree.TEMP F.FP)
        fun moveInstr (dst, src) = mipsGen.codegen frame (Tree.MOVE (dst, src))
        fun fetchInstrBuilder temp = moveInstr (Tree.TEMP temp, accessExp)
        fun storeInstrBuilder temp = moveInstr (accessExp, Tree.TEMP temp)

        fun transform insnBuilder temps =
          if List.exists (eq temp) temps then
            let
              val newtemp = Temp.newtemp ()
              fun replace newtemp temp' =
              if temp = temp' then newtemp else temp'
            in
              (insnBuilder newtemp, map (replace newtemp) temps)
            end
          else
            ([], temps)

        fun redoInsn (Assem.OPER {assem, dst, src, jump}) =
            let
              val (pre, src') = transform fetchInstrBuilder src
              val (post, dst') = transform storeInstrBuilder dst
            in
              pre @ [Assem.OPER {assem=assem,
              dst=dst',
              src=src',
              jump=jump}] @ post
            end
        | redoInsn (Assem.MOVE {assem, src, dst}) =
            let
              val (pre, [src']) = transform fetchInstrBuilder [src]
              val (post, [dst']) = transform storeInstrBuilder [dst]
            in
              pre @ [Assem.MOVE {assem=assem,
              dst=dst',
              src=src'}] @ post
            end
        | redoInsn instr = [instr]
      in
        foldl (fn (instr, instrs) =>
        instrs @ (redoInsn instr))
        []
        instrs
      end
	in
		foldl spill instrs spills
	end

	fun alloc(instrs, frame) =
    let
      val (fgraph, nodelist) = MakeGraph.instrs2graph(instrs)
      val (igraph, liveoutmapping) = Liveness.interferenceGraph(fgraph,nodelist)

      val Flow.FGRAPH {control, def, use, ismove } = fgraph
      val Liveness.IGRAPH {graph, tnode, gtemp, moves} = igraph

      fun spillCost node =
        let
          val temp = gtemp node

          fun getOccurences node =
            let
              val uses = Temp.Set.addList(Temp.Set.empty, Graph.Table.get (use, node, "use[n]"))
              val defs = Temp.Set.addList(Temp.Set.empty, Graph.Table.get (def, node, "def[n]"))
              val useCount = if Temp.Set.member (uses, temp) then 1 else 0
              val defCount = if Temp.Set.member (defs, temp) then 1 else 0
            in
              useCount + defCount
            end

          val occurences = foldl (fn (node, total) =>
          getOccurences node + total)
          0
          nodelist

          val degree = length (Graph.adj node)
        in
          Real./ (Real.fromInt occurences, Real.fromInt degree)
        end

      val i_graph = G.newGraph()
      (* val fake_igraph = {graph=i_graph, tnode=tnode, gtemp=gtemp, moves=moves}*)
      val allocation = F.tempMap
      val reglist = F.availableregisters

      val (newalloc, spills) =
      Color.color {interference = igraph,
                  initial = allocation,
                  spillCost = spillCost,
                  registers = reglist}

    in
      if List.null spills then
        (instrs, frame, newalloc)
      else
        alloc (redo (instrs, frame, spills), frame)
    end
end


