signature COLOR = sig
	structure F : FRAME

	type allocation = Frame.register Temp.Table.table

	val color : {
	interference: Liveness.igraph,
	initial: allocation,

	spillCost: Graph.node -> real,
	registers: Frame.register list}
	-> allocation * Temp.temp list
end

structure Color :> COLOR =
struct
	structure Set = ListSetFn(struct
		type ord_key = Temp.temp
		val compare = Int.compare
	end)

	structure G = Liveness.G
	structure F : FRAME = MipsFrame

	structure GS = G.Set and GT = G.Table

	(* Register Set *)
	structure RS = BinarySetFn (type ord_key = string
	                            val compare = String.compare)

	structure NodeList = GeneralLists(structure Set = GS)

	(* Move Set *)
	structure MS = BinarySetFn (type ord_key = Temp.temp * Temp.temp
	                            fun compare ((t1, t2), (t1', t2')) =
	                                if t1 = t1' then
	                                  Int.compare (t2, t2')
	                                else
	                                  Int.compare (t1, t1'))

	structure MoveWL = GeneralLists(structure Set = MS)

	structure Id = struct
		val colored = NodeList.newId "colored";
		val init = NodeList.newId "init";
		val precolored = NodeList.newId "precolored";
		val selected = NodeList.newId "selected";
		val simplify = NodeList.newId "simplify";
		val spill = NodeList.newId "spill";
		val spilled = NodeList.newId "spilled";
	end

	fun toNodeSet list = GS.addList (GS.empty, list)

	fun min ([], _) = raise Fail "list empty!"
	  | min (head :: tail, f : Graph.node -> real) =
	    let
	      val (item, _) =
          foldl (fn (item, (minItem, minVal)) =>
                  let val itemVal = f item
                  in
                    if itemVal < minVal then
                      (item, itemVal)
                    else
                      (minItem, minVal)
                  end)
                (head, f head) tail
	    in
	      item
	    end

	type allocation = F.register Temp.Table.table

	fun color {interference, initial : allocation, spillCost : Graph.node -> real, registers : F.register list} =
    let
      val Liveness.IGRAPH {graph, tnode, gtemp, moves} = interference


      val _ = print(Liveness.toStr(interference))

      val nodes = G.nodes (graph)

      val colorPane = RS.addList(RS.empty, registers)
      val _ = (print ("\n\nnumber of availale colors: "^ Int.toString(RS.numItems(colorPane)) ^ "\n"))

      fun isPrecolored node =
        case Temp.Table.look (initial, gtemp node)
          of SOME _ => true
           | NONE => false

      val (precolored, uncolored) =
          List.partition isPrecolored (Graph.nodes graph)

      val gls = NodeList.newLists
          [(Id.precolored, NodeList.Set (toNodeSet precolored)),
          (Id.init, NodeList.Set (toNodeSet uncolored)),
          (Id.simplify, NodeList.Set (toNodeSet [])),
          (Id.spill, NodeList.Set (toNodeSet [])),
          (Id.spilled, NodeList.Set (toNodeSet [])),
          (Id.colored, NodeList.Set (toNodeSet [])),
          (Id.selected, NodeList.List [])]

  val k = List.length registers

  val degrees =
    foldl GT.enter' GT.empty
        (map (fn node => (node, List.length (Graph.adj node))) uncolored)

  fun initgls (gls, degrees) =
    let
      fun initt(node, gls ) =
        let
          val moveTo = NodeList.move2 gls node Id.init
        in
          if GT.get (degrees, node, "degree[n]") >= k then
            moveTo Id.spill
          else
            moveTo Id.simplify
        end
    in
      GS.foldl initt
      gls (NodeList.getAsSet gls Id.init)
    end

  val gls = initgls (gls, degrees)

  fun adjc (node, gls) =
    foldl NodeList.Set.difference
          (NodeList.Set.addList (NodeList.Set.empty, Graph.adj node))
          [NodeList.getAsSet gls Id.simplify ]

  (*for simplify*)
  fun decrement (node, (gls, degrees)) =
    let
      val degree = GT.get (degrees, node, "degree[n]")
      val degrees' = GT.enter (degrees, node, degree - 1)
      val gls' =
        if degree = k then
          NodeList.move gls Id.spill Id.simplify node
        else
          gls
    in
      (gls', degrees')
    end

  fun simplify (gls, degrees) =
    case NodeList.getAsList gls Id.simplify
      of [] => (gls, degrees)
       | node :: _ =>
           let
             val gls' = NodeList.move gls Id.simplify Id.selected node
           in
             NodeList.Set.foldl decrement
                           (gls', degrees)
                           (adjc (node, gls'))
           end

  fun selectSpill (gls, degrees) =
      let
        val m = min (NodeList.getAsList gls Id.spill, spillCost)
      in
        (NodeList.move gls Id.spill Id.simplify m,
         degrees)
      end

  fun loop (gls, degrees) =
      let
        fun notEmpty id = not (NodeList.isEmpty gls id)
      in
        (*if simplify not empty*)
        if notEmpty Id.simplify then
          loop (simplify (gls, degrees))
        (*if spill not empty*)
        else if notEmpty Id.spill then
          loop (selectSpill (gls, degrees))
        else
          (gls, degrees) (* done *)
      end

  val (gls, degrees) = loop (gls, degrees)

  (*move the job of deciding color into colorTable*)
  fun colorNode (node, color, allocs) =
      Temp.Table.enter (allocs, gtemp node, color)


  fun getNodeColor(node, allocs) =
      Temp.Table.get (allocs, gtemp node, "color[n]")

  (*set color*)
  fun colorTable (gls, allocs) =
    (*if select, then ...
     * when it is marked select?*)
    case NodeList.getAsList gls Id.selected
      of [] => (gls, allocs)
       | node :: _ =>
          let
            fun neighborColor node =
              let
                (*val node = getAlias (node, aliases, gls)*)
                (*retrieve the colored and precolored list that equal to node*)
                val isMember = NodeList.isMember2 gls node
              in
                if isMember Id.colored orelse isMember Id.precolored then
                SOME (getNodeColor (node,allocs))
                else
                NONE
              end

            (*RSet add used colors for a given node*)
            val usedColors = RS.addList (RS.empty,
                  List.mapPartial neighborColor (Graph.adj node))

            val okColors = RS.difference (colorPane, usedColors)

            val (gls', allocs') =
              case RS.listItems okColors
                    (*if no useable colors, spill, else color it*)
                of [] => (NodeList.move gls Id.selected Id.spilled node, allocs)
                 | color :: _ => (NodeList.move gls Id.selected Id.colored node,
                      (*here allocs got changed*)
                      colorNode(node, color, allocs))
          in
            colorTable (gls',allocs')
          end

    (* gls is the lists keeping nodes
    * allocs is the str keeping alloc infos *)
    (* color based on that *)
    val (gls, allocs) = colorTable (gls, initial)

    val returnSpills = map gtemp (NodeList.getAsList gls Id.spilled)
  in
    (allocs, returnSpills)
  end
end
