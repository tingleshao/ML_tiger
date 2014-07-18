signature LIVENESS = sig
  datatype igraph =
    IGRAPH of {graph: Graph.graph,
               tnode: Temp.temp -> Graph.node,
               gtemp: Graph.node -> Temp.temp,
               moves: (Graph.node * Graph.node) list}

	structure G: GRAPH

  val interferenceGraph:
    Flow.flowgraph* G.node list -> igraph * (Flow.Graph.node -> Temp.temp list)

  val show : TextIO.outstream * igraph -> unit

	val toStr : igraph -> string
end

structure Liveness : LIVENESS =
struct
  structure Graph = Graph
  structure F = Flow
  structure G = Flow.Graph
  structure T = Temp

  structure S = ListSetFn(type ord_key = int
                    val compare = Int.compare)

  datatype igraph =
    IGRAPH of {graph: G.graph,
               tnode: T.temp -> G.node,
               gtemp: G.node -> T.temp,
               moves: (G.node * G.node) list}

      (* Convert a temp list to a set *)
  fun list_to_set(temps_l) = S.addList(S.empty, temps_l)

      (* For use with def/use tables *)
  fun get_templist(table, node) =
    case G.Table.look(table, node)
      of SOME temp_list => temp_list
       | NONE => []

  fun ls_to_str(n, lab, conv, l) = (G.nodename n) ^ "_" ^ lab ^ " <=> "
    ^ (String.concatWith "," (map (fn x => conv x) (l)))^"\n"


  fun get_livemaps(F.FGRAPH{control, def, use, ismove}) =
    let
      val fnodes = (G.nodes control) (*flow nodes?*)

      fun get_liveSet(live_map, n) =
        (case G.Table.look(live_map, n)
           of SOME entry => entry
            | NONE => ((ErrorMsg.impossible ((G.nodename n)^
                      " not found in liveMap"));
                      (S.empty)))

          (* Initialize in[n] and out[n] to empty liveSets *)
      val init_live_in = foldl (fn (n, live_in) =>
            G.Table.enter(live_in, n, S.empty)) G.Table.empty fnodes
      val init_live_out = foldl (fn (n, live_out) =>
            G.Table.enter(live_out, n, S.empty)) G.Table.empty fnodes
          (* Used to update the in[n] and out[n] for a node n*)
      fun update_node(n, (live_in, live_out, stop)) =
        let
          val s_use = list_to_set(get_templist(use, n))
          val s_def = list_to_set(get_templist(def, n))
          val in_n = get_liveSet(live_in, n)
          val out_n = get_liveSet(live_out, n)

          val in_n' = S.union(s_use, (S.difference(out_n, s_def)))
          val out_n' = foldr (fn (s, out) =>
                  S.union(out, (get_liveSet(live_in, s))))
                S.empty (G.succ n)

          (* val _ = (print (ls_to_str(n, "use ", T.makestring, get_templist(use, n))))
          val _ = (print (ls_to_str(n, "def ", T.makestring, get_templist(def, n))))


          val _ = (print (ls_to_str(n, "succ", G.nodename, G.succ n)))

          val _ = (print (ls_to_str(n, "in ", T.makestring, S.listItems in_n')))
          val _ = (print (ls_to_str(n, "out ", T.makestring, S.listItems
          out_n')))

          val _ = ((print ("Node " ^ (G.nodename n) ^ " adjs:"));
          (app (fn s => (print (" " ^ (G.nodename s)))) (G.adj n));
          (print "\n"))

          *)

          val live_in' = G.Table.enter(live_in, n, in_n')
          val live_out' = G.Table.enter(live_out, n, out_n')

          val stop' = stop andalso (S.equal(in_n', in_n)) andalso
                      (S.equal(out_n', out_n))

           val _ = ((print ("Node " ^ (G.nodename n) ^ " adjs:"));
                  (app (fn s => (print (" " ^ (G.nodename s)))) (G.adj n));
                  (print "\n"))

        in
          (live_in', live_out', stop')
        end

      and update_nodes (live_in, live_out)=
        let
          val (live_in', live_out', stop) =
            (foldl update_node (live_in, live_out, true) fnodes)
        in
          if stop then (live_in', live_out')
          else update_nodes(live_in', live_out')
        end
    in
      update_nodes(init_live_in, init_live_out)
    end

  fun interferenceGraph (fgraph as F.FGRAPH{control, def, use, ismove}, nodelist:G.node list) =
    let
      val (live_in, live_out) = get_livemaps(fgraph)
      fun liveMap_to_map live_out node =
        case G.Table.look(live_out, node)
          of SOME (set) => S.listItems set
           | NONE => ((ErrorMsg.impossible
              ("Node " ^ (G.nodename node) ^ " not found in live_out"));[])

      (* Mapping for FlowGraph node -> live out temps*)
      val get_out = liveMap_to_map live_out

      val i_graph = G.newGraph()
      val fnodes = (G.nodes control)
			(*print out fnodes*)

			val _ = print "-=========-\nfnodes: \n"
			val _ = (foldl (fn (i,[]) => (print ("fnode: " ^ i ^ " ");[])) []	(map (G.nodename) fnodes))
  	  val _ = (print "\n============\n")


          (* Retrieve list of temps from def and use table *)
      val temps = S.listItems(foldl (fn(n, temps) =>
          let
            val def_s = list_to_set(get_templist(def, n))
            val use_s = list_to_set(get_templist(use, n))
            val temps_n = S.union(def_s, use_s)
          in
            (S.union(temps, temps_n))
          end)
        S.empty fnodes)

		 val _ = (foldl (fn (i,[]) => (print ("temp: " ^ i ^ " ");[])) []	(map (Int.toString) temps))
 		 val _ = (print "\n")
      fun make_maps (temp, (tnode, gtemp)) =
        let val inode = G.newNode(i_graph)
        in (T.Table.enter(tnode, temp, inode), G.Table.enter(gtemp, inode, temp))
        end

          (* tnode is a mapping from temp -> inode
          * gtemp is a mapping from inode -> temp *)
      val (tnode, gtemp) =
        let
          val (t_table, g_table) = foldl make_maps (T.Table.empty, G.Table.empty) temps

          fun tnode temp =
            case T.Table.look(t_table, temp)
              of SOME(node) => node
               | NONE => (ErrorMsg.impossible
                  ("Node mapping from " ^ (T.makestring temp) ^ " does not exist"))

          fun gtemp inode =
            case G.Table.look(g_table, inode)
              of SOME(temp) => temp
               | NONE => (ErrorMsg.impossible
                  ("Temp mapping from " ^ (G.nodename inode) ^ " does not exist"))
        in
          (tnode, gtemp)
        end

          (* Convert flowgraph node to interference graph node and then draw
          * edges to anything that's live. We only use the live_out map here
          * to avoid redundant connections
          *)
      fun connectify(fnode) =
        let
          val (l_def) = S.listItems(list_to_set(get_templist(def, fnode)))
          val out_n = get_out fnode
          fun make_edge(def) =
            let val from = tnode def
            in app (fn(temp) => if temp = def then ()
                                else G.mk_edge{from=from, to=(tnode temp)})
                    out_n
            end
        in
          app make_edge l_def
        end

        (* Connectify all the flowgraph nodes! *)
      val _ = app connectify fnodes

          (* Append (target, source) registers to moves if fgraph is a MOVE insn *)
      fun make_moves(fnode, moves) =
        let
          val ismove_n = case (G.Table.look(ismove, fnode))
                           of SOME is_move_n => is_move_n
                            | NONE => ((ErrorMsg.impossible
                                ((G.nodename fnode) ^ "not found in ismove"));
                                false)

          val def_n = get_templist(def, fnode)
          val use_n = get_templist(use, fnode)
        in
          if ismove_n then
            (tnode (hd def_n), tnode (hd use_n)) :: moves
          else
            moves
        end

      val moves = foldl make_moves [] fnodes
    in

      (IGRAPH {graph=i_graph, tnode=tnode, gtemp=gtemp, moves=moves},
      get_out)
    end

  fun show (outstream, IGRAPH {graph=i_graph, tnode=tnode, gtemp=gtemp, moves=moves}) =
    TextIO.output(outstream,
        G.graph_to_str(i_graph, (fn n => T.makestring(gtemp n))))

 fun toStr(IGRAPH {graph=i_graph, tnode=tnode, gtemp=gtemp, moves=moves}) =
							G.graph_to_str(i_graph, (fn n => T.makestring(gtemp n)))

end
