signature MAKEGRAPH =
sig
  val instrs2graph: Assem.instr list ->
                Flow.flowgraph * Graph.node list
end

structure MakeGraph : MAKEGRAPH =
struct
  structure A = Assem
  structure S = Symbol
  structure F = Flow
  structure G = Graph
  structure T = Graph.Table
	structure Set = Temp.Set

      (* Converts a list of instructions to a flow graph *)
  fun instrs2graph (instr_list : A.instr list) =
  let
    val control = G.newGraph()

        (* Initialize def, use and ismove tables *)
    fun init_def(A.OPER instr, node, defs) = T.enter(defs, node, (#dst instr))
      | init_def(A.LABEL instr, node, defs) = T.enter(defs, node, [])
      | init_def(A.MOVE instr, node, defs) = T.enter(defs, node, [(#dst instr)])

    fun init_use(A.OPER instr, node, uses) = T.enter(uses, node, (#src instr))
      | init_use(A.LABEL instr, node, uses) = T.enter(uses, node, [])
      | init_use(A.MOVE instr, node, uses) = T.enter(uses, node, [(#src instr)])

    fun init_ismove(A.OPER instr, node, ismoves) = T.enter(ismoves, node, false)
      | init_ismove(A.LABEL instr, node, ismoves) = T.enter(ismoves, node, false)
      | init_ismove(A.MOVE instr, node, ismoves) = T.enter(ismoves, node, true)

        (* Keep track of LABEL nodes in a table *)
    fun make_nodes (instr as A.LABEL {assem, lab}, (nodes, labs, node2instr)) =
        let val node = G.newNode(control)
        in
          (node::nodes,
          (S.enter(labs, lab, node)),
          (G.Table.enter(node2instr, node, instr)))
        end
      | make_nodes (instr, (nodes, labs, node2instr)) =
        let val node = G.newNode(control)
        in
          (node::nodes, labs,
          (G.Table.enter(node2instr, node, instr)))
        end

        (* nodes is a list of all nodes,
         * lab_table is a mapping from label -> node for link_jump
         * node2instr is a mapping from node -> insn
         * *)
    val (nodes, lab_table, node2instr) = foldl make_nodes
            ([], S.empty, G.Table.empty) instr_list

    val def = ListPair.foldl init_def G.Table.empty (instr_list, nodes)
    val use = ListPair.foldl init_use G.Table.empty (instr_list, nodes)
    val ismove = ListPair.foldl init_ismove G.Table.empty (instr_list, nodes)

    fun link_jump from to_lab = case S.look(lab_table, to_lab)
                                  of SOME to => G.mk_edge({from=from, to=to})
                                   | _ => ()

        (*(* In case of jump, do not link adjacent instructions *)
    fun link_edges (A.OPER {assem, dst, src, jump=SOME labs}, node, _) =
             ((app (link_jump node) labs); SOME node)
      | link_edges (instr, node, SOME next_node) =
          ((G.mk_edge {from=node, to=next_node});
          SOME node)
      | link_edges (_, node, NONE) = (SOME node)

    val _ =  ListPair.foldr link_edges NONE (instr_list, nodes); *)

    fun link_nodes (a::(b::c)) =
      let
        val instr = valOf(G.Table.look(node2instr, a))
      in
        (case instr
          of A.OPER {assem, dst, src, jump} =>
                (case jump
                  of SOME labs => (app (link_jump a) labs)
                   | NONE => (G.mk_edge {from=a, to=b}))
           | _ => G.mk_edge {from=a, to=b});
        link_nodes(b::c)
      end
      | link_nodes(_) = ()

    val _ = link_nodes(nodes)

        (* Doesn't work for some reason.. *)
    fun print_graph() =
      let
        fun node2str(node) =
        let
          val instr = G.Table.look(node2instr, node)
          val instr_str =  case instr
                             of SOME i => A.instr_str(i)
                              | NONE => "NA\n"
        in
          ((G.nodename node) ^ " = " ^
          String.substring(instr_str, 0, (size instr_str) -1))
        end
      in
        print (G.graph_to_str(control, node2str)^"\n")
      end
  in
    (
    (F.FGRAPH {control=control, def=def, use=use, ismove=ismove}, nodes))
  end
end
