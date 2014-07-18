signature GENERAL_LISTS = sig
  type id
  type item
  type lists
  structure Set : ORD_SET sharing type Set.Key.ord_key = item

  datatype collection = List of item list
                      | Set of Set.set

  val getAsSet: lists -> id -> Set.set
  val getAsList: lists -> id -> item list
  val isMember: lists -> id -> item -> bool
  val isMember2: lists -> item -> id -> bool
  val isEmpty: lists -> id -> bool
  val move: lists -> id -> id -> item -> lists
  val move2: lists -> item -> id -> id -> lists
  val newId: string -> id
  val newLists: (id * collection) list -> lists

end

functor GeneralLists (structure Set : ORD_SET) : GENERAL_LISTS =
struct
	
structure Set = Set

type id = Symbol.symbol
type item = Set.item

datatype collection = List of item list
                    | Set of Set.set

type lists = collection Symbol.table

fun eq a b = Set.Key.compare (a, b) = General.EQUAL

fun get (lists, id) : collection =
    case Symbol.look (lists, id) of
      SOME collection => collection
    | NONE => raise Fail ("no item: " ^ (Symbol.name id))

fun getAsSet lists id =
    case get (lists, id) of
      List list => Set.addList (Set.empty, list)
    | Set set => set

fun getAsList lists id =
    case get (lists, id) of
      List list => list
    | Set set => Set.listItems set

fun isMember lists id item =
    case get (lists, id) of
      List list => List.exists (eq item) list
    | Set set => Set.member (set, item)

fun isMember2 lists item id =
    case get (lists, id) of
      List list => List.exists (eq item) list
    | Set set => Set.member (set, item)

fun isEmpty lists id =
    case get (lists, id) of
      List list => List.null list
    | Set set => Set.isEmpty set

fun move lists srcId dstId item =
    let
      fun removeList (_, []) = raise Fail "item was not in list"
        | removeList (item, item' :: rest) =
          if eq item item' then rest
          else item' :: (removeList (item, rest))

      fun removeSet (item, set) =
          if Set.member (set, item) then
            Set.delete (set, item)
          else
            raise Fail "item was not in list"

      fun remove (item, List list) = List (removeList (item, list))
        | remove (item, Set set) = Set (removeSet (item, set))

      val insertList = op::

      fun insertSet (item, set) = Set.add (set, item)

      fun insert (item, List list) = List (insertList (item, list))
        | insert (item, Set set) = Set (insertSet (item, set))

      val src = get (lists, srcId)
      val src' = remove (item, src)
      val dst = get (lists, dstId)
      val dst' = insert (item, dst)
    in
      foldl Symbol.enter'
            lists
            [(srcId, src'), (dstId, dst')]
    end

fun move2 lists item srcId dstId = move lists srcId dstId item

val newId = Symbol.symbol

fun newLists initials =
    foldr (fn ((id, initial), sets) =>
              Symbol.enter' ((id, initial),
                             sets))
          Symbol.empty
          initials

end