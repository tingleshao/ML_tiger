functor IntMapTable (type key
                     val getInt: key -> int
                     val getKey: int -> key) : TABLE =
struct
  type key=key
  type 'a table = 'a IntBinaryMap.map
  val empty = IntBinaryMap.empty
  fun enter (t, k, a) = IntBinaryMap.insert (t, getInt k, a)
  fun enter' ((k, a), table) = enter (table, k, a)
  fun look (t, k) = IntBinaryMap.find(t, getInt k)
  fun get (t, k, desc) = case look (t, k) of
                     SOME v => v
                   | NONE => raise Fail (desc ^ " not found")
  fun entries (t) =
      map (fn (i, v) => (getKey i, v))
          (IntBinaryMap.listItemsi (t : 'a table))
end