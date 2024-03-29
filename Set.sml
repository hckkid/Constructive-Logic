signature SET = sig
	type ''a myset = ''a list
	val belongs : ''a*(''a list) -> bool
	val makeSet : ''a list -> ''a myset
	val additem : ''a*(''a list) -> ''a myset
	val addlist : (''a list)*(''a myset) -> ''a myset
	val union : (''a myset)*(''a myset) -> ''a myset
	val intersection : (''a myset)*(''a myset) -> ''a myset
	val getlist : ''a myset -> ''a list
	val addToAll : ''a*''a myset myset -> ''a myset myset
	val powerSet : ''a myset -> ''a myset myset
	val subset : ''a myset * ''a myset -> bool
	val equals : ''a myset * ''a myset -> bool
	val diff : ''a myset * ''a myset -> ''a myset
end
structure Set :> SET = struct
	type ''a myset = ''a list
	fun belongs (x,[]) = false
		| belongs (x,y::ys) = if (x=y) then true else belongs(x,ys)
	fun makeSet [] = []
		| makeSet (x::xs) =
			let
				val tmpst = makeSet xs
				fun adder(z) = 
					if (belongs(z,tmpst)) then tmpst
					else z::tmpst
			in adder(x)
			end
	fun additem (x,tmpst) = if (belongs(x,tmpst)) then tmpst else x::tmpst
	fun addlist ([],tmpst) = tmpst
		| addlist (x::xs,tmpst) = additem(x,addlist(xs,tmpst))
	fun union ([],tmpst) = tmpst
		| union (x::xs,tmpst) = additem(x,union(xs,tmpst))
	fun intersection ([],tmpst) = nil
		| intersection (x::xs,tmpst) = if (belongs(x,tmpst)) then x::intersection(xs,tmpst) else intersection(xs,tmpst)
	fun getlist [] = []
		| getlist (x::xs) = x::xs
	fun addToAll (x,[]) = []
		| addToAll (x,y::ys) = additem(x,y)::addToAll(x,ys)
	fun powerSet [] = [[]]
		| powerSet (x::xs) = (powerSet(xs)@addToAll(x,powerSet(xs)))
	fun subset([],x) = true
		| subset(x::xs,[]) = false
		| subset(x::xs,y) = if (belongs(x,y)) then subset(xs,y) else false
	fun equals(x,y) = if (subset(x,y) andalso subset(y,x)) then true else false
	fun diff([],y) = []
		| diff(x::xs,y) = if (belongs(x,y)) then diff(xs,y) else x::diff(xs,y)
end;
