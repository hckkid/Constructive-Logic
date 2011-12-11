use "Form.sml";
signature sem1 = sig
	exception IncompleteValuation
	exception wrongFormula
	val valuation : (string*char) list -> (Form.form*bool) Set.myset
	val interperation : (Form.form*bool) Set.myset*Form.form -> bool
end
structure Sem1 :> sem1 = struct
	exception wrongFormula
	exception IncompleteValuation
	fun valuation [] = []
		| valuation((p:string,q:char)::xs) = (Form.propSymb p,(if ((q = #"T") orelse (q = #"t")) then true else false))::valuation(xs)
	fun interperation (valu,Form.Absurdum) = false
		| interperation (valu,Form.propSymb c) = (if (Set.belongs((Form.propSymb c,true),valu)) then true else false)
		| interperation (valu,Form.Negation p) = not(interperation(valu,p))
		| interperation (valu,Form.Conjunction(A,B)) = (interperation(valu,A) andalso interperation(valu,B))
		| interperation (valu,Form.Disjunction(A,B)) = ((interperation(valu,A)) orelse (interperation(valu,B)))
		| interperation (valu,Form.Implication(A,B)) = (((not(interperation(valu,A)))) orelse (interperation(valu,B)))
end
