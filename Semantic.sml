use "Form.sml";
signature semantic = sig
	val getModel : string list -> Form.form Set.myset
	val validates : Form.form Set.myset*Form.form -> bool
end
structure Semantic :> semantic = struct
	fun getModel [] = []
		| getModel (x::xs) = (Form.propSymb(x))::(getModel xs)
	fun validates (M,Form.Absurdum) = false
		| validates (M,Form.propSymb c) = (if (Set.belongs(Form.propSymb c,M)) then true else false)
		| validates (M,Form.Negation p) = not(validates(M,p))
		| validates (M,Form.Conjunction(A,B)) = (validates(M,A) andalso validates(M,B))
		| validates (M,Form.Disjunction(A,B)) = ((validates(M,A)) orelse (validates(M,B)))
		| validates (M,Form.Implication(A,B)) = (((not(validates(M,A)))) orelse (validates(M,B)))
end;
