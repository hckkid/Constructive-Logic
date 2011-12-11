use "Form.sml";
signature GENTZENSYSTEM = sig
	datatype sequent = seq of Form.form Set.myset * Form.form Set.myset
	datatype sequentTree = seqtree of sequent | seqtree1 of sequent*sequentTree | seqtree2 of sequent*sequentTree*sequentTree
	exception SomethingWicked
	val generateSequentTree : Form.form -> sequentTree
	val isValid : Form.form -> bool
	val isContradiction : Form.form -> bool
	val isSatisfiable : Form.form -> bool
	val testAllNode : sequentTree -> bool
	val printSequentTree : sequentTree -> unit
end
structure GentzenSystem :> GENTZENSYSTEM = struct
	datatype sequent = seq of Form.form Set.myset * Form.form Set.myset
	datatype sequentTree = seqtree of sequent | seqtree1 of sequent*sequentTree | seqtree2 of sequent*sequentTree*sequentTree
	exception SomethingWicked
	fun isBreakable(Form.propSymb(c)) = false
		| isBreakable(Form.Absurdum) = false
		| isBreakable(Form.Negation(Form.Absurdum)) = false
		| isBreakable(Form.Negation(Form.propSymb(c))) = false
		| isBreakable(f) = true
	fun isAnyBreakable([]) = false
		| isAnyBreakable(x::xs) = if (isBreakable(x)) then true else isAnyBreakable(xs)
	fun mergeX(x,[]) = []
		| mergeX(x,(y,z)::rm) = (Set.union([x],y),z)::mergeX(x,rm)
	fun mergeY([],y) = []
		| mergeY((x,z)::rm,y) = (x,Set.union([y],z))::mergeY(rm,y)
	fun breakY(x,[]) = [(x,[])]
		| breakY(x,y::ys) = if (isBreakable(y)) then
				let
					fun breakIt(x,Form.Conjunction(A,B)::y) = [(x,Set.union([A],y)),(x,Set.union([B],y))]
						| breakIt(x,Form.Disjunction(A,B)::y) = [(x,Set.union([A,B],y))]
						| breakIt(x,Form.Implication(A,B)::y) = [(Set.union([A],x),Set.union([B],y))]
						| breakIt(x,Form.Negation(A)::y) = [(Set.union([A],x),y)]
				in breakIt(x,y::ys)
				end
			else mergeY(breakY(x,ys),y)
	fun breakX([],y) = [([],y)]
		| breakX(x::xs,y) = if (isBreakable(x)) then
				let
					fun breakIt(Form.Conjunction(A,B)::x,y) = [(Set.union([A,B],x),y)]
						| breakIt(Form.Disjunction(A,B)::x,y) = [(Set.union([A],x),y),(Set.union([B],x),y)]
						| breakIt(Form.Implication(A,B)::x,y) = [(x,Set.union([A],y)),(Set.union([B],x),y)]
						| breakIt(Form.Negation(A)::x,y) = [(x,Set.union([A],y))]
				in breakIt(x::xs,y)
				end
			else mergeX(x,breakX(xs,y))
	fun generateSequentTree(f) = 
		let 
			fun tmpGenerate((x,y)) = 
				if (isAnyBreakable(x)) then
					let
						fun generator([t]) = seqtree1(seq(x,y),tmpGenerate(t))
							| generator(t1::t2::[]) = seqtree2(seq(x,y),tmpGenerate(t1),tmpGenerate(t2))
							| generator(_) = raise SomethingWicked
					in generator(breakX(x,y))
					end
				else if (isAnyBreakable(y)) then
					let
						fun generator([t]) = seqtree1(seq(x,y),tmpGenerate(t))
							| generator(t1::t2::[]) = seqtree2(seq(x,y),tmpGenerate(t1),tmpGenerate(t2))
							| generator(_) = raise SomethingWicked
					in generator(breakY(x,y))
					end
				else seqtree(seq(x,y))
				handle SomethingWicked => raise SomethingWicked
		in tmpGenerate(([],[f]))
		end
		handle SomethingWicked => raise SomethingWicked
	fun tmpInValidlist([]) = false
		| tmpInValidlist(Form.propSymb(c)::xs) = if (Set.belongs(Form.Negation(Form.propSymb(c)),xs)) 
			then true else tmpInValidlist(xs)
		| tmpInValidlist(Form.Absurdum::xs) = true
		| tmpInValidlist(Form.Negation(Form.propSymb(c))::xs) = if (Set.belongs(Form.propSymb(c),xs)) then true else tmpInValidlist(xs)
		| tmpInValidlist(Form.Negation(Form.Absurdum)::xs) = tmpInValidlist(xs)
	fun isFalsifiable(x,y) = 
		let
			fun falsifier(x,y) = if (Set.belongs(Form.Absurdum,x)) then false else
						if (Set.belongs(Form.Negation(Form.Absurdum),y)) then false else
						if (tmpInValidlist(x) orelse tmpInValidlist(y)) then false else
						if (Set.intersection(x,y)=[]) then true else false
		in falsifier(x,y)
		end
	fun testAllNode(seqtree(seq(x,y))) = isFalsifiable(x,y)
		| testAllNode(seqtree1(_,f)) = testAllNode(f)
		| testAllNode(seqtree2(_,f1,f2)) = (testAllNode(f1) orelse testAllNode(f2))
	fun isValid(f) = not(testAllNode(generateSequentTree(f)))
	fun isContradiction(f) = isValid(Form.Negation(f))
	fun isSatisfiable(f) = if (not (isContradiction(f))) then true else false
	fun printSequentTree(st) = 
		let
			fun printSeq(seq(x,y)) = 
				let
					fun tmpPrint([]) = ""
						| tmpPrint([x]) = Form.format(x)
						| tmpPrint(x::xs) = String.concat(Form.format(x)::","::tmpPrint(xs)::[])
				in String.concat("< "::tmpPrint(x)::" >"::" , "::"< "::tmpPrint(y)::" >"::[])
				end
			fun printer(seqtree(x),y) = (print(y);print(printSeq(x));print("\n"))
				| printer(seqtree1(x,y),z) = (print(z);print(printSeq(x));print("\n");printer(y,String.concat(z::"\t"::[])))
				| printer(seqtree2(x,y,z),t) = (print(t);print(printSeq(x));print("\n");printer(y,String.concat(t::"\t"::[]));printer(z,String.concat(t::"\t"::[])))
		in
			printer(st,"")
		end;
end
