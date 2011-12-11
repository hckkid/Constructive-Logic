use "Semantic.sml";
signature normalForms = sig
	val toNNF : Form.form -> Form.form
	val toCNF : Form.form -> Form.form
	val toDNF : Form.form -> Form.form
end
structure NormalForms :> normalForms = struct
	fun toNNF Form.Absurdum = Form.Absurdum
		| toNNF (Form.propSymb c) = (Form.propSymb c)
		| toNNF (Form.Negation(Form.propSymb c)) = Form.Negation(Form.propSymb(c))
		| toNNF (Form.Negation(Form.Absurdum)) = Form.Negation(Form.Absurdum)
		| toNNF (Form.Negation(Form.Negation(A))) = toNNF(A)
		| toNNF (Form.Negation(Form.Conjunction(A,B))) = Form.Disjunction(toNNF(Form.Negation(A)),toNNF(Form.Negation(B)))
		| toNNF (Form.Negation(Form.Disjunction(A,B))) = Form.Conjunction(toNNF(Form.Negation(A)),toNNF(Form.Negation(B)))
		| toNNF (Form.Negation(A)) = toNNF(Form.Negation(toNNF(A)))
		| toNNF (Form.Conjunction(A,B)) = Form.Conjunction(toNNF(A),toNNF(B))
		| toNNF (Form.Disjunction(A,B)) = Form.Disjunction(toNNF(A),toNNF(B))
		| toNNF (Form.Implication(A,B)) = Form.Disjunction(toNNF(Form.Negation(A)),toNNF(B))
	fun toCNF fm=
		let
			val fm' = toNNF(fm)
			fun toCNFn Form.Absurdum = Form.Absurdum
				| toCNFn (Form.propSymb c) = (Form.propSymb c)
				| toCNFn (Form.Negation(A)) = Form.Negation(A)
				| toCNFn (Form.Conjunction(A,B)) = Form.Conjunction(toCNFn(A),toCNFn(B))
				| toCNFn (Form.Disjunction(A,B)) = 
					let
						val A' = toCNFn(A)
						val B' = toCNFn(B)
						fun tmpDis (a,Form.Conjunction(b,c)) = Form.Conjunction(toCNFn(Form.Disjunction(a,b)),toCNFn(Form.Disjunction(a,c)))
							| tmpDis (Form.Conjunction(a,b),c) = Form.Conjunction(toCNFn(Form.Disjunction(a,c)),toCNFn(Form.Disjunction(b,c)))
							| tmpDis (a,b) = Form.Disjunction(a,b)
					in tmpDis(A',B')
					end
			in toCNFn(fm')
		end
	fun toDNF fm=
		let
			val fm' = toNNF(fm)
			fun toDNFn Form.Absurdum = Form.Absurdum
				| toDNFn (Form.propSymb c) = (Form.propSymb c)
				| toDNFn (Form.Negation(A)) = Form.Negation(A)
				| toDNFn (Form.Disjunction(A,B)) = Form.Disjunction(toDNFn(A),toDNFn(B))
				| toDNFn (Form.Conjunction(A,B)) = 
					let
						val A' = toDNFn(A)
						val B' = toDNFn(B)
						fun tmpCon (a,Form.Disjunction(b,c)) = Form.Disjunction(toDNFn(Form.Conjunction(a,b)),toDNFn(Form.Conjunction(a,c)))
							| tmpCon (Form.Disjunction(a,b),c) = Form.Disjunction(toDNFn(Form.Conjunction(a,c)),toDNFn(Form.Conjunction(b,c)))
							| tmpCon (a,b) = Form.Conjunction(a,b)
					in tmpCon(A',B')
					end
			in toDNFn(fm')
		end
end
signature proofSystem = sig
	val isTautology : Form.form -> bool
	val isContradiction : Form.form -> bool
	val areEquivalent : Form.form*Form.form -> bool
	val isValidCNF : Form.form -> bool
	val isValidDNF : Form.form -> bool
end
structure ProofSystem :> proofSystem = struct
	fun isTautology f =
		let
			val x = Form.getpropSymbs(f)
			val px = Set.powerSet(x)
			val pm = 
				let
					fun Powm [] = []
						| Powm (y::ys) = (Semantic.getModel(y)::Powm(ys))
				in Powm(px)
				end
			fun tauto (f',[]) = true
				| tauto (f',z::zs) = if (Semantic.validates(z,f') = true) then tauto(f',zs) else false
		in tauto(f,pm)
		end
	fun isContradiction f =
		let
			val x = Form.getpropSymbs(f)
			val px = Set.powerSet(x)
			val pm = 
				let
					fun Powm [] = []
						| Powm (y::ys) = (Semantic.getModel(y)::Powm(ys))
				in Powm(px)
				end
			fun tauto (f',[]) = true
				| tauto (f',z::zs) = if (Semantic.validates(z,f') = false) then tauto(f',zs) else false
		in tauto(f,pm)
		end
	fun areEquivalent (f1,f2) = if (isTautology(Form.Implication(f1,f2)) andalso isTautology(Form.Implication(f1,f2))) then true else false
	fun isValidCNF(f)=
		let
			val f' = NormalForms.toCNF(f)
			fun tmpValid (Form.Conjunction(A,B)) = (tmpValid(A) andalso tmpValid(B))
			| tmpValid (Form.Absurdum) = false
			| tmpValid (Form.propSymb c) = false
			| tmpValid (Form.Negation(Form.Absurdum)) = true
			| tmpValid (Form.Negation(Form.propSymb c)) = false
			| tmpValid (f) = 
				let 
					fun lister (Form.Absurdum) = ([],[],false)
						| lister (Form.propSymb c) = (Set.makeSet([c]),[],false)
						| lister (Form.Negation(Form.Absurdum)) = ([],[],true)
						| lister (Form.Negation(Form.propSymb c)) = ([],Set.makeSet([c]),false)
						| lister (Form.Disjunction(A',B')) =
							let
								val (plst1,nplst1,flag1) = lister(A')
								val (plst2,nplst2,flag2) = lister(B')
							in ( Set.union(plst1,plst2) , Set.union(nplst1,nplst2) , (flag1 orelse flag2))
							end
					fun validater (x) =
						let
							val (plst,nplst,flag) = lister(x)
							val cmmn = Set.intersection(plst,nplst)
						in (flag orelse (not (cmmn = [])))
						end
				in validater(f)
				end
		in tmpValid(f')
		end
	fun isValidDNF(f)=
		let
			val f' = NormalForms.toDNF(Form.Negation(f))
			fun tmpInValid (Form.Disjunction(A,B)) = (tmpInValid(A) andalso tmpInValid(B))
			| tmpInValid (Form.Absurdum) = true
			| tmpInValid (Form.propSymb c) = false
			| tmpInValid (Form.Negation(Form.Absurdum)) = false
			| tmpInValid (Form.Negation(Form.propSymb c)) = false
			| tmpInValid (f) = 
				let 
					fun lister (Form.Absurdum) = ([],[],true)
						| lister (Form.propSymb c) = (Set.makeSet([c]),[],true)
						| lister (Form.Negation(Form.Absurdum)) = ([],[],false)
						| lister (Form.Negation(Form.propSymb c)) = ([],Set.makeSet([c]),true)
						| lister (Form.Conjunction(A',B')) =
							let
								val (plst1,nplst1,flag1) = lister(A')
								val (plst2,nplst2,flag2) = lister(B')
							in ( Set.union(plst1,plst2) , Set.union(nplst1,nplst2) , (flag1 orelse flag2))
							end
					fun validater (x) =
						let
							val (plst,nplst,flag) = lister(x)
							val cmmn = Set.intersection(plst,nplst)
						in (flag orelse (not (cmmn = [])))
						end
				in validater(f)
				end
		in tmpInValid(f')
		end
end;
