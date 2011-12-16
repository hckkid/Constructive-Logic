signature NATURALDEDUCTION = sig
	datatype packet = Packet of Form.vrbl*Form.form
	datatype deductionNode = dNode of packet list * Form.form
	datatype deductionTree = dTree of deductionNode | dTree1 of deductionNode*deductionTree | dTree2 of deductionNode*deductionTree*deductionTree | dTree3 of deductionNode*deductionTree*deductionTree*deductionTree
	exception TreeException of string
	val parse_node : Form.token list -> deductionNode * Form.token list
	val fetchInput : string -> Form.token list
	val parse_deductionTree : string -> deductionTree
	val getPrednames : packet list -> string list
	val getFreevars : packet list -> Form.vrbl list
	val getBoundvars : packet list -> Form.vrbl list
	val getNames : deductionNode -> string list
	val getAllNames : deductionTree -> string list
	val isAxiom : deductionNode -> bool
	val isAbsurdelim : deductionNode*deductionNode -> bool
	val isImplintro : deductionNode*deductionNode -> bool
	val isImplelim : deductionNode*deductionNode*deductionNode -> bool
	val isConjintro : deductionNode*deductionNode*deductionNode -> bool
	val isConjelimlt : deductionNode*deductionNode -> bool
	val isConjelimrt : deductionNode*deductionNode -> bool
	val isDisjuncintrolt : deductionNode*deductionNode -> bool
	val isDisjuncintrort : deductionNode*deductionNode -> bool
	val isDisjuncelim : deductionNode*deductionNode*deductionNode*deductionNode -> bool
	val isUniintro : deductionNode*deductionNode -> bool
	val isUnielim : deductionNode*deductionNode -> bool
	val isExistentialintro : deductionNode*deductionNode -> bool
	val isExistentialelim : deductionNode*deductionNode*deductionNode -> bool
	val getRoot : deductionTree -> deductionNode
	val isValidTree : deductionTree ->bool
end
structure NaturalDeduction :> NATURALDEDUCTION = struct
	datatype packet = Packet of Form.vrbl*Form.form
	datatype deductionNode = dNode of packet list * Form.form
	datatype deductionTree = dTree of deductionNode | dTree1 of deductionNode*deductionTree | dTree2 of deductionNode*deductionTree*deductionTree | dTree3 of deductionNode*deductionTree*deductionTree*deductionTree
	exception TreeException of string
	fun parse_node (Form.Turnstile::xs) = 
			let
				val (f,lst) = Form.parse_tklst(xs)
			in (dNode([],f),lst)
			end
		| parse_node (Form.Identifier(x)::Form.Colon::rem) = 
			let
				val (f,lst) = Form.parse_tklst(rem)
			in 
				case lst
					of Form.Turnstile::xs => 
						let
							val (dNode(lst1,f'),lst') = parse_node(lst)
						in (dNode(Packet(Form.Vrbl(x),f)::lst1,f'),lst')
						end
					| Form.Comma::Form.Identifier(y)::ys	 => 
						let
							val (dNode(lst1,f'),lst') = parse_node(Form.Identifier(y)::ys)
						in (dNode(Packet(Form.Vrbl(x),f)::lst1,f'),lst')
						end
					| (t) => raise Form.SyntaxError "Comma or Turnstile Expected"
			end
		| parse_node (f) = raise Form.SyntaxError "Not A Deduction Node"
	fun fetchInput x = 
		let
			val instream = TextIO.openIn(x)
			val tklst = Form.tokenize(String.explode(TextIO.inputAll(instream)))
		in TextIO.closeIn(instream);tklst
		end
	fun parse_deductionTree(str) =
		let
			fun fetchNode(Form.Htab::x,[]) = raise TreeException "Can't fetch Node"
				| fetchNode(Form.Htab::x,y::ys) = fetchNode(x,ys)
				| fetchNode(x,y::ys) = raise TreeException "Can't fetch node"
				| fetchNode(x,[]) = parse_node(x)
			fun compareTabs(Form.Htab::x,[]) = "More"
				| compareTabs(Form.Htab::x,y::ys) = compareTabs(x,ys)
				| compareTabs(x,y::ys) = "Less"
				| compareTabs(x,[]) = "Equal"
			fun deductTree(tklst,lst') = 
				if (compareTabs(tklst,lst') = "Equal" ) 
					then ( let val (nd,tklst')=fetchNode(tklst,lst') in
						case tklst' 
							of [] => (dTree(nd),[]) 
							| [Form.Newline] => (dTree(nd),[])
							| Form.Newline:: tklst'' => 
								( if(compareTabs(tklst'',#"\t"::lst') = "Equal" ) 
									then 
										(let val (trlst,remlst) = deductTrees(tklst'',#"\t"::lst') in case trlst of
										[x] => (dTree1(nd,x),remlst)
										| [x,y] => (dTree2(nd,x,y),remlst)
										| [x,y,z] => (dTree3(nd,x,y,z),remlst) 
										| (f) => raise TreeException "More tree nodes" end)
								else if(compareTabs(tklst'',#"\t"::lst') = "More") 
									then raise TreeException "Wrongly Structured"
								else (dTree(nd),tklst'')
								)
						| (t) => raise TreeException "Wrong Format" 
						end
					)
				else raise TreeException "Size mismatch"
			and deductTrees(tklst,lst') = 
				if (compareTabs(tklst,lst') = "Equal" ) 
					then ( let val (dt,tklst')=deductTree(tklst,lst') in
						if (tklst' = [] ) then ([dt],[])
						else ( if(compareTabs(tklst',lst') = "Equal" )
							then 
								( let val (trlst,tklst'') = deductTrees(tklst',lst')
								in (dt::trlst,tklst'')
								end )
							else if(compareTabs(tklst',lst') = "More") 
								then raise TreeException "Wrongly Structured"
							else ([dt],tklst')
							) end 
					)
				else raise TreeException "Size mismatch"
			fun getTreeFromtuple(x) =
				let
					val (p,q) = x
				in p
				end
		in getTreeFromtuple(deductTree(fetchInput(str),[]))
		end
	fun getPrednames([]) = []
		| getPrednames(Packet(vr,f)::rem)=Set.union(Form.getPredNames(f),getPrednames(rem))
	fun getFreevars([]) = []
		| getFreevars(Packet(vr,f)::rem)=Set.union(vr::Form.getFreeVariables(f),getFreevars(rem))
	fun getBoundvars([]) = []
		| getBoundvars(Packet(vr,f)::rem)=Set.union(Form.getBoundVariables(f),getBoundvars(rem))
	fun getNames(dNode(ls,f)) = Set.union(Form.getVarnames(Set.union(getBoundvars(ls),getFreevars(ls))),getPrednames(ls))
	fun getAllNames (dTree(nd)) = getNames(nd)
		| getAllNames (dTree1(nd,tr1)) = Set.union(getNames(nd),getAllNames(tr1))
		| getAllNames (dTree2(nd,tr1,tr2)) = Set.union(getNames(nd),Set.union(getAllNames(tr1),getAllNames(tr2)))
		| getAllNames (dTree3(nd,tr1,tr2,tr3)) = Set.union(getNames(nd),Set.union(getAllNames(tr1),Set.union(getAllNames(tr2),getAllNames(tr3))))
	fun isAxiom(dNode(lst1,f1)) =
		let
			fun belongsNew([],f) = false
				| belongsNew(Packet(x,f1)::xs,f) = true
				| belongsNew(y::ys,f) = belongsNew(ys,f)
		in belongsNew(lst1,f1)
		end
	fun isAbsurdelim(dNode(lst1,f1),dNode(lst2,f2)) = 
		let
			val flg = Set.equals(lst1,lst2) andalso (f1=Form.Absurdum) andalso not(f2=Form.Absurdum)
		in flg
		end
	fun isImplintro(dNode(lst1,f1),dNode(lst2,f2)) =
		let
			val lst3 = Set.diff(lst1,lst2)
		in case (lst3,f2)
			of ([Packet(x,y)],Form.Implication(z,t)) => if (y=z andalso t=f1) then true else false
			| (x,z) => false
		end
	fun isConjintro(dNode(lst1,f1),dNode(lst2,f2),dNode(lst3,f3)) =
		let
			val truthVal = (Set.equals(lst1,lst2) andalso Set.equals(lst2,lst3) andalso Set.equals(lst1,lst3))
		in case (f3,truthVal)
			of (Form.Conjunction(x,y),true) => if (x=f1 andalso y=f2 ) then true else if
																	(x=f2 andalso y=f1 ) then true else false
			| (x,y) => false
		end
	fun isConjelimlt(dNode(lst1,f1),dNode(lst2,f2)) =
		let
			val truthVal = (Set.equals(lst1,lst2))
		in case (f1,truthVal)
			of (Form.Conjunction(x,y),true) => if (x=f2) then true else false
			| (x,y) => false
		end
	fun isConjelimrt(dNode(lst1,f1),dNode(lst2,f2)) =
		let
			val truthVal = (Set.equals(lst1,lst2))
		in case (f1,truthVal)
			of (Form.Conjunction(x,y),true) => if (y=f2) then true else false
			| (x,y) => false
		end
	fun isDisjuncintrolt(dNode(lst1,f1),dNode(lst2,f2)) =
		let
			val truthVal = (Set.equals(lst1,lst2))
		in case (f2,truthVal)
			of (Form.Disjunction(x,y),true) => if (x=f1) then true else false
			| (x,y) => false
		end
	fun isDisjuncintrort(dNode(lst1,f1),dNode(lst2,f2)) =
		let
			val truthVal = (Set.equals(lst1,lst2))
		in case (f2,truthVal)
			of (Form.Disjunction(x,y),true) => if (y=f1) then true else false
			| (x,y) => false
		end
	fun isImplelim(dNode(lst1,f1),dNode(lst2,f2),dNode(lst3,f3)) =
		let
			val truthVal = (Set.equals(lst1,lst2) andalso Set.equals(lst2,lst3) andalso Set.equals(lst1,lst3))
		in case (f1,f2,truthVal)
			of (Form.Implication(x,y),Form.Implication(z,t),true) => if (x=f2 andalso y=f3 ) then true else if
																	(z=f1 andalso t=f3 ) then true else false
			| (Form.Implication(x,y),z,true) => if (x=f2 andalso y=f3) then true else false
			| (z,Form.Implication(x,y),true) => if (x=f1 andalso y=f3) then true else false
			| (x,y,z) => false
		end
	fun isDisjuncelim(dNode(lst1,f1),dNode(lst2,f2),dNode(lst3,f3),dNode(lst4,f4)) =
		let
			val truthVal = if (Set.equals(lst1,lst4) andalso not(Set.equals(lst2,lst4) orelse Set.equals(lst3,lst4))) then Form.Identifier("1")
						 	else if (Set.equals(lst2,lst4) andalso not(Set.equals(lst1,lst4) orelse Set.equals(lst3,lst4))) then Form.Identifier("2")
							else if (Set.equals(lst3,lst4) andalso not(Set.equals(lst2,lst4) orelse Set.equals(lst1,lst4))) then Form.Identifier("3")
							else Form.Identifier("0")
			val dfl1 = Set.diff(lst1,lst4)
			val dfl2 = Set.diff(lst2,lst4)
			val dfl3 = Set.diff(lst3,lst4)
		in case (truthVal,dfl1,dfl2,dfl3)
			of (Form.Identifier("1"),[],[Packet(x,f1')],[Packet(y,f2')]) => if ((f1=Form.Disjunction(f1',f2') orelse f1=Form.Disjunction(f2',f1')) andalso (f2=f4) andalso (f3=f4)) then (print("Bingo");true) else false
			| (Form.Identifier("2"),[Packet(x,f1')],[],[Packet(y,f2')]) => if ((f2=Form.Disjunction(f1',f2') orelse f2=Form.Disjunction(f2',f1')) andalso (f1=f4) andalso (f3=f4)) then true else false
			| (Form.Identifier("3"),[Packet(x,f1')],[Packet(y,f2')],[]) => if ((f3=Form.Disjunction(f1',f2') orelse f3=Form.Disjunction(f2',f1')) andalso (f1=f4) andalso (f2=f4)) then true else false
			| (x,y,z,t) => false
		end
	fun isUniintro(dNode(lst1,f1),dNode(lst2,f2)) =
		let
			val truthVal = (Set.equals(lst1,lst2))
		in case (f2,truthVal,f1)
			of (Form.Universal(x,y),true,Form.Substitution(p,r,s)) => if (x=s andalso y=p andalso (Set.diff([r],Set.union(getFreevars(lst1),Form.getFreeVariables(p))))=[r]) then true else false
			| (x,y,z) => false
		end
	fun isUnielim(dNode(lst1,f1),dNode(lst2,f2)) =
		let
			val truthVal = (Set.equals(lst1,lst2))
		in case (f1,truthVal,f2)
			of (Form.Universal(x,y),true,Form.Substitution(p,r,s)) => if (x=s andalso y=p) then true else false
			| (x,y,z) => false
		end
	fun isExistentialintro(dNode(lst1,f1),dNode(lst2,f2)) =
		let
			val truthVal = (Set.equals(lst1,lst2))
		in case (f2,truthVal,f1)
			of (Form.Existential(x,y),true,Form.Substitution(p,r,s)) => if (x=s andalso y=p) then true else false
			| (x,y,z) => false
		end
	fun isExistentialelim(dNode(lst1,f1),dNode(lst2,f2),dNode(lst3,f3)) =
		let
			val truthVal = if (Set.equals(lst1,lst3) andalso not(Set.equals(lst2,lst3))) then Form.Identifier("1")
						 	else if (Set.equals(lst2,lst3) andalso not(Set.equals(lst1,lst3))) then Form.Identifier("2")
							else Form.Identifier("3")
			val df1 = Set.diff(lst1,lst3)
			val df2 = Set.diff(lst2,lst3)
		in case (truthVal,df1,df2,f1,f2)
			of (Form.Identifier("1"),[],[Packet(t,Form.Substitution(p,r,s))],Form.Existential(x,y),f) => if (x=s andalso y=p andalso (Set.diff([r],Set.union(getFreevars(lst1),Form.getFreeVariables(p)))=[r])) then true else false
			| (Form.Identifier("2"),[Packet(t,Form.Substitution(p,r,s))],[],f,Form.Existential(x,y)) => if (x=s andalso y=p andalso (Set.diff([r],Set.union(getFreevars(lst2),Form.getFreeVariables(p))))=[r]) then true else false
			| (p,q,r,s,t) => false
		end
	fun getRoot(dTree(nd)) = nd
		| getRoot(dTree1(nd,tr1)) = nd
		| getRoot(dTree2(nd,tr1,tr2)) = nd
		| getRoot(dTree3(nd,tr1,tr2,tr3)) = nd
	fun isValidTree(dt) = 
		let
			val inf1 = [isAxiom]
			val inf2 = [ isAbsurdelim , isImplintro , isConjelimlt , isConjelimrt , isDisjuncintrolt , isDisjuncintrort , isUniintro,isUnielim , isExistentialintro ]
			val inf3 = [isConjintro , isImplelim , isExistentialelim]
			val inf4 = [isDisjuncelim]
			fun applier([],nds) = false
				| applier(x::xs,nds) = if(x(nds)) then true else applier(xs,nds)
		in case dt
			of dTree(nd) => applier(inf1,nd)
			| dTree1(nd,tr1) => applier(inf2,(getRoot(tr1),nd)) andalso isValidTree(tr1)
			| dTree2(nd,tr1,tr2) => applier(inf3,(getRoot(tr1),getRoot(tr2),nd)) andalso isValidTree(tr1) andalso isValidTree(tr2)
			| dTree3(nd,tr1,tr2,tr3) => applier(inf4,(getRoot(tr1),getRoot(tr2),getRoot(tr3),nd)) andalso isValidTree(tr1) andalso isValidTree(tr2) andalso isValidTree(tr3)
			| f => false
		end
end;
