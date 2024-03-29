signature GENTZENSYSTEM = sig
	datatype sequentNode = sNode of Form.form list * Form.form
	datatype sequentTree = sTree of sequentNode | sTree1 of sequentNode*sequentTree | sTree2 of sequentNode*sequentTree*sequentTree
	exception TreeException of string
	val parse_node : Form.token list -> sequentNode * Form.token list
	val fetchInput : string -> Form.token list
	val parse_sequentTree : string -> sequentTree
	val getFreevars : Form.form list -> Form.vrbl list
	val getBoundvars : Form.form list -> Form.vrbl list
	val getPrednames : Form.form list -> string list
	val getNames : sequentNode -> string list
	val getAllNames : sequentTree -> string list
	val getPropositions : Form.form list -> Form.form list
	val getAllPropositions : sequentTree -> Form.form list
	val belongsNW : Form.form*Form.form list -> bool
	val deleteElem : Form.form*Form.form list -> Form.form list
	val diffnew : Form.form list*Form.form list -> Form.form list
	val eqNew : Form.form list * Form.form list -> bool
	val isAxiom : sequentNode -> bool
	val isAbsurdelim : sequentNode*sequentNode -> bool
	val isImplrt : sequentNode*sequentNode -> bool
	val isContraclt : sequentNode*sequentNode -> bool
	val isConjlt : sequentNode*sequentNode -> bool
	val isDisjuncrt : sequentNode*sequentNode -> bool
	val isUnirt : sequentNode*sequentNode -> bool
	val isUnilt : sequentNode*sequentNode -> bool
	val isExistlt : sequentNode*sequentNode -> bool
	val isExistrt : sequentNode*sequentNode -> bool
	val isConjrt : sequentNode*sequentNode*sequentNode -> bool
	val isCut : sequentNode*sequentNode*sequentNode -> bool
	val isDisjunclt : sequentNode*sequentNode*sequentNode -> bool
	val isImpllt : sequentNode*sequentNode*sequentNode -> bool
	val getRoot : sequentTree -> sequentNode
	val isValidTree : sequentTree ->bool
end
structure GentzenSystem :> GENTZENSYSTEM = struct
	datatype sequentNode = sNode of Form.form list * Form.form
	datatype sequentTree = sTree of sequentNode | sTree1 of sequentNode*sequentTree | sTree2 of sequentNode*sequentTree*sequentTree
	exception TreeException of string
	fun parse_node (Form.Turnstile::xs) = 
			let
				val (f,lst) = Form.parse_tklst(xs)
			in (sNode([],f),lst)
			end
		| parse_node (rem) = 
			let
				val (f,lst) = Form.parse_tklst(rem)
			in 
				case lst
					of Form.Turnstile::xs => 
						let
							val (sNode(lst1,f'),lst') = parse_node(lst)
						in (sNode(f::lst1,f'),lst')
						end
					| Form.Comma::ys => 
						let
							val (sNode(lst1,f'),lst') = parse_node(ys)
						in (sNode(f::lst1,f'),lst')
						end
					| (t) => raise Form.SyntaxError "Comma or Turnstile Expected"
			end
	fun fetchInput x = 
		let
			val instream = TextIO.openIn(x)
			val tklst = Form.tokenize(String.explode(TextIO.inputAll(instream)))
		in TextIO.closeIn(instream);tklst
		end
	fun parse_sequentTree(str) =
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
							of [] => (sTree(nd),[]) 
							| [Form.Newline] => (sTree(nd),[])
							| Form.Newline:: tklst'' => 
								( if(compareTabs(tklst'',#"\t"::lst') = "Equal" ) 
									then 
										(let val (trlst,remlst) = deductTrees(tklst'',#"\t"::lst') in case trlst of
										[x] => (sTree1(nd,x),remlst)
										| [x,y] => (sTree2(nd,x,y),remlst)
										| (f) => raise TreeException "More tree nodes" end)
								else if(compareTabs(tklst'',#"\t"::lst') = "More") 
									then raise TreeException "Wrongly Structured"
								else (sTree(nd),tklst'')
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
		| getPrednames(f::rem)=Set.union(Form.getPredNames(f),getPrednames(rem))
	fun getFreevars([]) = []
		| getFreevars(f::rem)=Set.union(Form.getFreeVariables(f),getFreevars(rem))
	fun getBoundvars([]) = []
		| getBoundvars(f::rem)=Set.union(Form.getBoundVariables(f),getBoundvars(rem))
	fun getNames(sNode(ls,f)) = Set.union(Form.getVarnames(Set.union(getBoundvars(ls),getFreevars(ls))),getPrednames(ls))
	fun getAllNames (sTree(nd)) = getNames(nd)
		| getAllNames (sTree1(nd,tr1)) = Set.union(getNames(nd),getAllNames(tr1))
		| getAllNames (sTree2(nd,tr1,tr2)) = Set.union(getNames(nd),Set.union(getAllNames(tr1),getAllNames(tr2)))
	fun getPropositions ([]) = []
		| getPropositions (x::xs) = Set.union([x],getPropositions(xs))
	fun getAllPropositions (sTree(sNode(ls,f))) = getPropositions(ls)
		| getAllPropositions (sTree1(sNode(ls,f),tr1)) = Set.union(getPropositions(ls),getAllPropositions(tr1))
		| getAllPropositions (sTree2(sNode(ls,f),tr1,tr2)) = Set.union(getPropositions(ls),Set.union(getAllPropositions(tr1),getAllPropositions(tr2)))
	fun belongsNW(x,[]) = false
		| belongsNW(x,y::ys) = if (x=y) then true else belongsNW(x,ys)
	fun deleteElem(x,[]) = []
		| deleteElem(x,y::ys) = if (x=y) then ys else y::deleteElem(x,ys)
	fun eqNew([],[]) = true
		| eqNew(x,[]) = false
		| eqNew([],y) = false
		| eqNew(x::xs,y::ys) = if(x=y) then eqNew(xs,ys) else false
	fun diffnew([],x) = []
		| diffnew(x::xs,y) = if (belongsNW(x,y)) then diffnew(xs,deleteElem(x,y)) else x::diffnew(xs,y)
	fun isAxiom(sNode(lst1,f1)) = belongsNW(f1,lst1)
	fun isAbsurdelim(sNode(lst1,f1),sNode(lst2,f2)) = 
		let
			val flg = Set.equals(lst1,lst2) andalso (f1=Form.Absurdum) andalso not(f2=Form.Absurdum)
		in flg
		end
	fun isContraclt(sNode(lst1,f1),sNode(lst2,f2)) =
		let
			val df=diffnew(lst1,lst2)
		in case df
			of ([x]) => if (belongsNW(x,lst2)) then true else false
			| (x) => false
		end
	fun isImplrt(sNode(lst1,f1),sNode(lst2,f2)) =
		let
			val lst3 = diffnew(lst1,lst2)
		in case (lst3,f2)
			of ([x],Form.Implication(z,t)) => if (x=z andalso t=f1) then true else false
			| (x,z) => false
		end
	fun isImpllt(sNode(lst1,f1),sNode(lst2,f2),sNode(lst3,f3)) =
		let
			val df1 = diffnew(lst1,lst3)
			val df2 = diffnew(lst2,lst3)
			val df3 = Set.union(diffnew(lst3,lst1),diffnew(lst3,lst2))
		in case (df1,df2,df3)
			of ([],[x],[Form.Implication(y,z)]) => if (x=y andalso z=f1 andalso f2=f3) then true else false
			| ([x],[],[Form.Implication(y,z)]) => if (x=y andalso z=f2 andalso f1=f3) then true else false
			| (x,y,z) => false
		end
	fun isCut(sNode(lst1,f1),sNode(lst2,f2),sNode(lst3,f3)) =
		let
			val df1 = diffnew(lst1,lst3)
			val df2 = diffnew(lst2,lst3)
			val df3 = Set.union(diffnew(lst3,lst1),diffnew(lst3,lst2))
		in case (df1,df2,df3)
			of ([],[x],[]) => if (x=f1 andalso f2=f3) then true else false
			| (x,y,z) => false
		end
	fun isConjrt(sNode(lst1,f1),sNode(lst2,f2),sNode(lst3,f3)) =
		let
			val truthVal = (eqNew(lst1,lst2) andalso eqNew(lst2,lst3) andalso eqNew(lst1,lst3))
		in case (f3,truthVal)
			of (Form.Conjunction(x,y),true) => if (x=f1 andalso y=f2 ) then true else if
																	(x=f2 andalso y=f1 ) then true else false
			| (x,y) => false
		end
	fun isConjlt(sNode(lst1,f1),sNode(lst2,f2)) =
		let
			val df1 = diffnew(lst1,lst2)
			val df2 = diffnew(lst2,lst1)
		in case (df1,df2)
			of ([a,b],[Form.Conjunction(x,y)]) => if (x=a andalso y=b andalso f1=f2) then true else if
														(x=b andalso y=a andalso f1=f2 ) then true else false
			| (x,y) => false
		end
	fun isDisjunclt(sNode(lst1,f1),sNode(lst2,f2),sNode(lst3,f3)) =
		let
			val truthVal = (f1=f2 andalso f2=f3)
			val df1 = diffnew(lst1,lst3)
			val df2 = diffnew(lst2,lst3)
			val df3 = Set.union(diffnew(lst3,lst1),diffnew(lst3,lst2))
		in case (df1,df2,df3,truthVal)
			of ([a],[b],[Form.Disjunction(x,y)],true) => if (x=a andalso y=b) then true else if
														(x=b andalso y=a) then true else false
			| (x,y,z,t) => false
		end
	fun isDisjuncrt(sNode(lst1,f1),sNode(lst2,f2)) =
		let
			val truthVal = (eqNew(lst1,lst2))
		in case (f2,truthVal)
			of (Form.Disjunction(x,y),true) => if (x=f1 orelse y=f1) then true else false
			| (x,y) => false
		end
	fun isUnilt(sNode(lst1,f1),sNode(lst2,f2)) =
		let
			val truthVal = (f1=f2)
			val df1 = diffnew(lst1,lst2)
			val df2 = diffnew(lst2,lst1)
		in case (df1,df2,truthVal)
			of ([Form.Substitution(p,r,s)],[Form.Universal(x,y)],true) => if (x=s andalso y=p) then true else false
			| (x,y,z) => false
		end
	fun isUnirt(sNode(lst1,f1),sNode(lst2,f2)) =
		let
			val truthVal = (eqNew(lst1,lst2))
		in case (f2,truthVal,f1)
			of (Form.Universal(x,y),true,Form.Substitution(p,r,s)) => if (x=s andalso y=p andalso (Set.diff([r],Set.union(getFreevars(lst1),Form.getFreeVariables(p))))=[r]) then true else false
			| (x,y,z) => false
		end
	fun isExistlt(sNode(lst1,f1),sNode(lst2,f2)) =
		let
			val truthVal = (f1=f2)
			val df1 = diffnew(lst1,lst2)
			val df2 = diffnew(lst2,lst1)
		in case (df1,df2,truthVal)
			of ([Form.Substitution(p,r,s)],[Form.Existential(x,y)],true) => if (x=s andalso y=p andalso (Set.diff([r],Set.union(getFreevars(lst1),Form.getFreeVariables(p))))=[r]) then true else false
			| (x,y,z) => false
		end
	fun isExistrt(sNode(lst1,f1),sNode(lst2,f2)) =
		let
			val truthVal = (eqNew(lst1,lst2))
		in case (f2,truthVal,f1)
			of (Form.Existential(x,y),true,Form.Substitution(p,r,s)) => if (x=s andalso y=p) then true else false
			| (x,y,z) => false
		end
	fun getRoot(sTree(nd)) = nd
		| getRoot(sTree1(nd,tr1)) = nd
		| getRoot(sTree2(nd,tr1,tr2)) = nd
	fun isValidTree(dt) = 
		let
			val inf1 = [isAxiom]
			val inf2 = [isAbsurdelim,isImplrt,isContraclt,isConjlt,isDisjuncrt,isUnirt,isUnilt,isExistlt,isExistrt]
			val inf3 = [isConjrt,isCut,isDisjunclt,isImpllt]
			fun applier([],nds) = false
				| applier(x::xs,nds) = if(x(nds)) then true else applier(xs,nds)
		in case dt
			of sTree(nd) => applier(inf1,nd)
			| sTree1(nd,tr1) => applier(inf2,(getRoot(tr1),nd)) andalso isValidTree(tr1)
			| sTree2(nd,tr1,tr2) => applier(inf3,(getRoot(tr1),getRoot(tr2),nd)) andalso isValidTree(tr1) andalso isValidTree(tr2)
			| f => false
		end
end;
