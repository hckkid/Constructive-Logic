use "Form.sml";
signature NATURALDEDUCTION = sig
	datatype packet = Packet of Form.vrbl*Form.form
	datatype deductionNode = dNode of packet list * Form.form
	datatype deductionTree = dTree of deductionNode | dTree1 of deductionNode*deductionTree | dTree2 of deductionNode*deductionTree*deductionTree | dTree3 of deductionNode*deductionTree*deductionTree*deductionTree
	val parse_deductionTree : string -> deductionTree
	exception TreeException of string
	val parse_node : Form.token list -> deductionNode * Form.token list
	val fetchInput : string -> Form.token list
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
end;
