use "Set.sml";
signature FORM = sig
	datatype token =
		LogicalAbsurdum | Identifier of string | LogicalNot |
		LogicalAnd | LogicalOr | LogicalImplies | LParen | RParen |
		LogicalExistential | LogicalUniversal | Dot | Comma | Slash |
		LBracket | RBracket | Turnstile | Space | Colon | Newline | Htab
	exception LexicalError
	val tokenize : char list -> token list
	val tokenizer : string -> token list
	datatype vrbl = Vrbl of string
	datatype form =
		Absurdum | Negation of form |
		Conjunction of form*form | Disjunction of form*form |
		Implication of form*form | Predicate of string*vrbl Set.myset |
		Existential of vrbl*form | Universal of vrbl*form | Substitution of form*vrbl*vrbl
	exception SyntaxError of string
	val parse : string -> form
	val parse_tklst : token list -> form*token list
	val format : form -> string
	val getBoundVariables : form -> vrbl list
	val getFreeVariables : form -> vrbl list
end
structure Form :> FORM = struct
	datatype token =
		LogicalAbsurdum | Identifier of string | LogicalNot |
		LogicalAnd | LogicalOr | LogicalImplies | LParen | RParen |
		LogicalExistential | LogicalUniversal | Dot | Comma | Slash |
		LBracket | RBracket | Turnstile | Space | Colon | Newline | Htab
	exception LexicalError
	fun tokenize [] = []
		| tokenize ( #"-" :: #">" :: cs) = (LogicalImplies :: tokenize(cs))
		| tokenize ( #"-" :: c :: cs) = raise LexicalError
		| tokenize ( #"&" :: #"&" :: cs) = (LogicalAnd :: tokenize(cs))
		| tokenize ( #"*" :: #"$" :: cs) = (LogicalUniversal :: tokenize(cs))
		| tokenize ( #"$" :: #"$" :: cs) = (LogicalExistential :: tokenize(cs))
		| tokenize ( #"&" :: c :: cs) = raise LexicalError
		| tokenize ( #"|" :: #"|" :: cs) = (LogicalOr :: tokenize(cs))
		| tokenize ( #"|" :: #"-" ::cs ) = (Turnstile :: tokenize(cs))
		| tokenize ( #"|" :: c :: cs) = raise LexicalError
		| tokenize ( #"!" :: cs) = (LogicalNot :: tokenize(cs))
		| tokenize ( #"_" :: cs) = (LogicalAbsurdum :: tokenize(cs))
		| tokenize ( #"." :: cs) = (Dot :: tokenize(cs))
		| tokenize ( #"(" :: cs) = (LParen :: tokenize(cs))
		| tokenize ( #")" :: cs) = (RParen :: tokenize(cs))
		| tokenize ( #"/" :: cs) = (Slash :: tokenize(cs))
		| tokenize ( #"[" :: cs) = (LBracket :: tokenize(cs))
		| tokenize ( #"]" :: cs) = (RBracket :: tokenize(cs))
		| tokenize ( #"," :: cs) = (Comma :: tokenize(cs))
		| tokenize ( #" " :: cs) = (Space :: tokenize(cs))
		| tokenize ( #"\n" :: cs) = (Newline :: tokenize(cs))
		| tokenize ( #"\t" :: cs) = (Htab :: tokenize(cs))
		| tokenize ( #":" :: cs) = (Colon :: tokenize(cs))
		| tokenize (c :: cs) = 
			let
				fun getcharlist [] = []
					| getcharlist ( #"-" :: #">" :: xs) = []
					| getcharlist ( #"-" :: x :: xs) = []
					| getcharlist ( #"&" :: #"&" :: xs) = []
					| getcharlist ( #"*" :: #"$" :: xs) = []
					| getcharlist ( #"$" :: #"$" :: xs) = []
					| getcharlist ( #"&" :: x :: xs) = []
					| getcharlist ( #"|" :: #"|" :: xs) = []
					| getcharlist ( #"|" :: x :: xs) = []
					| getcharlist ( #"!" :: xs) = []
					| getcharlist ( #"_" :: xs) = []
					| getcharlist ( #"." :: xs) = []
					| getcharlist ( #"(" :: xs) = []
					| getcharlist ( #")" :: xs) = []
					| getcharlist ( #"," :: xs) = []
					| getcharlist ( #"/" :: cs) = []
					| getcharlist ( #"[" :: cs) = []
					| getcharlist ( #"]" :: cs) = []
					| getcharlist ( #"|" :: #"-" ::cs ) = []
					| getcharlist ( #" " :: cs) = []
					| getcharlist ( #"\t" :: cs) = []
					| getcharlist ( #"\n" :: cs) = []
					| getcharlist ( #":" :: cs) = []
					| getcharlist (x :: xs) = x::getcharlist(xs)
				fun getrempart [] = []
					| getrempart ( #"-" :: #">" :: xs) = ( #"-" :: #">" :: xs)
					| getrempart ( #"-" :: x :: xs) = ( #"-" :: x :: xs)
					| getrempart ( #"&" :: #"&" :: xs) = ( #"&" :: #"&" :: xs)
					| getrempart ( #"*" :: #"$" :: xs) = ( #"*" :: #"$" :: xs)
					| getrempart ( #"$" :: #"$" :: xs) = ( #"$" :: #"$" :: xs)
					| getrempart ( #"&" :: x :: xs) = ( #"&" :: x :: xs)
					| getrempart ( #"|" :: #"|" :: xs) = ( #"|" :: #"|" :: xs)
					| getrempart ( #"|" :: x :: xs) = ( #"|" :: x :: xs)
					| getrempart ( #"!" :: xs) = ( #"!" :: xs)
					| getrempart ( #"_" :: xs) = ( #"_" :: xs)
					| getrempart ( #"." :: xs) = ( #"." :: xs)
					| getrempart ( #"(" :: xs) = ( #"(" :: xs)
					| getrempart ( #")" :: xs) = ( #")" :: xs)
					| getrempart ( #"," :: xs) = ( #"," :: xs)
					| getrempart ( #"/" :: cs) = ( #"/" :: cs)
					| getrempart ( #"[" :: cs) = ( #"[" :: cs)
					| getrempart ( #"]" :: cs) = ( #"]" :: cs)
					| getrempart ( #"|" :: #"-" ::cs ) = ( #"|" :: #"-" ::cs )
					| getrempart ( #" " :: cs) = ( #" " :: cs)
					| getrempart ( #"\t" :: cs) = ( #"\t" :: cs)
					| getrempart ( #"\n" :: cs) = ( #"\n" :: cs)
					| getrempart ( #":" :: cs) = ( #":" :: cs)
					| getrempart (x :: xs) = getrempart(xs)
			in (Identifier(String.implode(getcharlist(c::cs)))::tokenize(getrempart(c::cs)))
			end	
	fun tokenizer s = tokenize(String.explode(s))
	datatype vrbl = Vrbl of string
	datatype form =
		Absurdum | Negation of form |
		Conjunction of form*form | Disjunction of form*form |
		Implication of form*form | Predicate of string*vrbl Set.myset |
		Existential of vrbl*form | Universal of vrbl*form | Substitution of form*vrbl*vrbl
	exception SyntaxError of string
	fun parse_imp fm = 
		let
			val ( f , fm') = parse_or fm
		in
			case fm'
				of (LogicalImplies :: fm'') =>
					let
						val ( f' , fm''') = parse_imp fm''
					in
						(Implication ( f , f') , fm''')
					end
				| _ => (f, fm')
		end
	and parse_or fm = 
		let
			val ( f , fm') = parse_and fm
		in
			case fm'
				of (LogicalOr :: fm'') =>
					let
						val ( f' , fm''') = parse_or fm''
					in
						(Disjunction ( f , f') , fm''')   
					end
				| _ => (f, fm')
		end
	and parse_and fm = 
		let
			val ( f , fm') = parse_substitution fm
		in
			case fm'
				of (LogicalAnd :: fm'') =>
					let
						val ( f' , fm''') = parse_and fm''
					in
						(Conjunction ( f , f') , fm''')
					end
				| _ => (f, fm')
		end
	and parse_substitution fm = 
		let
			val (f , fm') = parse_atom fm
			fun getSubsList (Identifier(f')::Slash::Identifier(f'')::RBracket::fm'') = [(Vrbl(f'),Vrbl(f''))]
				| getSubsList (Identifier(f')::Slash::Identifier(f'')::Comma::fm'') = (Vrbl(f'),Vrbl(f''))::getSubsList(fm'')
				| getSubsList (_) = raise SyntaxError "Wierd Substitution"
			fun getRemList (Identifier(f')::Slash::Identifier(f'')::RBracket::fm'') = fm''
				| getRemList (Identifier(f')::Slash::Identifier(f'')::Comma::fm'') = getRemList(fm'')
				| getRemList (_) = raise SyntaxError "Wierd Substitution"
			fun doSubstitute(f,[]) = f      (* Single Bracket multi variable *)
				| doSubstitute(f,(f',f'')::rem) = doSubstitute(Substitution(f,f',f''),rem)
			fun multiSubstitute(f,fm') =     (* Multi Bracket multi variable *)
				let
					val fm'' = getRemList(fm')
					val fm''' = getSubsList(fm')
				in
					case fm''
						of LBracket::x => multiSubstitute(doSubstitute(f,fm'''),x)
						| (_) => (doSubstitute(f,fm'''),fm'')
				end
		in
			case fm'
				of (LBracket::fm'') => (multiSubstitute(f,fm''))
				| (_) => (f,fm')
		end
	and parse_atom nil = raise SyntaxError ("Factor Expected \n")
		| parse_atom (LogicalNot :: fm) = 
			let
				val ( f , fm') = parse_atom fm
			in
				(Negation f , fm')
			end
		| parse_atom (LogicalUniversal::fm) =
			let
				fun applyUniversal(x,y) = 
					let
						val ( f , fm' ) = parse_imp(x)
					in (Universal(y,f),fm')
					end
			in
				case fm
					of Identifier(x)::Dot::xs => applyUniversal(xs,Vrbl(x))
					| (_) => raise SyntaxError "Unable to quantify "
			end
		| parse_atom (LogicalExistential::fm) =
			let
				fun applyExistential(x,y) = 
					let
						val ( f , fm' ) = parse_imp(x)
					in (Existential(y,f),fm')
					end
			in
				case fm
					of Identifier(x)::Dot::xs => applyExistential(xs,Vrbl(x))
					| (_) => raise SyntaxError "Unable to quantify "
			end
		| parse_atom ((Identifier f) :: fm) = 
			let
				fun getVarList (RParen :: xs) = []
					| getVarList (Identifier(f) :: RParen :: xs) = [Vrbl(f)]
					| getVarList (Identifier(f) :: Comma :: xs) = Vrbl(f) :: getVarList(xs)
					| getVarList (_) = raise SyntaxError " RParen or Variable Expected"
				fun getRemPart (RParen :: xs) = xs
					| getRemPart (Identifier(f) :: RParen :: xs) = xs
					| getRemPart (Identifier(f) :: Comma :: xs) = getRemPart(xs)
					| getRemPart (_) = raise SyntaxError " RParen or Variable Expected"
			in
				case fm
					of (LParen :: fm') => (Predicate(f,getVarList(fm')),getRemPart(fm'))
					| _ => (Predicate(f,[]),fm)
			end
		| parse_atom (LogicalAbsurdum :: fm) = (Absurdum , fm)
		| parse_atom (LParen :: fm) =
			let
				val ( f , fm') = parse_imp fm
			in
				case fm'
					of nil => raise SyntaxError ("Right Parenthesis Expected .\n")
					| (RParen :: fm'') => ( f , fm'')
					| _ => raise SyntaxError ("Right Parenthesis Expected .\n")
			end
	fun parse_tklst x = parse_imp(x)
	fun parse s =
		let
			val ( f , fm) = parse_imp (tokenize (String.explode s))
		in
			case fm
				of nil => f
				| _ => raise SyntaxError ("Unexpected Input .\n")
		end
		handle LexicalError => raise SyntaxError ("Invalid Input .\n")
	fun format_exp Absurdum = [#"_"]
		| format_exp (Predicate(P,lst)) = 
			let
				fun printlst ([]) = []
					| printlst ([Vrbl(x)]) = String.explode(x)
					| printlst (Vrbl(y)::z) = (String.explode(y)@[#","]@printlst(z))
				val plst=printlst(lst)
			in
				case plst
					of nil => (String.explode(P))
					| x => (String.explode(P) @ [#"("] @ x @ [#")"])
			end
		| format_exp (Negation A) = 
			let
				val s = format_exp A
			in ([#"("] @ [#"!"] @ s @ [#")"])
			end
		| format_exp (Conjunction (A,B)) = 
			let
				val n = format_exp A
				val n' = format_exp B
			in [#"("] @ n @ [#"&"] @ [#"&"] @ n' @ [#")"]
			end
		| format_exp (Disjunction (A,B)) = 
			let
				val n = format_exp A
				val n' = format_exp B
			in ([#"("] @ n @ [#"|"] @ [#"|"] @ n' @ [#")"])
			end
		| format_exp (Implication (A,B)) = 
			let
				val n = format_exp A
				val n' = format_exp B
			in ([#"("] @ n @ [#"-"] @ [#">"] @ n' @ [#")"])
			end
		| format_exp (Substitution(x,Vrbl(y),Vrbl(z))) = (format_exp(x) @ [#"["] @ String.explode(y) @ [#"/"] @ String.explode(z) @ [#"]"] )
		| format_exp (Universal(Vrbl(x),y)) = ([#"*"] @ [#"$"] @ String.explode(x) @ [#"."] @ format_exp(y))
		| format_exp (Existential(Vrbl(x),y)) = ([#"$"] @ [#"$"] @ String.explode(x) @ [#"."] @ format_exp(y))
	fun getBoundVariables (Predicate(nm,vrlst)) = []
		| getBoundVariables (Negation(f1)) = getBoundVariables(f1)
		| getBoundVariables (Conjunction(f1,f2)) = Set.union(getBoundVariables(f1),getBoundVariables(f2))
		| getBoundVariables (Disjunction(f1,f2)) = Set.union(getBoundVariables(f1),getBoundVariables(f2))
		| getBoundVariables (Implication(f1,f2)) = Set.union(getBoundVariables(f1),getBoundVariables(f2))
		| getBoundVariables (Existential(vr,f2)) = Set.union([vr],getBoundVariables(f2))
		| getBoundVariables (Universal(vr,f2)) = Set.union([vr],getBoundVariables(f2))
		| getBoundVariables (Substitution(f1,vr1,vr2)) = getBoundVariables(f1)
	fun getFreeVariables (Predicate(nm,vrlst)) = vrlst
		| getFreeVariables (Negation(f1)) = getFreeVariables(f1)
		| getFreeVariables (Conjunction(f1,f2)) = Set.union(getFreeVariables(f1),getFreeVariables(f2))
		| getFreeVariables (Disjunction(f1,f2)) = Set.union(getFreeVariables(f1),getFreeVariables(f2))
		| getFreeVariables (Implication(f1,f2)) = Set.union(getFreeVariables(f1),getFreeVariables(f2))
		| getFreeVariables (Existential(vr,f2)) = Set.diff(getFreeVariables(f2),[vr])
		| getFreeVariables (Universal(vr,f2)) = Set.diff(getFreeVariables(f2),[vr])
		| getFreeVariables (Substitution(f1,vr1,vr2)) = Set.union(Set.union(getFreeVariables(f1),[vr1]),[vr2])
	fun format f = String.implode (format_exp f)
end;
