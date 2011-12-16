use "Form.sml";
use "NaturalDeduction.sml";
use "GentzenSystem.sml";
signature TRANSFORM = sig
	val transformSequent : NaturalDeduction.deductionTree -> GentzenSystem.sequentTree
	val doSubstitute : (Form.vrbl*Form.vrbl) list * NaturalDeduction.packet -> NaturalDeduction.packet
	val doSubstitution : (Form.vrbl*Form.vrbl) list * NaturalDeduction.packet list -> NaturalDeduction.packet list
	val tostring : string * char list -> string
	val nextName : string * char list * string list -> string
	val firstName : string * string list -> string
	val nameIt : Form.form list * Form.form list * string list * string -> (string * Form.form) list
(*	val transformDeduction : GentzenSystem.sequentTree -> NaturalDeduction.deductionTree *)
end
structure Transform :> TRANSFORM = struct
	datatype flags = flg1 | flg2 | flg3 | flg4 | flg5 | flg6 | flg7 | flg8 | flg9 | flg0
	exception ConversionError of string
	exception NameError of string
	fun eraseTags [] = []
		| eraseTags (NaturalDeduction.Packet(x,f)::rem) = f::eraseTags(rem)
	fun transformSequent (dt) = 
		let
			fun handler1(nd) = 
				let
					val NaturalDeduction.dNode(x,y) = nd
				in if (NaturalDeduction.isAxiom(nd)) then GentzenSystem.sTree(GentzenSystem.sNode(eraseTags(x),y)) else raise ConversionError ("Not an Axiom")
				end
			fun handler2(nd,tr1) = 
				let
					val NaturalDeduction.dNode(x1,y1) = nd
					val nd2=NaturalDeduction.getRoot(tr1)
					val NaturalDeduction.dNode(x2,y2) = nd2
					fun getflag(nd1',nd2') = 
						if (NaturalDeduction.isAbsurdelim(nd1',nd2')) then flg1 else 
						if (NaturalDeduction.isImplintro(nd1',nd2')) then flg1 else 
						if (NaturalDeduction.isConjelimlt(nd1',nd2')) then flg2 else 
						if (NaturalDeduction.isConjelimrt(nd1',nd2')) then flg2 else 
						if (NaturalDeduction.isDisjuncintrolt(nd1',nd2')) then flg1 else 
						if (NaturalDeduction.isDisjuncintrort(nd1',nd2')) then flg1 else 
						if (NaturalDeduction.isUniintro(nd1',nd2')) then flg1 else 
						if (NaturalDeduction.isUnielim(nd1',nd2')) then flg3 else 
						if (NaturalDeduction.isExistentialintro(nd1',nd2')) then flg1 else 
						flg0
				in case (getflag(nd2,nd),y1,y2)
					of (flg1,x,y) => GentzenSystem.sTree1(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr1))
					| (flg2,x,Form.Conjunction(y,z)) => GentzenSystem.sTree2(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr1) , GentzenSystem.sTree1(GentzenSystem.sNode(y2::eraseTags(x2),y1),GentzenSystem.sTree(GentzenSystem.sNode(y::z::eraseTags(x2),y1))))
					| (flg3,x,y) => GentzenSystem.sTree2(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr1) , GentzenSystem.sTree1(GentzenSystem.sNode(y2::eraseTags(x2),y1),GentzenSystem.sTree(GentzenSystem.sNode(y1::eraseTags(x2),y1))))
					| (f,x,y) => raise ConversionError "Tree Error"
				end 
			fun handler3(nd,tr1,tr2) = 
				let
					val NaturalDeduction.dNode(x1,y1) = nd
					val nd2=NaturalDeduction.getRoot(tr1)
					val NaturalDeduction.dNode(x2,y2) = nd2
					val nd3=NaturalDeduction.getRoot(tr2)
					val NaturalDeduction.dNode(x3,y3) = nd3
					fun getflag(nd1',nd2',nd3') = 
						if (NaturalDeduction.isConjintro(nd1',nd2',nd3')) then flg1 else 
						if (NaturalDeduction.isImplelim(nd1',nd2',nd3')) then flg2 else 
						if (NaturalDeduction.isExistentialelim(nd1',nd2',nd3')) then flg3 else 
						flg0
				in case (getflag(nd2,nd3,nd),y2,y3)
					of (flg1,x,y) => GentzenSystem.sTree2(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr1),transformSequent(tr2))
					| (flg2,Form.Implication(x,y),Form.Implication(p,q)) => if(x=Form.Implication(p,q)) then GentzenSystem.sTree2(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr1),GentzenSystem.sTree2(GentzenSystem.sNode(y2::eraseTags(x1),y1),transformSequent(tr2),GentzenSystem.sTree(GentzenSystem.sNode(y1::eraseTags(x1),y1)))) else if (p=Form.Implication(x,y)) then GentzenSystem.sTree2(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr2),GentzenSystem.sTree2(GentzenSystem.sNode(y3::eraseTags(x1),y1),transformSequent(tr1),GentzenSystem.sTree(GentzenSystem.sNode(y1::eraseTags(x1),y1)))) else raise ConversionError "Tree Error"
					| (flg2,Form.Implication(x,y),z) => if(x=z) then GentzenSystem.sTree2(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr1),GentzenSystem.sTree2(GentzenSystem.sNode(y2::eraseTags(x1),y1),transformSequent(tr2),GentzenSystem.sTree(GentzenSystem.sNode(y1::eraseTags(x1),y1)))) else raise ConversionError "Tree Error"
					| (flg2,x,Form.Implication(y,z)) => if(x=y) then GentzenSystem.sTree2(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr2),GentzenSystem.sTree2(GentzenSystem.sNode(y3::eraseTags(x1),y1),transformSequent(tr1),GentzenSystem.sTree(GentzenSystem.sNode(y1::eraseTags(x1),y1)))) else raise ConversionError "Tree Error"
					| (flg3,x,y) =>
						let
							val trval=(Set.diff(x2,x3)=[])
						in case trval
							of true => GentzenSystem.sTree2(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr1),GentzenSystem.sTree1(GentzenSystem.sNode(y2::eraseTags(x1),y1),transformSequent(tr2)))
							| false => GentzenSystem.sTree2(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr2),GentzenSystem.sTree1(GentzenSystem.sNode(y3::eraseTags(x1),y1),transformSequent(tr1)))
						end
					| (f,x,y) => raise ConversionError "Tree Error"
				end
			fun handler4(nd,tr1,tr2,tr3) = 
				let
					val NaturalDeduction.dNode(x1,y1) = nd
					val nd2=NaturalDeduction.getRoot(tr1)
					val NaturalDeduction.dNode(x2,y2) = nd2
					val nd3=NaturalDeduction.getRoot(tr2)
					val NaturalDeduction.dNode(x3,y3) = nd3
					val nd4=NaturalDeduction.getRoot(tr3)
					val NaturalDeduction.dNode(x4,y4) = nd4
					val f1=(Set.diff(x2,x1)=[])
					val f2=(Set.diff(x3,x1)=[])
					val f3=(Set.diff(x4,x1)=[])
				in if (f1=true) then GentzenSystem.sTree2(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr1),GentzenSystem.sTree2(GentzenSystem.sNode(y2::eraseTags(x1),y1),transformSequent(tr2),transformSequent(tr3))) else if (f2=true) then GentzenSystem.sTree2(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr2),GentzenSystem.sTree2(GentzenSystem.sNode(y3::eraseTags(x1),y1),transformSequent(tr1),transformSequent(tr3))) else if (f3=true) then GentzenSystem.sTree2(GentzenSystem.sNode(eraseTags(x1),y1),transformSequent(tr3),GentzenSystem.sTree2(GentzenSystem.sNode(y4::eraseTags(x1),y1),transformSequent(tr1),transformSequent(tr2))) else raise ConversionError ("Not an Axiom")
				end
		in case dt
			of NaturalDeduction.dTree(nd) => handler1(nd)
			| NaturalDeduction.dTree1(nd,tr1) => handler2(nd,tr1)
			| NaturalDeduction.dTree2(nd,tr1,tr2) => handler3(nd,tr1,tr2)
			| NaturalDeduction.dTree3(nd,tr1,tr2,tr3) => handler4(nd,tr1,tr2,tr3)
		end
	fun doSubstitute([],y) = y
		| doSubstitute((x1,x2)::rem,NaturalDeduction.Packet(x,f)) = if (x=x2) then NaturalDeduction.Packet(x1,f) else
			doSubstitute(rem,NaturalDeduction.Packet(x,f))
	fun doSubstitution(x,[]) = []
		| doSubstitution(x,y::ys) = doSubstitute(x,y)::doSubstitution(x,ys)
	fun tostring(str,[]) = str
		| tostring(str,x) = String.concat([str,String.implode(x)])
	fun nextName(str,x,[]) = tostring(str,#"'"::x)
		| nextName(str,x,y) = if (Set.belongs(tostring(str,#"'"::x),y)) then nextName(str,#"'"::x,y) else tostring(str,#"'"::x)
	fun firstName(str,[]) = str
		| firstName(str,y) = if (Set.belongs(str,y)) then nextName(str,[],y) else str
	fun nameIt([],pPoset,rsrvd,str) = []
		| nameIt(x,[],rsrvd,str) = raise NameError("Out of poset")
		| nameIt(x,y::ys,rsrvd,str) = if (GentzenSystem.belongsNW(y,x)) then (firstName(str,rsrvd),y)::nameIt(GentzenSystem.deleteElem(y,x),y::ys,str::rsrvd,firstName(str,rsrvd)) else nameIt(x,y::ys,rsrvd,str)
end
