(* ::Package:: *)

(* ::Title:: *)
(*DirichletCharacters Package*)


(* ::Chapter:: *)
(*Enhanced functionality for handling Dirichlet characters. The primary enhancement is via the use of Conrey's notation, which makes arithmetic with characters transparent.*)


BeginPackage["DirichletCharacters`"]


(* ::Subsection:: *)
(*Usage Messages*)


(* ::Text:: *)
(*These are accessed by "?CommandName". A list of commands can be obtained by "?DirichletCharacters`*".*)


DC::usage = "DC[q,i] represents the Dirichlet character with modulus q and index i, in Conrey's naming scheme. DC[q,i][n] evaluates the character at n. A list of commands can be obtained by \"?DirichletCharacters`*\".";
CharacterModulus::usage = "Returns the modulus of a character given in DC[modulus,index] form.";
ConreyIndex::usage = "Returns the index of a character given in DC[modulus,index] form.";
CharacterQ::usage = "Returns True if the input is in the form DC[modulus,index] with modulus a positive integer and index is an integer that is relatively prime to modulus, and returns False otherwise."; 

ConreyIndexToMathematicaIndex::usage="ConreyIndexToMathematicaIndex[\[Chi]] takes in a character in DC[q,i] form and returns {q,j}, where the character is the same as the built-in DirichletCharacter[q,j,#].";
ConreyIndexFromMathematicaIndex::usage="ConreyIndexFromMathematicaIndex[q,j] returns DC[q,i], which is character built into Mathematica as DirichletCharacter[q,j,#].";

Generators::usage="Generators[q] returns a list of residues that multiplicatively generate the group of units modulo q.";
IdentifyCharacter::usage="IdentifyCharacter[LOV] returns the character with modulus Length[LOV] that agrees with the list of values LOV. This function could be much more awesome, in that it should only need a few values to work. Also, the implementation is horribly slow.";

CharacterIndices::usage="CharacterIndices[q] returns the subset of {1,...,q} of numbers that are relatively prime to q.";
CharacterGroup::usage="CharacterGroup[q] returns the list of all EulerPhi[q] characters with modulus q.";

LMFDBLink::usage="LMFDBLink[\[Chi]] returns hyperlinks into the L-Series and Maass Forms Database (LMFDB) for the character and for the associated L-series.";

TrivialCharacterQ::usage="TrivialCharacterQ[\[Chi]] returns True if \[Chi]=DC[q,i] is the trivial character. That is, if q==1.";
PrincipalCharacterQ::usage="PrincipalCharacterQ[\[Chi]] returns True if \[Chi]=DC[q,i] is a principal character. That is, if Mod[i,q]==1.";
RealCharacterQ::usage="RealCharacterQ[\[Chi]] returns True if \[Chi]=DC[q,i] is a real character. That is, if Mod[i^2,q]==1.";
Sign::usage = Sign::usage<>"For a character \[Chi]=DC[q,i], Sign[\[Chi]] returns 1 or -1 according to whether \[Chi] is an even or odd function. That is, it returns \[Chi](-1).";
EvenQ::usage = EvenQ::usage<>"For a character \[Chi]=DC[q,i], EvenQ[\[Chi]] returns True if \[Chi] is an even function, and False otherwise.";
OddQ::usage = OddQ::usage<>"For a character \[Chi]=DC[q,i], OddQ[\[Chi]] returns True if \[Chi] is an odd function, and False otherwise.";
PrimitiveCharacterQ::usage="PrimitiveCharacterQ[\[Chi]] returns True if \[Chi]=DC[q,i] is a primitive character, and False otherwise.";

InducedModulusQ::usage="InducedModulusQ[\[Chi],d] returns true if d is an induced modulus for the character \[Chi], given in the form DC[q,i].";
InducedModuli::usage="InducedModulusQ[\[Chi]] returns a list of the induced moduli for the character \[Chi], given in the form DC[q,i].";
Conductor::usage="Conductor[\[Chi]] returns the conductor of \[Chi], given in the form DC[q,i].";

NumberOfPrimitiveCharacters::usage="NumberOfPrimitiveCharacters[q] returns the number of primitive characters modulo q.";
PrimitiveCharacters::usage="PrimitiveCharacters[q] returns a list of the primitive characters with modulus q.";
InducingCharacter::usage="InducingCharacter[\[Chi]] returns the character that induces \[Chi]=DC[q,i].";

CharacterTable::usage="CharacterTable[q] returns the character table for the group of characters modulo q. To get labelling, provide the option Method -> TableForm";

ConjugateCharacter::usage="ConjugateCharacter[\[Chi]] returns the character \[Tau] obtained by pointwise complex conjugation. In other words, \[Chi]\[Tau] is real.";
CharacterOrder::usage="CharacterOrder[\[Chi]] returns the least positive integer n with \[Chi] a principal character. CharacterOrder[\[Chi],{\!\(\*SubscriptBox[\(a\), \(1\)]\),...,\!\(\*SubscriptBox[\(a\), \(k\)]\)}] returns the least positive integer n with \!\(\*SuperscriptBox[\(\[Chi]\), \(n\)]\) in the set {\!\(\*SubscriptBox[\(a\), \(1\)]\),...,\!\(\*SubscriptBox[\(a\), \(k\)]\)}, which must be a list of characters with same modulus as \[Chi].";
LiftCharacter::usage="LiftCharacter[\[Chi],Q] returns a character \[Tau] with modulus Q and \[Chi]*DC[Q,1] = \[Tau].";

CharacterDecomposition::usage="Not implimented. CharacterDecomposition[LOV] returns a linear combination of characters that evaluates Range[Length[LOV]] to LOV.";

DirichletL::usage="DirichletL[\[Chi],s] returns the evaluation of the L-series for \[Chi] evaluated at s. This uses the built in Mathematica DirichletL function.";
LSeriesXi::usage="LSeriesXi[\[Chi],t] returns a symmetrized form of the Dirichlet L-series for the character \[Chi], given in the form DC[q,i], evaluated at t.";
LSeriesZeros::usage="LSeriesZeros[\[Chi],interval,stepsize] evaluates the (symmetrized) L series Xi[\[Chi],t] for the character \[Chi], given in the form DC[q,i], in the interval, given in the form Interval[{a,b}] at points at most stepsize apart, and uses bisection whenever there is a sign change. Returns a list of real numbers that are the imaginary parts of zeros of the L series on the critical line. This may miss zeros!";
NTchi::usage="NTchi[\[Chi],Interval[{a,b}]] uses numerical integration to compute the number of zeros of L(s,\[Chi]) whose height is between a and b.";


Begin["`Private`"]


(* ::Subsection::Closed:: *)
(*Interacting with the data structure: *)
(*CharacterQ, ConreyIndex, CharacterModulus, DCValue, *)
(*CharacterIndices, IdentifyCharacter,*)
(*ConreyIndexToMathematicaIndex, ConreyIndexFromMathematicaIndex, Generators*)


CharacterModulus[DC[q_,m_]]:=q;
ConreyIndex[DC[q_,m_]]:=m;
CharacterQ[\[Chi]_]:=(Head[\[Chi]]==DC)&&Length[\[Chi]]==2&&IntegerQ[First[\[Chi]]]&&Positive[First[\[Chi]]]&&IntegerQ[Last[\[Chi]]]&&GCD[First[\[Chi]],Last[\[Chi]]]==1;


DC[q_Integer?Positive,m_Integer][n_Integer] :=
		Module[
			{bm=Mod[m,q,-1],bn=Mod[n,q,-1]},
			Which[
				Or[Not[CoprimeQ[q,bn]],Not[CoprimeQ[q,bm]]],
					0,
				bm==1||bn==1,
					1,
				bn==-1,
					Module[
						{evenexponent=0,oddpart=q,evencontribution,oddcontribution},
						While[EvenQ[oddpart],evenexponent++;oddpart/=2];
						evencontribution=If[evenexponent<=1,1,(-1)^Boole[Divisible[bm+1,4]]];
						oddcontribution=Product[JacobiSymbol[bm,prime],{prime,First/@FactorInteger[oddpart]}];
						evencontribution*oddcontribution
					],
				bm==-1,
					DC[q,bn][bm],
				EvenQ[q],
					Module[{qe2=IntegerExponent[q,2],evencontribution,oddcontribution},
					  evencontribution=Which[
						qe2==1,  1,
						qe2==2,  If[Mod[bm,4]==1||Mod[bn,4]==1,1,-1],
						qe2>=3,  
							Module[{a,b,\[Epsilon]m,\[Epsilon]n},
								If[IntegerQ[a=MultiplicativeOrder[5,2^qe2,{bm}]],
									\[Epsilon]m=1,
									a=MultiplicativeOrder[5,2^qe2,{-bm}];\[Epsilon]m=-1];
								If[IntegerQ[b=MultiplicativeOrder[5,2^qe2,{bn}]],
									\[Epsilon]n=1,
									b=MultiplicativeOrder[5,2^qe2,{-bn}];\[Epsilon]n=-1];
								Exp[2\[Pi] I((a b)/2^(qe2-2))]*(-1)^Boole[And[\[Epsilon]n === -1,\[Epsilon]m === -1]]
						]];
						oddcontribution=DC[q/2^qe2,bm][bn];
						evencontribution*oddcontribution],
				OddQ[q],
					Module[{gList,mList,bList,factorlist,philist},
						factorlist=FactorInteger[q];
						gList=factorlist/.{p_Integer,e_}:>{p,e,PrimitiveRoot[p^2,1]};
						mList=gList/.{p_Integer,e_,g_}:>MultiplicativeOrder[g,p^e,{bm}];
						philist=factorlist/.{p_Integer,e_}:>(p-1) p^(e-1);
						bList=gList/. {p_Integer,e_,g_}:>MultiplicativeOrder[g,p^e,{bn}];
						Exp[2\[Pi] I Mod[(mList.(bList/philist)),1]]
					]
			]];
			
DC[q_Integer?Positive,m_Integer][List[n___Integer]] := Map[DC[q,m],{n}];
(*SAD: Evaluation recomputes the stuff related to q and m for each value of n. One frequently computes it on Range[q].*)		


Generators[1]={};
Generators[q_Integer?Positive]:=
	Module[{factorlist=FactorInteger[q],g,gens={},CRinputs},
		g[p_]:=g[p]=PrimitiveRoot[p^2,1];
		If[Length[factorlist]==1,
			p=factorlist[[1,1]];
			gens=If[p==2,Which[q==2,{},q==4,{3},True,Union[Mod[{-1,5},q]]],{g[p]}];
		Return[gens]];

	If[EvenQ[q],
		CRinputs=Transpose[factorlist/.{{2,e_}:>{-1,2^e},{p_Integer?(#>=3&),e_Integer}:>{1,p^e}}];
		AppendTo[gens,ChineseRemainder@@CRinputs];
		CRinputs=Transpose[factorlist/.{{2,e_Integer}:>{5,2^e},{p_Integer?(#>=3&),e_Integer}:>{1,p^e}}];
		AppendTo[gens,ChineseRemainder@@CRinputs]];

	gens=Select[gens,#>1&];

	Do[
		CRinputs=Transpose[Append[Drop[factorlist,{k}]/.{{2,e_Integer}:>{1,2^e},{p_Integer,e_Integer}:>{1,p^e}},factorlist[[k]]/.{p_,e_}:>{g[p],p^e}]];
		AppendTo[gens,ChineseRemainder@@CRinputs],
	{k,1+Boole[EvenQ[q]],Length[factorlist]}];

	Union[gens]];


CharacterIndices[q_Integer]:=CharacterIndices[q]=Select[Range[q],GCD[#,q]===1&];

CharacterGroup[q_Integer]:=Map[DC[q,#]&,CharacterIndices[q]];


IdentifyCharacter[ListOfValues_List]:=
  Module[
    {q=Length[ListOfValues],vals=Simplify[ListOfValues],Rq,ind},
    Rq=Range[q];
    ind=First[Select[CharacterIndices[q],(vals==DC[q,#][Rq])&,1]];
    DC[q,ind]];
(*SAD: IdentifyCharacter needs a full period of values.*)
(*SAD: IdentifyCharacter does not take advantage of generators.*)
(*SAD: IdentifyCharacter will not function intelligently if ListOfValues does not correspond to a character.*)


ConreyIndexToMathematicaIndex[\[Chi]_DC?CharacterQ]:=ConreyIndexToMathematicaIndex[\[Chi]]=
    Module[{q=CharacterModulus[\[Chi]],gens,j=1},
        gens=Generators[q];
        onGens=\[Chi][gens];
        While[onGens != Map[DirichletCharacter[q,j,#]&,gens],j++];
        List[q,j]];
(*SAD: ConreyIndexToMathematicaIndex is not aware of the structure in Mathematica's notation.*)

ConreyIndexFromMathematicaIndex[q_Integer,j_Integer]:=
	(ConreyIndexFromMathematicaIndex[q,j]=
			Module[{onGens,m=1,gens=Generators[q]},
              onGens=Map[DirichletCharacter[q,j,#]&,gens];
              m=Select[CharacterIndices[q],DC[q,#][gens]==onGens&,1];
              First[m]] 
              )/; 0<j<EulerPhi[q];
(*SAD: ConreyIndexFromMathematicaIndex is not aware of the structure in Mathematica's notation.*)


(* ::Subsection::Closed:: *)
(*Links to the External LMFDB database (some broken links that I consider an LMFDB problem): *)
(*LMFDBLink*)


LMFDBLink[\[Chi]_DC?CharacterQ]:={Hyperlink["LMFDB link to character","http://www.lmfdb.org/Character/Dirichlet/"<>ToString[CharacterModulus[\[Chi]]]<>"/"<>ToString[ConreyIndex[\[Chi]]]],Hyperlink["LMFDB link to L-series","http://www.lmfdb.org/L/Character/Dirichlet/"<>ToString[CharacterModulus[\[Chi]]]<>"/"<>ToString[ConreyIndex[\[Chi]]]]}


(* ::Subsection::Closed:: *)
(*Properties of Characters: *)
(*TrivialCharacterQ, PrincipalCharacterQ, RealCharacterQ, Sign, EvenQ, OddQ, PrimitiveCharacterQ*)


TrivialCharacterQ[\[Chi]_DC?CharacterQ]:=CharacterModulus[\[Chi]]==1;

PrincipalCharacterQ[\[Chi]_DC?CharacterQ]:=Mod[ConreyIndex[\[Chi]],CharacterModulus[\[Chi]]]==1;

RealCharacterQ[\[Chi]_DC?CharacterQ]:=PowerMod[ConreyIndex[\[Chi]],2,CharacterModulus[\[Chi]]]==1;

DC/:Sign[\[Chi]_DC?CharacterQ]:=\[Chi][-1]


DC/:EvenQ[\[Chi]_DC?CharacterQ]:= (Sign[\[Chi]] == 1);
DC/:OddQ[\[Chi]_DC?CharacterQ]:= (Sign[\[Chi]] == -1);

PrimitiveCharacterQ[\[Chi]_DC?CharacterQ]:=InducedModuli[\[Chi]]=={CharacterModulus[\[Chi]]};



(* ::Subsection::Closed:: *)
(*Induced Moduli: *)
(*InducedModulusQ, InducedModuli, Conductor, InducingCharacter*)


InducedModulusQ[\[Chi]_DC?CharacterQ,d_Integer]:=
  Module[
	  {q=CharacterModulus[\[Chi]]},
	Which[
		(* q is always an induced modulus *)
		d==q, True, 
		(*By definition, induced modulus must be a positive divisor of q *)
		Not[d>0 && Divisible[q,d]], False,
		(* using definition on page 187 (Section 8.7) of Apostol *)
		True, AllTrue[ Range[d+1,q,d], GCD[#,q]>1||\[Chi][#]==1&]
			]
		];	

(* Sadly does not use that if d is an induced modulus and d|Subscript[d, 2]|q, then Subscript[d, 2] is an induced modulus *)
InducedModuli[\[Chi]_DC?CharacterQ]:=Select[Divisors[CharacterModulus[\[Chi]]],InducedModulusQ[\[Chi],#]&];

Conductor[\[Chi]_DC?CharacterQ]:=First[Select[Divisors[CharacterModulus[\[Chi]]],InducedModulusQ[\[Chi],#]&,1]];

InducingCharacter[chi_]:=
	Module[
		{qstar=Conductor[chi],q=CharacterModulus[chi]},
		First[Select[PrimitiveCharacters[qstar],#*DC[q,1]==chi&,1]]];


(* ::Subsection::Closed:: *)
(*Primitive Characters:*)
(*NumberOfPrimitiveCharacters, PrimitiveCharacters*)


NumberOfPrimitiveCharacters[q_Integer?Positive]:=
	Module[
		{factorization=FactorInteger[q],term},
		term=factorization/.{{1,1}->1,{p_,1}:>(1-2/p),{p_,e_/;e>1}:>(1-1/p)^2};
		q*(Times@@term)];

PrimitiveCharacters[q_Integer?Positive]:=Map[DC[q,#]&,Select[CharacterIndices[q],PrimitiveCharacterQ[DC[q,#]]&]];


(* ::Subsection::Closed:: *)
(*Character Table:*)
(*CharacterTable*)


Options[CharacterTable]={Method->List};
CharacterTable[q_Integer?Positive,OptionsPattern[]]:=
	Module[{PHI,ct},
		PHI=CharacterIndices[q];
		ct=Table[DC[q,m][PHI],{m,PHI}];
		Which[
			OptionValue[Method]===TableForm,
				TableForm[ct,TableHeadings->{"DC["<>ToString[q]<>","<>ToString[#]<>"]"&/@PHI,PHI}],
			OptionValue[Method]===List,
				ct,
			True,
				OptionValue[Method][ct]
		]
	];
(*SAD: CharacterTable doesn't take advantage of symmetry.*)


(* ::Subsection::Closed:: *)
(*Character Arithmetic:*)
(*ConjugateCharacter, CharacterOrder, Times, Equal, Lift*)


ConjugateCharacter[\[Chi]_DC?CharacterQ]:=Module[
	{inverse},
	inverse=PowerMod[ConreyIndex[\[Chi]],-1,CharacterModulus[\[Chi]]];
	DC[CharacterModulus[\[Chi]],inverse]];
ConjugateCharacter[DC[1,1]]=DC[1,1];

CharacterOrder[\[Chi]_DC?CharacterQ]:=MultiplicativeOrder[ConreyIndex[\[Chi]],CharacterModulus[\[Chi]]];
CharacterOrder[\[Chi]_DC?CharacterQ,A_List]:=MultiplicativeOrder[ConreyIndex[\[Chi]],CharacterModulus[\[Chi]],Map[ConreyIndex,A]];


LiftCharacter[\[Chi]_DC?CharacterQ,NewQ_]:=Module[
	{q=CharacterModulus[\[Chi]],
	m=ConreyIndex[\[Chi]],
	F=FactorInteger[NewQ],
	residues,
	moduli,
	twoRule,
	pRule},
	
	twoRule={2,e_Integer}:>
		Which[
			IntegerExponent[q,2]==0,1,
			IntegerExponent[q,2]==e,m,
			True,If[Mod[Mod[m,2^IntegerExponent[q,2]],4]==1,1,-1]*PowerMod[m,2^(e-IntegerExponent[q,2]),2^e]];
	pRule={p_Integer,e_Integer}:>If[IntegerExponent[q,p]==0,1,Mod[PowerMod[m,p^(e-IntegerExponent[q,p]),p^e],p^e]];
	
	residues=F/.{twoRule,pRule};
	moduli=F/.{p_Integer,e_Integer}:>p^e;
	DC[NewQ,ChineseRemainder[residues,moduli]]];


DC/:Power[\[Chi]_DC?CharacterQ,exponent_Integer]:=Module[
	{q=CharacterModulus[\[Chi]],
	m=ConreyIndex[\[Chi]]},
	DC[q,PowerMod[m,exponent,q]]];


DC/:Equal[DC[q1_Integer,m1_Integer],DC[q2_Integer,m2_Integer]]:=
Module[{g1,g2,f1,f2,p,e1,e2,M},
	{g1,g2}={CoprimeQ[q1,m1],CoprimeQ[q2,m2]};
	If[Not[g1]||Not[g2],Return[g1==g2]];
	(* we know: neither DC is 0 *)

	If[q1>q2,Return[DC[q2,m2]==DC[q1,m1]]];
	(* we know: q1 \[LessEqual] q2 *)

	If[q1==q2,Return[Mod[m1,q1]==Mod[m2,q1]]];
	(* we know: q1 < q2 *)

	{f1,f2}=Map[FactorInteger,{q1,q2}];
	(*Are they zero in the same places?*)
	If[Not[(First/@f1)==(First/@f2)],Return[False]];
	(* we know: f1 and f2 have the same length *)

	(*Prime powers are the base case*)
	If[Length[f1]==1,
		{p,e1}=f1[[1]];
		{p,e2}=f2[[1]];
		If[p==2,
			M=Mod[m1,q1];Mod[If[Mod[M,4]==1,1,-1]*m2,q2]==PowerMod[M,2^(e2-e1),q2],
			Mod[m2,q2]==PowerMod[m1,p^(e2-e1),q2]],

	AllTrue[Table[{DC[f1[[k,1]]^f1[[k,2]],m1],DC[f2[[k,1]]^f2[[k,2]],m2]},{k,Length[f1]}],Equal@@#&]
	]
];


DC/:Times[DC[q1_,m1_],DC[q2_,m2_],othercharacters___]:=
Which[
q1==q2,
Times[DC[q1,Mod[m1 m2,q1]],othercharacters],

CoprimeQ[q1,q2],
Times[DC[q1 q2,ChineseRemainder[{m1,m2},{q1,q2}]],othercharacters],

True,
Block[
{Q=LCM[q1,q2]},
Times[DC[Q,Mod[ConreyIndex[LiftCharacter[DC[q1,m1],Q]]*ConreyIndex[LiftCharacter[DC[q2,m2],Q]],Q]],othercharacters]
]
];


(* ::Subsection::Closed:: *)
(*Zeros of L-Series:*)
(*DirichletL, LSeriesXi, LSeriesZeros, NTchi*)


DC/:DirichletL[\[Chi]_DC?CharacterQ,s_]:=Module[{q,m},{q,m}=ConreyIndexToMathematicaIndex[\[Chi]];DirichletL[q,m,s]];


(* See http://arxiv.org/pdf/1102.2680v1.pdf for details and symmetries of Xi *)
LSeriesXi[\[Chi]_DC?CharacterQ,t_]:=
	Module[
		{s=1/2+t I,b=Boole[OddQ[\[Chi]]],q,m},
		
		{q,m}=ConreyIndexToMathematicaIndex[\[Chi]];
		(\[Pi]/q)^(-(s+b)/2) Gamma[(s+b)/2]DirichletL[q,m,s]];


NTchi[chi_,i_Interval]:=Module[{a=(1-chi[-1])/2,q=CharacterModulus[chi],conjchi,estimateT=0,estimatet=0,T,t},
{t,T}={Min[i],Max[i]};
If[t<0,conjchi=ConjugateCharacter[chi]];
Which[
T>0,
	estimateT=1/\[Pi] Im[LogGamma[1/4+a/2+I T/2]]+T/(2\[Pi]) Log[q/\[Pi]]+1/\[Pi] Im[NIntegrate[D[DirichletL[chi,s],s]/DirichletL[chi,s],{s,1/2,3}]]+1/\[Pi] Im[NIntegrate[D[DirichletL[chi,s],s]/DirichletL[chi,s],{s,3+I T,1/2+I T}]],
T<0,
	estimateT=1/\[Pi] Im[LogGamma[1/4+a/2+I (-T)/2]]+-T/(2\[Pi]) Log[q/\[Pi]]+1/\[Pi] Im[NIntegrate[D[DirichletL[conjchi,s],s]/DirichletL[conjchi,s],{s,1/2,3}]]+1/\[Pi] Im[NIntegrate[D[DirichletL[conjchi,s],s]/DirichletL[conjchi,s],{s,3-I T,1/2-I T}]],
T==0,
	estimateT=0];
Which[
t>0,
	estimatet=1/\[Pi] Im[LogGamma[1/4+a/2+I t/2]]+t/(2\[Pi]) Log[q/\[Pi]]+1/\[Pi] Im[NIntegrate[D[DirichletL[chi,s],s]/DirichletL[chi,s],{s,1/2,3}]]+1/\[Pi] Im[NIntegrate[D[DirichletL[chi,s],s]/DirichletL[chi,s],{s,3+I t,1/2+I t}]],
t<0,
	estimatet=1/\[Pi] Im[LogGamma[1/4+a/2+I (-t)/2]]+-t/(2\[Pi]) Log[q/\[Pi]]+1/\[Pi] Im[NIntegrate[D[DirichletL[conjchi,s],s]/DirichletL[conjchi,s],{s,1/2,3}]]+1/\[Pi] Im[NIntegrate[D[DirichletL[conjchi,s],s]/DirichletL[conjchi,s],{s,3-I t,1/2-I t}]],
t==0,
	estimatet=0];

Round[estimateT]-If[t>0,1,-1]Round[estimatet]]


LSeriesZeros[\[Chi]_,int_Interval,stepsize_]:=Module[
	{Bisection,F,start,end,sols,q,m,b,root,zeros},
(* Assumes that all zeros are on the Re[s]=1/2 line, and checks for potential 
zeros every stepsize inside int, using Bisection if there is a sign change. 
Uses Xi, which is real on the real axis, to avoid checking both Real and Imaginary parts. *)

Bisection[lower_,upper_]:=Bisection[lower,Sign[F[lower]],upper,Sign[F[upper]]];
Bisection[lower_,Flower_,upper_,Fupper_]:=
	Module[{mid,Fmid},
		mid=(lower+upper)/2;
		Fmid=Sign[F[mid]];
		Which[mid==lower||mid==upper,mid,
		Flower Fupper>0,Infinity,
		Flower Fmid<0,Bisection[lower,Flower,mid,Fmid],
		Fmid Fupper<0,Bisection[mid,Fmid,upper,Fupper]]];

	{q,m}=ConreyIndexToMathematicaIndex[\[Chi]];
	b=Boole[OddQ[\[Chi]]];
	F[t_]:=Re[(\[Pi]/q)^(-(1/2+t I+b)/2) * Gamma[(1/2+t I+b)/2] * DirichletL[q,m,1/2+t I]];

	start=Min[int];
	end=Max[int];

	zeros=Reap[
			Do[
				root=Bisection[a,a+stepsize];
				If[root<=end,Sow[root]],
			{a,start,end+stepsize,stepsize}]];
	If[Length[Last[zeros]]>=1,Last[Last[zeros]],{}]
	];

(*SAD: LSeriesZeros does not take advantage of symmetry of real characters.*)
(*SAD: LSeriesZeros does not take advantage of a table.*)
(*SAD: LSeriesZeros does not go to arbitrary precision.*)
(*SAD: LSeriesZeros does not check for missing zeros.*)
(*SAD: LSeriesZeros does not use Compile for the Xi function.*)
(*SAD: LSeriesZeros uses bisection, which isn't brainiac territory.*)
(*SAD: LSeriesZeros does not scale "stepsize" to be smart about when there are more zeros, like at great height or conductor.*)
(*SAD: LSeriesZeros assumes GRH, and even so may miss zeros.*)
(*SAD: LSeriesZeros does not generate an error message to the effect that zeros are not too precise, and some may be missing.*)


(* ::Subsection::Closed:: *)
(*End the package*)


End[]
EndPackage[]
