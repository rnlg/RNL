(* ::Package:: *)

(* ::Title:: *)
(*GMatrices*)


(* ::Subsubtitle:: *)
(*Package for manipulating with \[Gamma]-matrices*)


(* ::Text:: *)
(**)


(* ::Section:: *)
(*Preamble*)


Module[{b=Contexts["GMatrices`*"]},If[b=!={},
    LinearFunctions`LFRules=
      DeleteCases[LinearFunctions`LFRules,x_/;!FreeQ[x,GMatrices`GTrace]];
    (Unprotect[#];Remove[#])&/@((#<>"*")&/@b)]];
\[Gamma];(*Make Global`\[Gamma] visible*)



(* ::Section:: *)
(*BeginPackage[GMatrices`]*)


Vectors`VectorsLog=False;Needs["Vectors`","RNL`Vectors`"];
Needs["LinearFunctions`","RNL`LinearFunctions`"];
Needs["Numbers`","RNL`Numbers`"];
Needs["Types`","RNL`Types`"];Notation`AutoLoadNotationPalette = False;
BeginPackage["GMatrices`",{"Notation`","Types`","Numbers`","LinearFunctions`","Vectors`"}]


$GMatricesFORMTempDir=$TemporaryDirectory<>"/";


(* ::Section:: *)
(*Open all public names*)


GLMatrix::usage="GLMatrix is a type of all linear combinations of \[Gamma]-matrices";
GPMatrix::usage="GPMatrix is a type of all polinomials of \[Gamma]-matrices";
GTComponent::usage="GTComponent[{\[LeftAngleBracket]\[ScriptU]\[ScriptP]\[ScriptP]\[ScriptE]\[ScriptR]\[RightAngleBracket]},{\[LeftAngleBracket]\[ScriptL]\[ScriptO]\[ScriptW]\[ScriptE]\[ScriptR]\[RightAngleBracket]},{\[LeftAngleBracket]\[ScriptN]\[ScriptU]\[ScriptM]\[ScriptB]\[RightAngleBracket]}] is a type of covariant polinomials of \[Gamma]-matrices having \[LeftAngleBracket]\[ScriptU]\[ScriptP]\[ScriptP]\[ScriptE]\[ScriptR]\[RightAngleBracket], \[LeftAngleBracket]\[ScriptL]\[ScriptO]\[ScriptW]\[ScriptE]\[ScriptR]\[RightAngleBracket], and \[LeftAngleBracket]\[ScriptN]\[ScriptU]\[ScriptM]\[ScriptB]\[RightAngleBracket](coupled) indices";
GTCompQ::usage="GTCompQ[\[ScriptE]\[ScriptX]\[ScriptP]\[ScriptR]] gives True if \[ScriptE]\[ScriptX]\[ScriptP]\[ScriptR] is of type GTComponent[...]";
GTComponentQ::usage="GTComponentQ[\[ScriptE]\[ScriptX]\[ScriptP]\[ScriptR],{\[ScriptU]\[ScriptP]\[ScriptP]\[ScriptE]\[ScriptR]},{\[ScriptL]\[ScriptO]\[ScriptW]\[ScriptE]\[ScriptR]}] gives true if ExpressionType[\[ScriptE]\[ScriptX]\[ScriptP]\[ScriptR]] matches GTComponent[{\[ScriptU]\[ScriptP]\[ScriptP]\[ScriptE]\[ScriptR]},{\[ScriptL]\[ScriptO]\[ScriptW]\[ScriptE]\[ScriptR]},_List]";
GIdentity::usage="GIdentity is the identity matrix";
GMatrix::usage="GMatrix is the \[Gamma]-matrix, use lower/upper indices";
Gamma5::usage="Gamma5 is the normalized contraction of \[Gamma]-matrices with the antisymmetric tensor in integer dimension";
GReduce::usage="GReduce[\[LeftAngleBracket]\[ScriptE]\[ScriptX]\[ScriptP]\[ScriptR]\[RightAngleBracket]] does some known reduction of formulas with \[Gamma]-matrices";
GLinQ::usage="GLinQ[\[LeftAngleBracket]\[ScriptE]\[ScriptX]\[ScriptP]\[ScriptR]\[RightAngleBracket]] returns True if \[LeftAngleBracket]\[ScriptE]\[ScriptX]\[ScriptP]\[ScriptR]\[RightAngleBracket] is linear in \[Gamma]-matrices";
GHat::usage="GHat[\[LeftAngleBracket]\[ScriptV]\[ScriptE]\[ScriptC]\[RightAngleBracket]] represents the contraction of\[LeftAngleBracket]\[ScriptV]\[ScriptE]\[ScriptC]\[RightAngleBracket]and \[Gamma]-matrix vector indices";
GTrace::usage="GTrace[\[LeftAngleBracket]\[ScriptCapitalG]\[ScriptCapitalP]\[ScriptCapitalM]\[ScriptA]\[ScriptT]\[ScriptR]\[ScriptI]\[ScriptX]\[RightAngleBracket]] calculates a trace of \[LeftAngleBracket]\[ScriptCapitalG]\[ScriptCapitalP]\[ScriptCapitalM]\[ScriptA]\[ScriptT]\[ScriptR]\[ScriptI]\[ScriptX]\[RightAngleBracket] over \[Gamma]-matrices";
gTrace::usage="gTrace[\[LeftAngleBracket]\[ScriptCapitalG]\[ScriptCapitalP]\[ScriptCapitalM]\[ScriptA]\[ScriptT]\[ScriptR]\[ScriptI]\[ScriptX]\[RightAngleBracket]] marks a trace of \[LeftAngleBracket]\[ScriptCapitalG]\[ScriptCapitalP]\[ScriptCapitalM]\[ScriptA]\[ScriptT]\[ScriptR]\[ScriptI]\[ScriptX]\[RightAngleBracket]. Use FORMTraces to take traces.";
FORMTraces::usage="FORMTraces[ex] takes traces in ex marked with gTrace.\nNB: FORM is not good with denominators, so it is better if ex has no denominators.";
GMatrices::usage="\n"<>ToString[TableForm[Partition[Join[Names["GMatrices`*"],{"","","","","",""}],5],TableSpacing->{0,3}]];


GDistribute::usage="GDistribute[\[LeftAngleBracket]\[ScriptE]\[ScriptX]\[ScriptP]\[ScriptR]\[RightAngleBracket]] distributes over + and pulls out factors in expression";


Print["Input file hash: ",Style[FileHash[$InputFileName,"MD5"],Small]]


Begin["`Private`"]



(* ::Subsection:: *)
(*Notations*)


VecQs[a_]:=(VecQ@@MakeExpression[a,StandardForm]);
VecIndQs[a_]:=(VecIndQ@@MakeExpression[a,StandardForm]);


MakeBoxes[GHat[a_?VecQ],StandardForm]:=OverscriptBox[MakeBoxes[a,StandardForm],"^"]
MakeBoxes[GHat[a_?VecQ],TraditionalForm]:=OverscriptBox[MakeBoxes[a,StandardForm],"^"]
MakeExpression[OverscriptBox[p_?VecQs,"^"],StandardForm]:=MakeExpression[RowBox[{"GHat","[",p,"]"}],StandardForm]
MakeExpression[RowBox[{lhs___,"\[Gamma]","\[CenterDot]",p_?VecQs,rhs___}],StandardForm]:=MakeExpression[RowBox[{"GHat","[",p,"]"}],StandardForm]
MakeExpression[RowBox[{lhs___,p_?VecQs,"\[CenterDot]","\[Gamma]",rhs___}],StandardForm]:=MakeExpression[RowBox[{"GHat","[",p,"]"}],StandardForm]


MakeExpression[SuperscriptBox["\[Gamma]",b_],StandardForm]:=MakeExpression[RowBox[{"SupIndex","[",RowBox[{GMatrix,",",b}],"]"}],StandardForm]


MakeBoxes[SupIndex[GMatrix,b_],StandardForm]:=SuperscriptBox["\[Gamma]",MakeBoxes[b,StandardForm]]
MakeBoxes[SupIndex[GMatrix,b_],TraditionalForm]:=SuperscriptBox["\[Gamma]",MakeBoxes[b,TraditionalForm]]


MakeExpression[SubscriptBox["\[Gamma]",b_],StandardForm]:=MakeExpression[RowBox[{"SubIndex","[",RowBox[{GMatrix,",",b}],"]"}],StandardForm]


MakeBoxes[SubIndex[GMatrix,b_],StandardForm]:=SubscriptBox["\[Gamma]",MakeBoxes[b,StandardForm]]
MakeBoxes[SubIndex[GMatrix,b_],TraditionalForm]:=SubscriptBox["\[Gamma]",MakeBoxes[b,TraditionalForm]]


MakeExpression[SubscriptBox["I","\[Gamma]"],StandardForm]:=MakeExpression["GIdentity",StandardForm]
MakeBoxes[GIdentity,StandardForm]:=SubscriptBox["I","\[Gamma]"]


AddInputAlias[NotationBoxTag[SubscriptBox["I","\[Gamma]"]],"ig",InputNotebook[]];


MakeExpression[SubscriptBox["\[Gamma]","5"],StandardForm]:=MakeExpression["Gamma5",StandardForm]
MakeBoxes[Gamma5,StandardForm]:=SubscriptBox["\[Gamma]","5"]


AddInputAlias[NotationBoxTag[SubscriptBox["\[Gamma]","5"]],"g5",InputNotebook[]];


TypeHierarchy[GLMatrix,GPMatrix];
Unprotect[Times,Plus,Dot];
Block[{TypesBelow},Clear[TypesBelow];
ReleaseHold[Hold[
AddTypeRule[SubIndex,{{_,GMatrix},{Number,_}}:>GLMatrix,{{_,GMatrix},{VectorIndex,i_}}:>GTComponent[{},{i},{}]];
AddTypeRule[SupIndex,{{_,GMatrix},{Number,_}}:>GLMatrix,{{_,GMatrix},{VectorIndex,i_}}:>GTComponent[{i},{},{}]];AddTypeRule[GHat,{{Vector,_}}:>GTComponent[{},{},{}]];
AddTypeRule[Times,{{Number,_}...,{GLMatrix,_},{Number,_}...}:>GLMatrix,{{Number,_}...,{GPMatrix,_},{Number,_}...}:>GPMatrix,l:{({Number|TComponent[_List,_List,_List],_})...,{GTComponent[_List,_List,_List],_},({Number|TComponent[_List,_List,_List],_})...}:>GTComponent@@Sort/@MapThread[Join,Apply[List,Cases[(#[[1]]&/@l),_TComponent|_GTComponent],2]]];
AddTypeRule[Plus,{{GLMatrix,_}..}:>GLMatrix,{{GPMatrix,_}..}:>GPMatrix,l1:{({GTComponent[a_List,b_List,_List],_})..}:>GTComponent[a,b,Union@@((#[[1,3]])&/@l1)]];
AddTypeRule[Dot,{{GPMatrix,_}..}:>GPMatrix,l:{{GTComponent[_List,_List,_List],_}..}:>GTComponent@@Sort/@MapThread[Join,Apply[List,(#[[1]]&/@l),2]]]
]/.{a:(GLMatrix|GPMatrix|Number|Vector)->TypesBelow[a]}/.{(a_:>TypesBelow[b:(GLMatrix|GPMatrix|Number|Vector)])->(a:>b)}
]
  ];
TypeX[Gamma5]^={GTComponent[{},{},{}],Gamma5};
Protect[Times,Plus,Dot];



SetLinearIn[(NumQ[#]||TCompQ[#])&,Dot,All];SetLinearIn[(NumQ[#]||TCompQ[#])&,GTrace,1];
SetLinear[GHat,1,VecQ];


GTCompQ[x_]:=ExpressionType[Unevaluated[x],_GTComponent]
GTComponentQ[x_,u_,d_]:=ExpressionType[Unevaluated[x],GTComponent[u,d,_List]]



Declare[GIdentity,GTComponent[{},{},{}]];
GIdentity/:Dot[GIdentity,b__]:=Dot[b];
GIdentity/:Dot[a__,GIdentity,b___]:=Dot[a,b];
Protect[GIdentity];



GHat[0]=0;
GHat[Ort[x_]]:=SubIndex[GMatrix,x];
GHat[OrtC[x_]]:=SupIndex[GMatrix,x];


HoldPattern[LowerIndex[SupIndex[GMatrix,i_],i_->j_]]:=SubIndex[GMatrix,j];
HoldPattern[LowerIndex[Dot[x_,z_],i_->j_]]:=Dot[x,LowerIndex[z,i->j]]/;FreeQ[x,i];
HoldPattern[LowerIndex[Dot[z_,x_],i_->j_]]:=Dot[LowerIndex[z,i->j],x]/;FreeQ[x,i];
HoldPattern[LowerIndex[x_,i_->j_]/;ExpressionType[x,GTComponent[_,{___,i,___},_]]]:=(x/.i->j);
HoldPattern[LowerIndex[x_,i_->j_]/;(i=!=j)&&ExpressionType[x,GTComponent[{___,i,___},_,_]]]:=MetricTensor[{},{i,j}]*x;
HoldPattern[UpperIndex[SubIndex[GMatrix,i_],i_->j_]]:=SupIndex[GMatrix,j];
HoldPattern[UpperIndex[Dot[x_,z_],i_->j_]]:=Dot[x,UpperIndex[z,i->j]]/;FreeQ[x,i];
HoldPattern[UpperIndex[Dot[z_,x_],i_->j_]]:=Dot[UpperIndex[z,i->j],x]/;FreeQ[x,i];
HoldPattern[UpperIndex[x_,i_->j_]/;ExpressionType[x,GTComponent[{___,i,___},_,_]]]:=(x/.i->j);
HoldPattern[UpperIndex[x_,i_->j_]/;(i=!=j)&&ExpressionType[x,GTComponent[_,{___,i,___},_]]]:=MetricTensor[{i,j},{}]*x;


(* ::Input:: *)
(*Dummies[expr_]:=*)
(*  Sort[Union@@*)
(*      Cases[{expr},*)
(*        x_?(TCompQ[#]||GTCompQ[#]&):>*)
(*          First[TypeX[x]][[3]],Infinity],*)
(*   Vectors`Private`VISort]*)


Dummies[expr_]:=Module[{a=ExpressionType[Unevaluated[expr]]},If[MatchQ[Head[a],TComponent|GTComponent],Sort[a[[3]],Vectors`Private`VISort],{}]];


SpEliminate[HoldPattern[GHat[a_?VecQ]]]:=ReleaseHold[Hold[MetricTensor[{},{x1,x2}]*SupIndex[GMatrix,x1]*SupIndex[a,x2]]/.Vectors`Private`newvi[x1,x2]]


Vectors`Private`VErule2=Join[Vectors`Private`VErule2,{
SubIndex[x_?VecQ,n_?VecIndQ]*SupIndex[GMatrix,n_]:>(AppendTo[Vectors`Private`ni,n];GHat[x]),
SupIndex[x_?VecQ,n_?VecIndQ]*SubIndex[GMatrix,n_]:>(AppendTo[Vectors`Private`ni,n];GHat[x]),
SubIndex[x_?VecQ,n_?VecIndQ]*y:Dot[a___,b_.*SupIndex[GMatrix,n_],c___]:>(AppendTo[Vectors`Private`ni,n];Dot[a,(b*GHat[x]),c])/;FreeQ[{a,b,c},n]&&MatchQ[ExpressionType[{a,c}],{___GTComponent}]&&ExpressionType[b,Number|_TComponent],
SupIndex[x_?VecQ,n_?VecIndQ]*y:Dot[a___,b_.*SubIndex[GMatrix,n_],c___]:>(AppendTo[Vectors`Private`ni,n];Dot[a,(b*GHat[x]),c])/;FreeQ[{a,b,c},n]&&MatchQ[ExpressionType[{a,c}],{___GTComponent}]&&ExpressionType[b,Number|_TComponent],
HoldPattern[MetricTensor[{n_,m_}|{m_,n_},{}]]*x_:>(AppendTo[Vectors`Private`ni,n];UpperIndex[x,n->m])/;ExpressionType[x,HoldPattern[GTComponent[{___},{___,n,___},_]]],
HoldPattern[MetricTensor[{m_},{n_}]]*x_:>(AppendTo[Vectors`Private`ni,n];UpperIndex[x,n->m])/;ExpressionType[x,HoldPattern[GTComponent[{___,n,___},{___},_]]],
HoldPattern[MetricTensor[{},{n_,m_}|{m_,n_}]]*x_:>(AppendTo[Vectors`Private`ni,n];LowerIndex[x,n->m])/;ExpressionType[x,HoldPattern[GTComponent[{___,n,___},{___},_]]],
HoldPattern[MetricTensor[{n_},{m_}]]*x_:>(AppendTo[Vectors`Private`ni,n];LowerIndex[x,n->m])/;ExpressionType[x,HoldPattern[GTComponent[{___},{___,n,___},_]]]
}]


HoldPattern[Partial[x_Dot?GTCompQ,v_]]:=
  Plus@@(MapAt[Partial[#,v]&,x,#]&/@
        Position[x,
          y_/;!FreeQ[y,v[[1]]],{1}])
(*HoldPattern[Partial[x_Dot?GTCompQ,v_]]:=
    Sum[MapAt[Partial[#,v]&,x,i],{i,Length[x]}]*)
HoldPattern[Partial[GHat[x_],v_]]:=
  ReleaseHold[
    Hold[SupIndex[GMatrix,x1]*
          Partial[SubIndex[x,x1],v]]/.Vectors`Private`newvi[x1]]



VPolyQ[HoldPattern[Dot[a__]],x_?VecVarQ]:=True/;(And@@(VPolyQ[#,x]&/@{a}));
VPolyQ[GHat[y_],x_?VecVarQ]:=True/;(VPolyQ[y,x]);



GTComponent[_List,{___,a_,a_,___},_List]=Badformed;
GTComponent[_List,{x___,a_,y___},{z___,a_,t___}]=Badformed;
GTComponent[{x___,a_,y___},_List,{z___,a_,t___}]=Badformed;
GTComponent[{x___,a_,y___},{z___,a_,t___},{u___}]:=GTComponent[{x,y},{z,t},{u,a}];



 GLinQ[x_]:=MatchQ[x,((SubIndex|SupIndex)[GMatrix,_?NumQ|_?VecIndQ]|GHat[_?VecQ]|Plus[_?GLinQ,__?GLinQ]|_?(NumQ[#]&&!(#===1)&)*_?GLinQ)]



GReduce[HoldPattern[Dot[a___,SupIndex[GMatrix,\[Mu]_?VecIndQ],b___?GLinQ,SubIndex[GMatrix,\[Mu]_?VecIndQ],c___]]]:=Module[{i,l=Length[{b}]},
GReduce[Sum[-2*(-1)^i Dot[a,Sequence@@Delete[{b},i],{b}[[i]],c],{i,1,l}]+(-1)^l MetricTensor[]*GReduce[Dot[a,GIdentity,b,c]]]];
GReduce[HoldPattern[Dot[a___,Gamma5,b___?GLinQ,Gamma5,c___]]]:=(-1)^(Length[{b}])GReduce[Dot[a,GIdentity,b,c]];
GReduce[HoldPattern[Dot[a___,SubIndex[GMatrix,\[Mu]_?VecIndQ],b___?GLinQ,SupIndex[GMatrix,\[Mu]_?VecIndQ],c___]]]:=Module[{i,l=Length[{b}]},
GReduce[Sum[-2*(-1)^i Dot[a,Sequence@@Delete[{b},i],{b}[[i]],c],{i,1,l}]+(-1)^l MetricTensor[]*GReduce[Dot[a,GIdentity,b,c]]]];
GReduce[a_Plus]:=GReduce/@a;GReduce[a:(_[__])]:=GReduce/@a;GReduce[a_]:=a;
GReduce[HoldPattern[Dot[a___,GHat[p_],GHat[p_],c___]]]:=GReduce[sp[p,p]*Dot[a,GIdentity,c]];
GReduce[HoldPattern[Dot[a___,GHat[p_],b___?GLinQ,GHat[p_],c___]]]:=Module[{i,l=Length[{b}]},
GReduce[Sum[-2*(-1)^i GTrace[GHat[p] . {b}[[i]]]*Dot[a,Sequence@@Delete[{b},i],GHat[p],c],{i,1,l}]+(-1)^l sp[p,p]*Dot[a,b,GIdentity,c]]]



GMPat=GIdentity|GMatrix|GHat|Gamma5;


GDistribute[expr_]:=Module[{ex,dot,fl,factor},
factor=(fl=Times@@Power@@@DeleteCases[FactorList[#],_?(FreeQ[#,GMPat]&)];
{Together[#/fl],fl})&;
ex=FixedPoint[(#/.Dot->dot/.dt_dot:>Distribute[dt]/.dot[a__]:>((Times@@#[[1]])(dot@@#[[2]])&[Transpose[factor/@{a}]])/.dot->Dot)&,expr]
]


GTrace[expr_]:=GDistribute[expr]/.Dot->gtrace


gtrace[a__]/;FreeQ[{a},Gamma5]&&OddQ[Length[{a}]]=0;
gtrace[]=1;
gtrace[a:(SupIndex|SubIndex)[GMatrix,_],b:(SupIndex|SubIndex)[GMatrix,_]]:=MetricTensor[Last/@Cases[{a,b},_SupIndex],Last/@Cases[{a,b},_SubIndex]]
gtrace[a:(SupIndex|SubIndex)[GMatrix,_],GHat[b_]]:=ReplacePart[a,1->b]
gtrace[GHat[a_],b:(SupIndex|SubIndex)[GMatrix,_]]:=ReplacePart[b,1->a]
gtrace[GHat[a_],GHat[b_]]:=sp[a,b]
gtrace[a_,b1_,bs__]:=Sum[(-1)^(i+1)*gtrace[a,{b1,bs}[[i]]]gtrace@@Delete[{b1,bs},i],{i,Length[{b1,bs}]}]


(* ::Input:: *)
(**)
(*GTrace[x_Plus]:=GTrace/@x;*)
(*GTrace[x_?(FreeQ[#,GMPat]&)*y_]:=x*GTrace[y];*)
(*GTrace[GIdentity]=1;*)
(*GTrace[((SubIndex|SupIndex)[GMatrix,_])|GHat[_]]=0;*)
(*GTrace[(a:((SubIndex|SupIndex)[GMatrix,_])) . (b:((SubIndex|SupIndex)[GMatrix,_]))]:=MetricTensor[(#[[2]])&/@Cases[{a,b},_SupIndex],(#[[2]])&/@Cases[{a,b},_SubIndex]];*)
(*GTrace[SupIndex[GMatrix,a_] . SupIndex[GMatrix,b_]]:=MetricTensor[{a,b},{}];*)
(*GTrace[SubIndex[GMatrix,a_] . SubIndex[GMatrix,b_]]:=MetricTensor[{},{a,b}];*)
(*GTrace[SupIndex[GMatrix,a_] . SubIndex[GMatrix,b_]]:=MetricTensor[{a},{b}];*)
(*GTrace[SubIndex[GMatrix,b_] . SupIndex[GMatrix,a_]]:=MetricTensor[{a},{b}];*)
(*GTrace[(GHat[a_] . (b:((SubIndex|SupIndex)[GMatrix,_])))|((b:((SubIndex|SupIndex)[GMatrix,_])) . GHat[a_])]:=ReplacePart[b,a,1];*)
(*GTrace[GHat[a_] . GHat[b_]]:=sp[a,b];*)
(*pair[SupIndex[GMatrix,a_],SupIndex[GMatrix,b_]]:=MetricTensor[{a,b},{}];*)
(*pair[SubIndex[GMatrix,a_],SubIndex[GMatrix,b_]]:=MetricTensor[{},{a,b}];*)
(*pair[SupIndex[GMatrix,a_],SubIndex[GMatrix,b_]]:=MetricTensor[{a},{b}];*)
(*pair[SubIndex[GMatrix,b_],SupIndex[GMatrix,a_]]:=MetricTensor[{a},{b}];*)
(*pair[GHat[a_],(b:((SubIndex|SupIndex)[GMatrix,_]))]:=ReplacePart[b,a,1]*)
(*pair[(b:((SubIndex|SupIndex)[GMatrix,_])),GHat[a_]]:=ReplacePart[b,a,1];*)
(*pair[GHat[a_],GHat[b_]]:=sp[a,b];*)
(*GTrace[a:HoldPattern[Dot[(((SubIndex|SupIndex)[GMatrix,_])|GHat[_])..]]]:=*)
(*  If[OddQ@Length@a,0,Sum[(-1)^i pair[a[[1]],a[[i]]]*GTrace[Delete[a,{{1},{i}}]],{i,2,Length[a]}]]*)


(* ::Input:: *)
(*GTrace[a_Dot]:=GTrace[b]/;a=!=(b=LFDistribute[a,Dot])*)


SetLinear[gTrace,All];


Options[FORMTraces]={Run->True};


(* ::Text:: *)
(*To do: make FORMTraces work with traces that evaluate to expression containing metric tensor.*)


FORMTraces[ex_,OptionsPattern[]]:=Module[{
dim=MetricTensor[],dr,
symbols,sr,
vectors=Union[Cases[ex,_?VecVarQ,-1]],vr,
indices=Union[Cases[ex,_?VecIndQ,-1]],ir,
sps,
g,d,
ext,ids,k,
declare,gt,
program,
mt=Unique["mt"]
},
dr = dim -> Unique["d"];
sps=Union[Flatten@Outer[Sort@{##}->sp[##]&,vectors,vectors]];
symbols=Union[Cases[{ex,Last/@sps,dim},_?NumVarQ,-1]];
sr=Thread[symbols->Table[Unique["s"],{Length@symbols}]];
vr=Thread[vectors->Table[Unique["v"],{Length@vectors}]];
ir=Thread[indices->Table[Unique["i"],{Length@indices}]];
declare=If[#2==={},"",#1<>" "<>StringRiffle[Last/@#2,","]<>";\n"]&;
k=0;
ext=LFDistribute[ex/.{gTrace[x_]:>1/4 gt[++k,x]},GHat|SupIndex|SubIndex|sp];
(*<--- each trace is numbered,todo: powers of traces are processed wrongly*)
ext=StringReplace[StringReplace[ToString[ext/.{gt[k_,exp_]:>(exp/.sr/.vr/.ir/.{GIdentity->g[k],GHat[p_]:>g[k,p],(SubIndex|SupIndex)[GMatrix, j_]:>g[k,j],
(SubIndex|SupIndex)[v_?VecVarQ, j_]:>v[j]}/.Dot->NonCommutativeMultiply)}/.{(SupIndex|SubIndex)[p_,j_]:>d[p,j],MetricTensor[i_,j_]:>d@@Join[i,j]}/.sr/.vr/.ir,InputForm],{ToString[g]<>"["~~args:Except["]"]..~~"]":>"g_("<>args<>")",ToString[d]<>"["~~args:Except["]"]..~~"]":>"d_("<>args<>")","sp["~~arg1:Except[","]..~~","~~arg2:Except["]"]..~~"]":>"("<>arg1<>"."<>arg2<>")"}],{"**"->"*"," "->""}];
ids=StringReplace[StringRiffle[Join["id "<>StringRiffle[ToString[#,InputForm]&/@#1,"."]<>" = "<> ToString[#2,InputForm]&@@@(DeleteCases[sps,(l_->s_)/;l===List@@s] /.sr/.vr/.ir),"id "<>ToString[#,InputForm]<>" = "<> ToString[#2,InputForm]&@@@(DeleteCases[{(dim/.dr)->(dim/.sr)},(l_->l_)])],";\n"],
{ToString[g]<>"["~~args:Except["]"]..~~"]":>"g_("<>args<>")",ToString[d]<>"["~~args:Except["]"]..~~"]":>"d_("<>args<>")","sp["~~arg1:Except[","]..~~","~~arg2:Except["]"]..~~"]":>StringReplace["("<>arg1<>"."<>arg2<>")"," ":>""]}];
program="* NOTATIONS:
* "<>StringRiffle[ToString[Reverse@#,InputForm]&/@Join[sr,vr,ir],"\n* "]<>"
* START:
Dimension "<>ToString[dim/.dr]<>";\n"<>
declare["Symbols",sr]<>
declare["Vectors",vr]<>
"Vectors vp1,vp2;\n"<>
declare["Indices",ir]<>
"Indices ip1,ip2;\n"<>
"CF sp, SupIndex, "<>ToString[mt,InputForm]<>";
Local expression = "<>ext<>";
"<>StringRiffle[Array["tracen,"<>ToString[#]&,k],";\n"]<>";
"<>ids<>";
id vp1?.vp2? = sp(vp1,vp2);
id vp1?(ip1?) =SupIndex(vp1,ip1);
id d_(ip1?,ip2?) ="<>ToString[mt,InputForm]<>"(ip1,ip2);
"<>".sort
Format Mathematica;
Format NoSpaces;
Format 255;
#write<"<>$GMatricesFORMTempDir<>"result.m>\"(%E)\",expression;
.end";
Quiet[DeleteFile[$GMatricesFORMTempDir<>"program.frm"]];
Quiet[DeleteFile[$GMatricesFORMTempDir<>"result.m"]];
WriteString[$GMatricesFORMTempDir<>"program.frm",program];
Close[$GMatricesFORMTempDir<>"program.frm"];
If[OptionValue[Run]===False,Return[$GMatricesFORMTempDir<>"program.frm"]];
RunProcess[{"form",$GMatricesFORMTempDir<>"program.frm"}];
Get[$GMatricesFORMTempDir<>"result.m"]/.(Reverse/@sr)/.(Reverse/@vr)/.(Reverse/@ir)/.mt->(MetricTensor[{##},{}]&)
]


End[];


EndPackage[];
