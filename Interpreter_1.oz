%===================================================================%
%%% Author:
%%%   Rodrigo Botero Ibarra <rbotero001@gmail.com>
%%%
%%% Copyright:
%%%   Rodrigo Botero Ibarra, 2022
%===================================================================%
declare
%-------------------------------------------------------------------%
%% From CTM, Van Roy and Haridi, 2004, pag. 773: Solve function.
% Returns the list of solutions of Script given by a lazy
% depth-first exploration
fun {Solve Script}
   {SolveStep {Space.new Script} nil}
end
% Returns the list of solutions of S appended with SolTail
fun {SolveStep S SolTail}
   case {Space.ask S}
   of failed          then SolTail
   [] succeeded       then {Space.merge S}|SolTail
   [] alternatives(N) then {SolveLoop S 1 N SolTail}
   end
end
% Lazily explores the alternatives I through N of space S,
% and returns the list of solutions found, appended with
% SolTail
fun lazy {SolveLoop S I N SolTail}
   if I>N then SolTail
   elseif I==N then {Space.commit S I} {SolveStep S SolTail}
   else
      C={Space.clone S} NewTail={SolveLoop S I+1 N SolTail} in
      {Space.commit C I}
      {SolveStep C NewTail}
   end
end
%-------------------------------------------------------------------%
%% From CTM, Van Roy and Haridi, 2004, pag. 626: SolveOne function.
fun {SolveOne F} L={Solve F} in
   if L==nil then nil else [L.1] end
end
%===================================================================%
%% In the procedure 'VarsCycle': LV is a list of variables and RC an empty
%% record. LV should be a list in the form [Atom1 Atom2 ... AtomN '(' ...],
%% where Atom1 through AtomN are pairwise distinct. If two or more atoms are
%% equal, only the first one is placed in the record of variables 'vars'. The
%% output of the procedure 'VarsCycle' is the tuple R=vars(Atom1 Atom2 ...
%% AtomN-1)#Lr, where Lr=[AtomN '(' ...] is the remaining list from LV.
fun {CEquals X Y} case X#Y of X#X then true else false end end
proc {IsInTuple Rec V R} %% Asks whether V is in the record Rec.
   if {Record.width Rec}>0 then
      L={Record.foldR Rec fun {$ X Xr} X|Xr end nil}
      R1=for I in L sum:S do if {CEquals I V} then {S 1} else skip end end in
      R=if R1>0 then true else false end
   else R=false
   end
end
proc {VarsCycle LV RC N R} R2 in
   case LV
   of V1|'('|_ andthen {IsAtom V1} then R=RC#LV
   [] domain|_ then R=RC#LV
   [] 'in'|_ then R=RC#LV
   [] V1|L1 andthen {IsAtom V1} then
      if {IsInTuple RC V1}==false
      then {Record.adjoinAt RC N V1 R2} {VarsCycle L1 R2 N+1 R}
      elseif {IsInTuple RC V1}
      then {VarsCycle L1 RC N R}
      else skip
      end
   else raise error_in_List_ofAtoms(LV) end
   end
end
proc {DomCycle LD RD N X R} D1 D2 R2 in
   choice
      LD=']'|D1 X=D1 R=RD
   [] D2={IsATuple LD D1} {Record.adjoinAt RD N D2 R2} {DomCycle D1 R2 N+1 X R}
   end
end
proc {SumCycle LS RS N X R} L1 P1 R2 in
   choice
      LS=')'|L1 X=L1 R=RS
   [] P1={IsIdent LS L1} {Record.adjoinAt RS N P1 R2} {SumCycle L1 R2 N+1 X R}
   [] P1={IsATuple LS L1} {Record.adjoinAt RS N P1 R2} {SumCycle L1 R2 N+1 X R}
   [] P1={IsSum LS L1} {Record.adjoinAt RS N P1 R2} {SumCycle L1 R2 N+1 X R}
   [] P1={IsTout LS L1} {Record.adjoinAt RS N P1 R2} {SumCycle L1 R2 N+1 X R}
   end
end
proc {ParCycle LS RS N X R} L1 P1 R2 in
   choice
      LS=')'|L1 X=L1 R=RS
   [] P1={IsIdent LS L1} {Record.adjoinAt RS N P1 R2} {ParCycle L1 R2 N+1 X R}
   [] P1={IsAgent LS L1} {Record.adjoinAt RS N P1 R2} {ParCycle L1 R2 N+1 X R}
   end
end

%===================================================================%
%% Adapted from CTM, Van Roy and Haridi, 2004, pag. 643, Section 9.4.1:
%% A simple grammar.
fun {NGR X}
   X\='(' andthen X\=')' andthen X\='['
   andthen X\=']' andthen X\='{' andthen X\='}'
end
fun {IsATuple X0 X} P1 P2 X1 X2 X3 in
   choice
      P1={IsInteg X0 X1} X1='#'|X2 P2={IsInteg X2 X} '#'(P1 P2)
   [] P1={IsBool X0 X1}  X1='#'|X2 P2={IsIdent X2 X} '#'(P1 P2)
   [] P1={IsBool X0 X1}  X1='#'|X2 P2={IsAgent X2 X} '#'(P1 P2)
   [] P1={IsIdent X0 X1} X1='#'|X2 P2={IsIdent X2 X} '#'(P1 P2)
   [] P1={IsConst X0 X1} X1='#'|X2 X3={IsAgent X2 X} '#'(P1 X3)
   end
end
fun {IsInteg X0 X} N in
   X0=N|X
   if {IsInt N}
   then int(N)
   else X0=X
   end
end
fun {IsBool X0 X} B in
   X0=B|X
   if B == 'true' orelse B == 'false'
   then bool(B)
   else X0=X
   end
end
fun {IsIdent X0 X} V in
   X0=V|X
   if {IsAtom V} andthen {NGR V} andthen V\=omit andthen V\=abort
      andthen V\='true' andthen V\='false'
   then var(V)
   else X0=X
   end
end
fun {IsVars X0 X}
   R={VarsCycle X0 {Record.make vars nil} 1} in
   X=R.2 R.1
end
fun {IsADom X0 X}
   {DomCycle X0 {Record.make doms nil} 1 X}
end
fun {IsFact X0 X} F1 in
   choice
      F1={IsInteg X0 X}
   [] F1={IsIdent X0 X}
   end
   F1
end
fun {IsTerm X0 X} X1 X2 T1 T2 in
   T1={IsFact X0 X1}
   choice
      X1 = '*'|X2 T2={IsFact X2 X} '*'(T1 T2)
   [] X1 = '/'|X2 T2={IsFact X2 X} '/'(T1 T2)
   [] X1 = X T1
   end
end
fun {IsExpr X0 X} X1 X2 E1 E2 in
   E1={IsTerm X0 X1}
   choice
      X1 = '+'|X2 E2={IsTerm X2 X} '+'(E1 E2)
   [] X1 = '-'|X2 E2={IsTerm X2 X} '-'(E1 E2)
   [] X1 = X E1
   end
end
fun {IsComp X0 X} C1 C2 X1 X2 in
   C1={IsExpr X0 X1}
   choice
      X1 = '=='|X2 C2={IsExpr X2 X} '=='(C1 C2)
   [] X1 = '/='|X2 C2={IsExpr X2 X} '!='(C1 C2)
   [] X1 = '>='|X2 C2={IsExpr X2 X} '>='(C1 C2)
   [] X1 = '=<'|X2 C2={IsExpr X2 X} '=<'(C1 C2)
   [] X1 =  '>'|X2 C2={IsExpr X2 X}  '>'(C1 C2)
   [] X1 =  '<'|X2 C2={IsExpr X2 X}  '<'(C1 C2)
   [] X1 = X C1
   end
end
fun {IsConst X0 X} X1 X2 X3 in %% Constraint.
   X0='('|X1
   choice
      X2={IsBool X1 X3} X3=')'|X
   [] X2={IsComp X1 X3} X3=')'|X
   end
   X2
end
fun {IsEqual X0 X} E1 E2 X1 X2 X3 X4 in
   X0='('|X1
   choice
      E1={IsIdent X1 X2} X2='='|X3 E2={IsBool X3 X4} X4=')'|X '='(E1 E2)
   [] E1={IsIdent X1 X2} X2='='|X3 E2={IsExpr X3 X4} X4=')'|X '='(E1 E2)
   [] E1={IsExpr X1 X2} X2='='|X3 E2={IsExpr X3 X4} X4=')'|X '='(E1 E2)
   end
end
fun {IsSum X0 X} P1 X1 X2 X3 X4 in
   choice
      X0=when|X1 P1={IsBool X1 X2} X2='do'|X3 X4={PProcess X3 X} '#'(P1 X4)
   [] X0=when|X1 P1={IsConst X1 X2} X2='do'|X3 X4={PProcess X3 X} '#'(P1 X4)
   end
end
fun {IsTout X0 X} P1 X1 X2 X3 X4 in
   choice
      X0=unless|X1 P1={IsBool X1 X2} X2=next|X3 X4={PProcess X3 X} '#'(P1 X4)
   [] X0=unless|X1 P1={IsConst X1 X2} X2=next|X3 X4={PProcess X3 X} '#'(P1 X4)
   end
end
%-------------------------------------------------------------------%
fun {PTell X0 X} P1 in
   choice
      P1={IsEqual X0 X}
   [] P1={IsConst X0 X}
   end P1
end
fun {PNext X0 X} E1 X1 X2 X3 X4 in
   X0='('|X1
   choice
      E1={IsInteg X1 X2} X3={IsIdent X2 X4} X4=')'|X next(E1 X3)
   [] E1={IsInteg X1 X2} X3={IsAgent X2 X4} X4=')'|X next(E1 X3)
   [] X3={IsIdent X1 X4} X4=')'|X next(X3)
   [] X3={IsAgent X1 X4} X4=')'|X next(X3)
   end
end
fun {PSum Label X0 X} P1 P2 X1 X2 RC={Record.make Label nil} in
   X0='('|X1
   choice
      P1={IsIdent X1 X2} P2={SumCycle X2 {Record.adjoinAt RC 1 P1} 2 X}
   [] P1={IsATuple X1 X2} P2={SumCycle X2 {Record.adjoinAt RC 1 P1} 2 X}
   [] P1={IsSum X1 X2} P2={SumCycle X2 {Record.adjoinAt RC 1 P1} 2 X}
   [] P1={IsTout X1 X2} P2={SumCycle X2 {Record.adjoinAt RC 1 P1} 2 X}
   end
end
fun {PPar Label X0 X} P1 P2 X1 X2 RC={Record.make Label nil} in
   X0='('|X1
   choice
      P1={IsIdent X1 X2} P2={ParCycle X2 {Record.adjoinAt RC 1 P1} 2 X}
   [] P1={IsAgent X1 X2} P2={ParCycle X2 {Record.adjoinAt RC 1 P1} 2 X}
   end
end
fun {PStrBng Label X0 X} S1 S2 X1 X2 X3 X4 X5 in
   X0='('|X1
   choice
      S1={IsExpr X1 X2} S2={IsExpr X2 X3} X4={IsAgent X3 X5}
      X5=')'|X Label(S1 S2 X4)
   [] S1={IsExpr X1 X2} X3={IsAgent X2 X4} X4=')'|X Label(S1 X3)
   [] X3={IsAgent X1 X4} X4=')'|X Label(X3)
   end
end
fun {PLocal X0 X} A1 X1 X2 X3 X4 in
   X0='('|X1
   choice
      A1={IsVars X1 X2} X3={IsAgent X2 X4} X4=')'|X hide(A1 X3)
   end
end
%-------------------------------------------------------------------%
proc {IsAgent X0 X R} A1 X1 X2 X3 X4 in
   R=choice
	X0 = tell|X1 A1={PTell X1 X} tell(A1)        %% Tell
     [] X0 = when|X1                                 %% When
	A1={IsConst X1 X2} X2='do'|X3 X4={PProcess X3 X} when(A1 X4)
     [] X0 = unless|X1                               %% Unless
	A1={IsConst X1 X2} X2=next|X3 X4={PProcess X3 X} unless(A1 X4)
     [] X0 = sum|X1       X2={PSum sum X1 X}         %% Summation
     [] X0 = sum|X1 X1='('|X2 X2=0|X3 X3=')'|X sum(0)
     [] X0 = par|X1       X2={PPar par X1 X}         %% Parallel
     [] X0 = next|X1      X2={PNext X1 X}            %% Next, Next^N
     [] X0 = hide|X1      X2={PLocal X1 X}           %% Local
     [] X0 = star|X1      X2={PStrBng star X1 X}     %% Asynchrony, Eventualyty
     [] X0 = bang|X1      X2={PStrBng bang X1 X}     %% Replication, Invariance
     [] X0 = tout|X1      X2={PSum tout X1 X}        %% Non-determi. Time-Out
     [] X0 = async|X1     X2={PPar async X1 X}       %% Asynchronous Parallel
     [] X0 = omit|X1      X1=X omit                  %% Skip
     [] X0 = abort|X1     X1=X abort                 %% Abort
     end
end
%-------------------------------------------------------------------%
fun {Junction X0 X} J1 J2 X1 X2 in
   choice
      J1={IsConst X0 X1} X1='and'|X2 J2={IsConst X2 X} 'and'(J1 J2)
   [] J1={IsConst X0 X1} X1='or'|X2 J2={IsConst X2 X} 'or'(J1 J2)
   [] J1={IsConst X0 X} J1
   end
end
fun {Conditional X0 X} I1 X1 X2 X3 X4 X5 X6 X7 X8 in % Revisar
   X0='if'|X1
   choice
      I1={Junction X1 X2} X2='then'|X3 X4={Process X3 X5} X5='end'|X
      'if'(I1 X4)
   [] I1={Junction X1 X2} X2='then'|X3 X4={Process X3 X5} X5='else'|X6
      X7={Process X6 X8} X8='end'|X 'if'(I1 X4 X7)
   end
end
fun {PFunction X0 X} F1 F2 X1 X2 X3 X4 X5 X6 X7 X8 X9 in % Definir
   X0='fun'|X1
   choice
      X1='{'|X2 X2='$'|X3 F1={IsIdent X3 X4} X4='}'|X5
      X6={IsAgent X5 X7} X7='end'|X 'fun'(F1 X6)
   [] X1='{'|X2 X2='$'|X3 F1={IsIdent X3 X4} F2={IsIdent X4 X5} X5='}'|X6
      X7={IsAgent X6 X8} X8='end'|X 'fun'(F1 F2 X7)
   [] X1=lazy|X2 X2='{'|X3 X3='$'|X4 F1={IsIdent X4 X5} X5='}'|X6
      X7={IsAgent X6 X8} X8='end'|X 'lazy'(F1 X7)
   [] X1=lazy|X2 X2='{'|X3 X3='$'|X4 F1={IsIdent X4 X5} F2={IsIdent X5 X6}
      X6='}'|X7 X8={IsAgent X7 X9} X9='end'|X 'lazy'(F1 F2 X8)
   [] X1='{'|X2 X2='$'|X3 F1={IsIdent X3 X4} X4='}'|X5
      X6={Conditional X5 X7} X7='end'|X 'fun'(F1 X6)
   [] X1=lazy|X2 X2='{'|X3 X3='$'|X4 F1={IsIdent X4 X5} X5='}'|X6
      X7={Conditional X6 X8} X8='end'|X 'lazy'(F1 X7)
   end
end
fun {IsAssign X0 X} P1 X1 X2 X3 in
   P1={IsIdent X0 X1} X1=':='|X2 X3={IsExpr X2 X} assig(P1 X3) %% Cell assig.
end
fun {Process X0 X} X1 in
   choice
      X1={IsAgent X0 X}
   [] X1={PFunction X0 X}
   [] X1={IsAssign X0 X}
   [] X1={IsIdent X0 X}
   end
   X1
end
fun {PProcess X0 X} P1 X1 X2 X3 in
   choice
      P1={IsIdent X0 X1} X1='='|X2 X3={IsAgent X2 X} def(P1 X3)
   [] P1={IsIdent X0 X1} X1='='|X2 X3={PFunction X2 X} def(P1 X3)
   [] P1={IsIdent X0 X1} X1='='|X2 X3={IsIdent X2 X} fail %% p = q No definido.
   [] P1={IsIdent X0 X1} X1='='|X2 X3={IsAssign X2 X} def(P1 X3)
   [] X1={Process X0 X} X1
   end
end
fun {Parallel X0 X} X1 X2 X3 X4 in
   choice
      X1={PProcess X0 X2} X2=';'|X3 X4={Parallel X3 X} par(X1 X4)
   [] X1={PProcess X0 X} X1
   end
end
%-------------------------------------------------------------------%
fun {Program X0 X} D1 I1 P1 V1 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12 in
   X0='NtccSim'|X1 X1=begin|X2 X2='declare'|X3 V1={IsVars X3 X4} X4=domain|X5
   X5='='|'['|X6 D1={IsADom X6 X7} X7=tsim|X8 X8='='|X9
   I1={IsInteg X9 X10} X10='in'|X11 P1={Parallel X11 X12} X12='end'|X
   prog(V1 D1 tsim(I1) sim(P1))
end
%===================================================================%

%===================================================================%
% Some Examples:
%-------------------------------------------------------------------%
%{Browse 'IsInteg'#{IsInteg [0] _}}
%{Browse 'IsBool'#{IsBool ['true'] _}}
% {Browse 'IsIdent'#{IsIdent [x '==' 0] _}}
%-------------------------------------------------------------------%
% {Browse 'IsUnless'#{SolveOne fun {$} {IsUnless [unless '(' x '==' 0 ')' next tell '(' x '=' 0 ')'] _} end}}
% {Browse 'IsFact'#{SolveOne fun {$} {IsFact [0] _} end}}
% {Browse 'IsATuple'#{SolveOne fun {$} {IsATuple [a '#' b] _} end}}
% {Browse 'IsATuple'#{SolveOne fun {$} {IsATuple ['(' x '==' 0 ')' '#' tell '(' x '=' 0 ')'] _} end}}
% {Browse 'IsTerm'#{SolveOne fun {$} {IsTerm [2 '*' a] _} end}}
% {Browse 'IsExpr1'#{SolveOne fun {$} {IsExpr [2 '*' a '+' b '/' 0] _} end}}
% {Browse 'IsExpr2'#{SolveOne fun {$} {IsExpr [a '+' b '/' 0] _} end}}
% {Browse 'IsExpr3'#{SolveOne fun {$} {IsExpr [2 '*' a '+' b] _} end}}
% {Browse 'IsExpr4'#{SolveOne fun {$} {IsExpr [2 '+' b] _} end}}
% {Browse 'IsExpr5'#{SolveOne fun {$} {IsExpr ['false'] _} end}}
% {Browse 'IsComp1'#{SolveOne fun {$} {IsComp ['(' 2 '+' b '==' a ')'] _} end}}
% {Browse 'IsComp2'#{SolveOne fun {$} {IsComp ['(' b '>=' a ')'] _} end}}
% {Browse 'IsComp3'#{SolveOne fun {$} {IsComp ['(' 'true' ')'] _} end}}
%{Browse 'IsConst1'#{SolveOne fun {$} {IsConst ['(' 'true' ')'] _} end}}
%{Browse 'IsConst2'#{SolveOne fun {$} {IsConst ['(' x '==' 0 ')'] _} end}}
%{Browse 'IsConst3'#{SolveOne fun {$} {IsConst ['(' 2 '*' 2 '+' b '==' a '+' 1')'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'IsAgent0'#{SolveOne fun {$} {IsAgent [tell '(' 'true' ')'] _} end}}
%{Browse 'IsAgent1a'#{SolveOne fun {$} {IsAgent [tell '(' x '==' 0 ')'] _} end}}
%{Browse 'IsAgent1b'#{SolveOne fun {$} {IsAgent [tell '(' a '+' 2 '=' 15 ')'] _} end}}
%{Browse 'IsAgent2'#{SolveOne fun {$} {IsAgent [when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')'] _} end}}
% {Browse 'IsAgent3'#{SolveOne fun {$} {IsAgent [unless '(' x '==' 0 ')' next tell '(' x '==' 0 ')'] _} end}}
% {Browse 'IsAgent4'#{SolveOne fun {$} {IsAgent [next '(' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent5'#{SolveOne fun {$} {IsAgent [next '(' 1 when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent6'#{SolveOne fun {$} {IsAgent [next '(' a when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent6a'#{SolveOne fun {$} {IsAgent [next '(' a ')'] _} end}}
% {Browse 'IsAgent7'#{SolveOne fun {$} {IsAgent [next '(' a '+' 1 when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent8'#{SolveOne fun {$} {IsAgent [par '(' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent9'#{SolveOne fun {$} {IsAgent [par '(' sum '(' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')' tell '(' x '==' 0 ')' ')'] _} end}}
%{Browse 'IsAgent10'#{SolveOne fun {$} {IsAgent [hide '(' a when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')'')'] _} end}}
% {Browse 'IsAgent11'#{SolveOne fun {$} {IsAgent [star '(' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent12'#{SolveOne fun {$} {IsAgent [star '(' 1 when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent13'#{SolveOne fun {$} {IsAgent [star '(' a when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent14'#{SolveOne fun {$} {IsAgent [star '(' a '+' 1 when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent15'#{SolveOne fun {$} {IsAgent [star '(' 1 a '+' 1 when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent16'#{SolveOne fun {$} {IsAgent [star '(' b '*' 2 a '+' 1 when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent17'#{SolveOne fun {$} {IsAgent [bang '(' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent18'#{SolveOne fun {$} {IsAgent [bang '(' 1 when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent19'#{SolveOne fun {$} {IsAgent [bang '(' a when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent20'#{SolveOne fun {$} {IsAgent [bang '(' a '+' 1 when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent21'#{SolveOne fun {$} {IsAgent [bang '(' 1 a '+' 1 when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent22'#{SolveOne fun {$} {IsAgent [bang '(' b '*' 2 a '+' 1 when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent23'#{SolveOne fun {$} {IsAgent [par '(' b a ')'] _} end}}
% {Browse 'IsAgent24a'#{SolveOne fun {$} {IsAgent [par '(' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent24b'#{SolveOne fun {$} {IsAgent [par '(' par '(' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' sum '(' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')' sum '(' when '(' x '==' 0 ')' 'do' next '(' tell '(' x '==' 1 ')' ')' when '(' x '==' 1 ')' 'do' next '(' tell '(' x '==' 0 ')' ')' when '(' x '==' a ')' 'do' next '(' tell '(' x '==' b ')' ')' ')' par '(' par '(' b a ')' ')' ')'] _} end}}
% {Browse 'IsAgent25'#{SolveOne fun {$} {IsAgent [sum '(' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent26a'#{SolveOne fun {$} {IsAgent [sum '(' when '(' x '==' 0 ')' 'do' next '(' tell '(' x '==' 1 ')' ')' when '(' x '==' 1 ')' 'do' next '(' tell '(' x '==' 0 ')' ')' when '(' x '==' a ')' 'do' next '(' tell '(' x '==' b ')' ')' ')'] _} end}}
% {Browse 'IsAgent26b'#{SolveOne fun {$} {IsAgent [par '(' sum '(' when '(' x '==' 0 ')' 'do' next '(' tell '(' x '==' 1 ')' ')' when '(' x '==' 1 ')' 'do' next '(' tell '(' x '==' 0 ')' ')' when '(' x '==' a ')' 'do' next '(' tell '(' x '==' b ')' ')' ')' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent26c'#{SolveOne fun {$} {IsAgent [par '(' sum '(' when '(' x '==' 0 ')' 'do' next '(' tell '(' x '==' 1 ')' ')' when '(' x '==' 1 ')' 'do' next '(' tell '(' x '==' 0 ')' ')' when '(' x '==' a ')' 'do' next '(' tell '(' x '==' b ')' ')' ')' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' sum '(' when '(' x '==' 0 ')' 'do' next '(' tell '(' x '==' 1 ')' ')' when '(' x '==' 1 ')' 'do' next '(' tell '(' x '==' 0 ')' ')' when '(' x '==' a ')' 'do' next '(' tell '(' x '==' b ')' ')' ')' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent26d'#{SolveOne fun {$} {IsAgent [par '(' sum '(' '(' x '==' 0 ')''#' next '(' tell '(' x '==' 1 ')' ')' '(' x '==' 1 ')' '#' next '(' tell '(' x '==' 0 ')' ')' '(' x '==' a ')' '#' next '(' tell '(' x '==' b ')' ')' ')' when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent27a'#{SolveOne fun {$} {IsAgent [hide '(' a when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent27b'#{SolveOne fun {$} {IsAgent [hide '(' a b c when '(' x '==' 0 ')' 'do' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent28'#{SolveOne fun {$} {IsAgent [omit] _} end}}
% {Browse 'IsAgent29'#{SolveOne fun {$} {IsAgent [abort] _} end}}
% {Browse 'IsAgent30a'#{SolveOne fun {$} {IsAgent [tell '(' x '=' 0 ')'] _} end}}
% {Browse 'IsAgent30b'#{SolveOne fun {$} {IsAgent [tout '(' unless '(' x '==' 0 ')' next tell '(' x '=' 1 ')' unless '(' x '==' 1 ')' next tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent30c'#{SolveOne fun {$} {IsAgent [tout '(' '(' x '==' 0 ')' '#' tell '(' x '=' 1 ')' '(' x '==' 1 ')' '#' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent30d'#{SolveOne fun {$} {IsAgent [tout '(' '(' 'true' ')' '#' tell '(' x '=' 1 ')' '(' x '==' 1 ')' '#' tell '(' x '==' 0 ')' ')'] _} end}}
% {Browse 'IsAgent30e'#{SolveOne fun {$} {IsAgent [tell '(' x '=' 'true' ')'] _} end}}
% {Browse 'IsAgent30c'#{SolveOne fun {$} {IsAgent [async '(' when '(' x '==' 1 ')' 'do' next '(' tell '(' x '==' 0 ')' ')' when '(' x '==' 0 ')' 'do' next '(' tell '(' x '==' 1 ')' ')' when '(' x '==' 2 ')' 'do' next '(' tell '(' x '==' 2 ')' ')' ')'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Parallel1'#{SolveOne fun {$} {Parallel [p1] _} end}}
%{Browse 'Parallel2'#{SolveOne fun {$} {Parallel [p1 ';' p2] _} end}}
%{Browse 'Parallel3'#{SolveOne fun {$} {Parallel [p1 ';' p2 ';' p3] _} end}}
%{Browse 'Parallel4'#{SolveOne fun {$} {Parallel [p1 '=' tell '(' x '==' 0 ')' ';' p2] _} end}}
%{Browse 'Parallel5'#{SolveOne fun {$} {Parallel [p1 '=' tell '(' x '==' 0 ')' ';' p '=' q] _} end}} %% p '=' q no esta definido.
%{Browse 'Parallel6'#{SolveOne fun {$} {Parallel [p1 '=' tell '(' x '==' 0 ')' ';' p2 '=' abort] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Junction1'#{SolveOne fun {$} {Junction ['(' a '==' 1 ')' 'or' '(' b '>' 2 ')'] _} end}}
%{Browse 'Junction2'#{SolveOne fun {$} {Junction ['(' a '==' 1 ')' 'and' '(' b '>' 2 ')'] _} end}}
%{Browse 'Junction3'#{SolveOne fun {$} {Junction ['(' 'true' ')'] _} end}}
%{Browse 'Junction4'#{SolveOne fun {$} {Junction ['(' a '==' 1 ')'] _} end}}
%{Browse 'Junction5'#{SolveOne fun {$} {Junction ['(' a '-' 2 '==' 1 ')' 'or' '(' a '==' 1 ')'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Conditional1'#{SolveOne fun {$} {Conditional ['if' '(' a '==' 1 ')' 'or' '(' b '>' 2 ')' 'then' p1 'end'] _} end}}
%{Browse 'Conditional2'#{SolveOne fun {$} {Conditional ['if' '(' a '==' 1 ')' 'then' p1 'else' p2 'end'] _} end}}
%{Browse 'Conditional3'#{SolveOne fun {$} {Conditional ['if' '(' 'true' ')' 'then' p1 'else' p2 'end'] _} end}}
%{Browse 'Conditional4'#{SolveOne fun {$} {Conditional ['if' '(' 'true' ')' 'and' '(' b '>' 2 ')' 'then' p1 'else' p2 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'PFunction1'#{SolveOne fun {$} {PFunction ['fun' '{' '$' f1 '}' tell '(' x '==' 0 ')' 'end'] _} end}}
%{Browse 'PFunction2'#{SolveOne fun {$} {PFunction ['fun' '{' '$' f1 f2 '}' tell '(' x '==' 0 ')' 'end'] _} end}}
%{Browse 'PFunction3'#{SolveOne fun {$} {PFunction ['fun' 'lazy' '{' '$' f1 '}' tell '(' x '==' 0 ')' 'end'] _} end}}
%{Browse 'PFunction4'#{SolveOne fun {$} {PFunction ['fun' 'lazy' '{' '$' f1 f2 '}' tell '(' x '==' 0 ')' 'end'] _} end}}
%{Browse 'PFunction5'#{SolveOne fun {$} {PFunction ['fun' '{' '$' f1 '}' 'if' '(' 'true' ')' 'and' '(' b '>' 2 ')' 'then' p1 'else' p2 'end' 'end'] _} end}}
%{Browse 'PFunction6'#{SolveOne fun {$} {PFunction ['fun' 'lazy' '{' '$' f1 '}' 'if' '(' 'true' ')' 'and' '(' b '>' 2 ')' 'then' p1 'else' p2 'end' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Process1'#{SolveOne fun {$} {Process [p1] _} end}}
%{Browse 'Process2'#{SolveOne fun {$} {Process [abort] _} end}}
%{Browse 'Process3'#{SolveOne fun {$} {Process [tell '(' x '==' 0 ')'] _} end}}
%{Browse 'Process4'#{SolveOne fun {$} {Process ['fun' 'lazy' '{' '$' f1 '}' 'if' '(' 'true' ')' 'and' '(' b '>' 2 ')' 'then' p1 'else' p2 'end' 'end'] _} end}}
%{Browse 'Process5'#{SolveOne fun {$} {PProcess [p1 '=' tell '(' x '==' 0 ')'] _} end}}
%{Browse 'Process6'#{SolveOne fun {$} {PProcess [x1 ':=' x1 '+' 1] _} end}}
%{Browse 'Process7'#{SolveOne fun {$} {PProcess [p1 '=' x1 ':=' x1 '+' 1] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program1'#{SolveOne fun {$} {Program ['NtccSim' 'begin' 'declare' x y z domain '=' '[' 1 '#' 2 3 '#' 4 5 '#' 6 7 '#' 8 ']' tsim '=' 10 'in' p1 '=' tell '(' x '==' 0 ')' ';' p2 '=' tell '(' x '==' 1 ')' ';' p3 '=' tell '(' x '==' 2 ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program2'#{SolveOne fun {$} {Program ['NtccSim' 'begin' 'declare' x y z domain '=' '[' 1 '#' 2 3 '#' 4 5 '#' 6 7 '#' 8 ']' tsim '=' 10 'in' cellx '=' par '(' tell '(' x1 '==' a ')' unless '(' changex ')' next cellx')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program3'#{SolveOne fun {$} {Program ['NtccSim' 'begin' 'declare' x y z domain '=' '[' 1 '#' 2 3 '#' 4 5 '#' 6 ']' tsim '=' 10 'in' p1 '=' 'fun' 'lazy' '{' '$' f1 '}' 'if' '(' 'true' ')' 'and' '(' b '>' 2 ')' 'then' p1 'else' p2 'end' 'end' ';' p2 '=' tell '(' x '==' 0 ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program4'#{SolveOne fun {$} {Program ['NtccSim' 'begin' 'declare' x y z domain '=' '[' 1 '#' 2 3 '#' 4 5 '#' 6 ']' tsim '=' 10 'in' q1 '=' par '(' tell '(' x '==' 1 ')' next '(' hide '(' x par '(' q1 when '(' x '==' 1 ')' 'do' p1 ')' ')' ')' ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program5'#{SolveOne fun {$} {Program ['NtccSim' begin 'declare' w x y z domain '=' '[' 1 '#' 2 3 '#' 4 5 '#' 6 ']' tsim '=' 10 'in' q1 '=' par '(' tell '(' x '==' 1 ')' next '(' hide '(' x y z w par '(' q1 tell '(' x '==' 2 ')' ')' ')' ')' ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program6'#{SolveOne fun {$} {Program ['NtccSim' begin 'declare' a b c d domain '=' '[' 0 '#' 20 0 '#' 30 0 '#' 40 0 '#' 50 ']' tsim '=' 2 'in' par '(' sum '(' when  '(' c '>=' 5 ')' 'do' tell '(' 2 '*' a '<' 15 ')' when '(' b '=<' 8 ')' 'do' tell '(' 2 '*' d '<' 45 ')' when '(' a '=<' 20 ')' 'do' tell '(' 2 '*' d '<' 25 ')' ')' tell '(' a '+' 2 '=' 15 ')' tell '(' b '-' 1 '=' 7 ')' tell '(' c '>=' 5 ')' next '(' tell '(' d '>=' 15 ')' ')' ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program7'#{SolveOne fun {$} {Program ['NtccSim' begin 'declare' a b c d domain '=' '[' 0 '#' 20 0 '#' 30 0 '#' 40 0 '#' 50 ']' tsim '=' 2 'in' t1 '=' tell '(' 2 '*' a '<' 15 ')' ';' when  '(' b '>=' 0 ')' 'do' t1 ';' when '(' a '=<' 7 ')' 'do' tell '(' b '-' 4 '=' 15 ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program8'#{SolveOne fun {$} {Program ['NtccSim' begin 'declare' a b domain '=' '[' 0 '#' 20 0 '#' 30 ']' tsim '=' 5 'in' t1 '=' tell '(' 2 '*' a '<' 15 ')' ';' next '(' 3 tell '(' b '-' 4 '=' 15 ')' ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program9'#{SolveOne fun {$} {Program ['NtccSim' begin 'declare' a b domain '=' '[' 0 '#' 20 0 '#' 30 ']' tsim '=' 5 'in' t1 '=' tell '(' 2 '*' a '<' 15 ')' ';' next '(' 3 t1 ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program10'#{SolveOne fun {$} {Program ['NtccSim' begin 'declare' x y domain '=' '[' 0 '#' 20 0 '#' 20 ']' tsim '=' 2 'in' when '(' y '==' 5 ')' 'do' tell '(' x '<' 10 ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program10'#{SolveOne fun {$} {Program ['NtccSim' begin 'declare' x y domain '=' '[' 0 '#' 20 0 '#' 20 ']' tsim '=' 2 'in' next '(' when '(' y '==' 5 ')' 'do' tell '(' x '<' 10 ')' ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program11'#{SolveOne fun {$} {Program ['NtccSim' begin 'declare' x y z domain '=' '[' 0 '#' 10 0 '#' 10 0 '#' 10 ']' tsim '=' 5 'in' p1 '=' unless '(' x '>' 10 ')' next tell '(' x '-' 1 '==' 3 ')' ';' p2 '=' unless '(' x '<' 10 ')' next tell '(' y '>=' 4 ')' ';' p3 '=' unless '(' y '==' 4 ')' next tell '(' z '<' 7 ')' ';' sum '(' p1 p2 p3 ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program12'#{SolveOne fun {$} {Program ['NtccSim' begin 'declare' x y z domain '=' '[' 0 '#' 10 0 '#' 10 0 '#' 10 ']' tsim '=' 5 'in' p1 '=' unless '(' x '>' 10 ')' next tell '(' x '-' 1 '==' 3 ')' ';' p2 '=' unless '(' x '<' 10 ')' next tell '(' y '>=' 4 ')' ';' p3 '=' unless '(' y '==' 4 ')' next tell '(' z '<' 7 ')' ';' tout '(' p1 p2 p3 ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program12'#{SolveOne fun {$} {Program ['NtccSim' begin 'declare' x y z domain '=' '[' 0 '#' 10 0 '#' 10 0 '#' 10 ']' tsim '=' 5 'in' sum '(' 0 ')' 'end'] _} end}}
%-------------------------------------------------------------------%
%{Browse 'Program12'#{SolveOne fun {$} {Program ['NtccSim' begin 'declare' x y z domain '=' '[' 0 '#' 10 0 '#' 10 0 '#' 10 ']' tsim '=' 5 'in' abort 'end'] _} end}}
%-------------------------------------------------------------------%

