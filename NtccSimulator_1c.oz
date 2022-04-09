%===================================================================%
%%% Author:
%%%   Rodrigo Botero Ibarra <rbotero001@gmail.com>
%%%
%%% Copyright:
%%%   Rodrigo Botero Ibarra, 2022
%===================================================================%
\insert 'Aleatorio.oz'
%-------------------------------------------------------------------%
declare
%-------------------------------------------------------------------%
%% Adapted from the ntccSim simulator by Arbeláez & Gutierrez, 2006.
%% Entrega un 'record' de variables con dominios finitos.
proc {Raiz ListVar Limite V}
   proc {Limites R}
      R=case Limite
	of nil then {FoldR ListVar fun {$ X Xr} 0#FD.sup|Xr end nil}
	else Limite
	end
   end
   fun {IsATuple T} case T of int(_)#int(_) then true else false end end
   proc {IntToTuple T R} case T of int(T1)#int(T2) then R=T1#T2 end end
   LD={List.map {Limites} proc {$ X R}
			  if {IsATuple X} then R={IntToTuple X}
			  else R=X
			  end
		       end} in
   V={Record.make var ListVar}
   case LD
   of _|_ then
      for I in 1..{List.length ListVar} do
	 case {Nth LD I}
	 of _#_ then V.{Nth ListVar I}::{Nth LD I}
	 else V.{Nth ListVar I}::0#{Nth Limite I}
	 end
      end
   else
      V:::0#Limite
   end     
end
%-------------------------------------------------------------------%
%% Adapted from the simulator ntccSim by Arbeláez & Gutierrez, 2006.
proc {CloneVars Rec R}
   R={Record.map Rec
      proc {$ X R} R=if {FD.is X} then {FD.int {FD.reflect.dom X}}
		     else X
		     end
      end}
end
%-------------------------------------------------------------------%
%% Creates a list of proccesses to run in parallel or to run in the next
%% time unit.
proc {CProcList R}
   C={NewCell nil}
   proc {Insert X U} Xr=@C in C:=X|Xr U=unit end
   proc {Get L} L=@C end
   proc {Clear} C:=nil end in
   R=q(insert:Insert get:Get clear:Clear)
end
%-------------------------------------------------------------------%
Q1={CProcList} %% List of proccesses to run in the next time unit.
Q2={CProcList} %% List of proccesses defined by def(V A)=>V#A=var(X)#Proccs.
%-------------------------------------------------------------------%
%% Tests whether X is a record or not.
fun {IsARecord X}
   if {Record.is X} then unit else raise error_NotARecord_in_(X) end end
end
%-------------------------------------------------------------------%
%% Given a list L of tuples in the form V1#V2 this procedure finds the first
%% element V1 that matches V, the result is R=V2 where V2=A#Sc#T.
proc {FindProcc V L R}
   R=case L
     of nil then nil
     [] X|Xr then if X.1==V then X.2#X.3#X.4 else {FindProcc V Xr} end
     end
end
%===================================================================%
%% Adapted from Schulte, 2000. Deref and Ask, pág. 103; Status, pág. 107;
%% and the idea for Encapsulate, pág. 106.
fun {CDeref X}
   case X of suspended(X) then {CDeref X} else X end
end
fun {CEncapsulate Sc G}
   C={Space.merge {Space.clone Sc}} in
   {Space.new proc {$ X}
		 X=C
		 X={if {Procedure.is G} then G else {CGuard G} end}
	      end}
end
fun {CStatus Sc}
   case {CDeref {Space.askVerbose Sc}}
   of failed then failed
   [] succeeded(X) then X
   [] alternatives(_) then stuck
   end
end
fun {CAsk Sc G N} R S1 in
   case G
   of bool('true') then R=entailed
   else S1={CEncapsulate Sc G}
      case {Space.askVerbose S1}
      of suspended(_) then if {Value.isDet N}
			   then if N<1 then R=failed else R={CAsk Sc G N-1} end
			   else R={CAsk Sc G 100}
			   end
      else R={CStatus S1}
      end
   end R
end
%===================================================================%
%% This is the procedure R={CTell Sc C}, where Sc:Space, C:Constraint,
%% R:Result=Status for sinchronization. This procedure just add new
%% information to the store in the form of constraints. Remember, a
%% constraint could be an equality or an inequality.
proc {CTell Sc C R}
   case C
   of omit then raise not_a_constraint(C) end
   [] abort then raise not_a_constraint(C) end
   else case C
	of bool('true') then skip %% Revisar
	[] bool('false') then {Space.inject Sc proc {$ _} fail end}
	else {Space.inject Sc if {Procedure.is C} then C else {CGuard C} end}
	end
        R={CStatus Sc}
   end
end
%-------------------------------------------------------------------%
%% This is the procedure R={CWhen Sc T G P}, where  Sc:Space, T:Time
%% of simulation, G:Guard, P:Processes, and R:Result. The proccess P is
%% executed in the current time unit only if the guard G can be inferred
%% from the store in the current time unit as well.
proc {CWhen Sc T G P R}
   case {CAsk Sc G _}
   of entailed then case {DoAgent Sc T P}
		    of abort then R=abort
		    else R=entailed
		    end
   else R=failed
   end
end
%-------------------------------------------------------------------%
%% This is the procedure R={CUnless Sc T G P}, where  Sc:Space, T:Time
%% of simulation, G:Guard, P:Processes, and R:Result. The proccess P is
%% executed in the next time unit only if the guard G cannot be inferred
%% from the store in the current time unit.
proc {CUnless Sc T G P R}
   case {CAsk Sc G _}
   of failed then {Wait {DoAgent Sc T next(P)}} R=success
   else R=failed
   end
end
%-------------------------------------------------------------------%
%% The proccess 'Hide' corresponds to 'Local', where P should be in the form:
%% hide(X Pr) or hide(vars(X1 X2 X3... XN) Pr), and X's are atoms and Pr is a
%% proccess. Here is how it works: first, the global variables with their
%% current state have been accessed by cloning and merging the space Sc in
%% C1. After that, the domains of the local variables (contained in X) are
%% defined in X1 and then adjoined to C1 in C2. Due to precedence, all
%% new variables in X1 replace the variables in C1, even though they are
%% the same. Now, a new space is created with C2 and the computations
%% included in the agent 'hide' are executed in this space. In C3 the
%% resulting store is accessed via the root variable of S1. Now, the local
%% variables contained in L1 are subtracted from C3, the result is
%% adjoined to the root variable in C1, and then injected into the top
%% level space Sc.
proc {CLocal Sc T P R}
   {Wait {IsARecord P}}
   case P
   of hide(X Pr) then
      C1={Space.merge {Space.clone Sc}} C2 C3 C4 L1 L2 S1 X1 in
      case X
      of vars(...) then L1={Record.toList X} X1={Raiz L1 nil}
      else
	 if {IsAtom X} then X1={Raiz [X] [FD.sup]}
	 else raise error_ReviewVars_in_Hide(X Pr) end
	 end
      end
      C2={Adjoin C1.res X1}
      S1={Space.new proc{$ R} R=store(res:{CloneVars C2}) end}
      {Wait {DoAgent S1 T Pr}}
      C3={Space.merge {Space.clone S1}}
      L2={Record.subtractList C3.res L1}
      C4={Adjoin C1.res L2}
      {Space.inject Sc proc {$ X} X=store(res:C4) end}
   else raise error_ReviewFormat_in_(P) end
   end
   R=unit
end
%-------------------------------------------------------------------%
%% With R={CNext P}, every proccess is executed in the next time unit.
%% If P==next(N P), then the proccess P waits N time units to be executed.
%% For instance, next(1 P)==next(P), waits one time unit to be executed;
%% next(2 P)==next(next(P)) waits two time units to be executed (in the
%% third time unit of the simulation) and so on.
proc {CNext Sc T P R}
   {Wait {IsARecord P}}
   case P
   of next(X) then case X
		   of var(_) then {Wait {CVars X next}}
		   else {Wait {Q1.insert X}}
		   end
   [] next(N X) then N1 in
      case N of int(X) then N1=X else N1=N end
      if N1>1 then case X
		  of var(_) then {Wait {CVars X next(N1)}}
		  else {Wait {Q1.insert next(N1-1 X)}}    %% N next time units.
		  end
      elseif N1==1 then case X
		       of var(_) then {Wait {CVars X next(1)}}
		       else {Wait {Q1.insert X}}          %% Next time unit.
		       end
      else raise error_Review_TimeUnits_in_(P) end
      end
   end
   R=unit
end
%-------------------------------------------------------------------%
%% R={CSum P} is the non-deterministic operator, where GP is a record in
%% the form sum(G1#P1 G2#P2 ... GN#PN). This is how it works: given a
%% record of tuples in the form G#P, where G is a guard and P a proccess,
%% this procedure first selects all the proccesses Pi whose guard can
%% be inferred from the store in the current time unit. Right after that,
%% the procedure choose, non-deterministically, one of the Pi to be
%% executed in the current time unit. If no choice is possible, then the
%% operator precludes. Notice that the non-determinism is simulated by
%% using a random selection of the proccess Pi.
proc {CSum Sc T GP R}
   {Wait {IsARecord GP}}
   case GP
   of sum(0) then R=unit
   else
      GP1={Record.map GP
	   proc {$ X R}
	      R=case X of var(_) then {FindProcc X {Q2.get}}.1 else X end
	   end}
      R0={Record.filter GP1
	  proc {$ X R}
	     R=case X
	       of 'true'#_ then true
	       [] bool('true')#_ then true
	       [] G#_ then
		  case {CAsk Sc G _} of entailed then true else false end
	       [] when(G _) then
		  case G
		  of 'true' then true
		  [] bool('true') then true
		  else case {CAsk Sc G _} of entailed then true else false end
		  end
	       else raise error_NotARecord_in_Sumation(X) end
	       end
	  end} Rw={Record.width R0} in
%      if Rw>0 then R1=R0.{Record.waitOr R0} in % Always selects the first one.
      if Rw>0 then R1 in
	 case Rw
	 of 1 then R1=R0.{Record.waitOr R0}
	 else
%	    A1={OS.rand} mod {Record.width R0} + 1 in % Using Mozart rand. gen.
	    A1={WG} mod Rw + 1 in
	    R1=R0.{Nth {Record.arity R0} A1}
	 end
	 {DoAgent Sc T R1.2 R}
      else R=unit
      end {Wait R}
   end
end
%-------------------------------------------------------------------%
%% R={CPar P} is the parallel composition of proccesses, where P should
%% be in the form par(P1 P2 ... PN). This procedure executes all the
%% proccesses Pi in parallel in the same time unit, although 'tell'
%% proccesses will take precedence over the other proccesses.
proc {CPar Sc T P R} P0 P1 P2 P3 P4 P5 /*Pr*/ in
   {Wait {IsARecord P}}
   if {Record.width P}>0 then
      {Record.partition P proc {$ X R}
			     R=case X of abort then true else false end
			  end P0 P1}
   else raise no_elements_in_P(P) end
   end
   if {Record.width P0}>0 then      % P0 for aborted simulation.
      {Record.forAll P0 proc {$ X} {DoAgent Sc T X R} end}
   else
      R1={CProcList} in
      if {Record.width P1}>0 then
	 {Record.partition P1 proc {$ X R}
				 R=case X
				   of tell(...) then true
				   [] def(...) then true
				   else false
				   end
			      end P2 P3}
      else skip
      end
      if {Record.width P2}>0 then   % P1 for 'tell' and 'def' proccesses.
	 if {List.member abort
	     {Record.foldR P2
	      fun {$ X Xr} thread {DoAgent Sc T X} end|Xr end nil}}
%	     {Record.foldL P2
%	      fun {$ Xr X} thread {DoAgent Sc T X} end|Xr end nil}}
	 then {Wait {R1.insert abort}}
	 else {Wait {R1.insert unit}}
	 end
      else skip
      end
      if {Record.width P3}>0 then
	 {Record.partition P3 proc {$ X R}
				 R=case X
				   of when(...) then true
				   [] unless(...) then true
				   else false
				   end
			      end P4 P5}
      else skip
      end
      if {Value.isDet P4} andthen {Record.width P4}>0 then
	 if {List.member abort      % P4: 'when' and 'unless' proccesses.
	     {Record.foldR P4
	      fun {$ X Xr} thread {DoAgent Sc T X} end|Xr end nil}}
%	     {Record.foldL P4
%	      fun {$ Xr X} thread {DoAgent Sc T X} end|Xr end nil}}
	 then {Wait {R1.insert abort}}
	 else {Wait {R1.insert unit}}
	 end
      else skip
      end
      if {Value.isDet P5} andthen {Record.width P5}>0 then
	 if {List.member abort      % P5 for other proccesses.
	     {Record.foldR P5
	      fun {$ X Xr} thread {DoAgent Sc T X} end|Xr end nil}}
%	     {Record.foldL P5
%	      fun {$ Xr X} thread {DoAgent Sc T X} end|Xr end nil}}
	 then {Wait {R1.insert abort}}
	 else {Wait {R1.insert unit}}
	 end
      else skip
      end
      if {List.member abort {R1.get}} then R=abort else R=unit#{CStatus Sc} end 
   end
end

%-------------------------------------------------------------------%
%% With R={CStar P}, the proccess P will eventually be executed once
%% during the whole simulation time. If P==star(M P), then the proccess
%% P will eventually be executed once, anytime from the time unit M,
%% inclusive. If P==star(M N P), with N>=M and Tsim>=N, the proccess P
%% will eventually be executed once, anytime from the time unit M until
%% the time unit N, inclusive. In any case, the simulation is terminated
%% if no further proccesses remain to be executed in the subsequent
%% time units or if the simulation time is over. Additionally,
%% star(N N P)==next(N-1 P).
proc {CStar Sc T P R}
   {Wait {IsARecord P}}
   case P
   of star(X) then
      case X
      of var(_) then {CVars X star R}
      else A1={WG} mod T + 1 in
	 if A1>1 then {DoAgent Sc T next(A1-1 X) R}
	 else {DoAgent Sc T X R}
	 end
      end
   [] star(M X) then M1 in  %% Bounded eventuality: any point in time from M on.
      case M of int(X) then M1=X else M1=M end
      if M1>=0 andthen M1<T then
	 case X of var(_) then {CVars X star(M1) R}
	 else A1={WG} mod (T-M1+1) + M1 in
	    if A1>1 then {DoAgent Sc T next(A1-1 X) R}
	    else {DoAgent Sc T X R}
	    end
	 end
      else raise error_review_M_and_N_Values end
      end
   [] star(M N X) then M1 N1 in %% Bound. event.: any point in time from M to N.
      case M of int(X) then M1=X else M1=M end
      case N of int(X) then N1=X else N1=N end
      if N1>M1 then
	 if M1>=0 andthen N1>0 andthen M1<T andthen N1=<T then
	    case X of var(_) then {CVars X star(M1 N1) R}
	    else A1={WG} mod (N1-M1+1) + M1 in
	       if A1>1 then {DoAgent Sc T next(A1-1 X) R}
	       else {DoAgent Sc T X R}
	       end
	    end
	 else raise error_review_M_and_N_Values end
	 end
      elseif N1==M1 then case X of var(_) then {CVars X star(M1 N1) R}
		       else {DoAgent Sc T next(N1-1 X) R}   %% M equals to N.
		       end
      else raise error_review_M_and_N_Values end            %% N<M not admited.
      end
   end
end
%-------------------------------------------------------------------%
%% With R={CBang P}, the proccess P is executed every time unit.
%% If P==bang(M P), then the proccess P is executed from the time unit M,
%% inclusive. If P==bang(M N P), with N>=M and Tsim>=N, the proccess P
%% will be executed from the time unit M until the time unit N, inclusive.
%% In any case, the simulation is terminated if no further proccesses
%% remain to be executed in the subsequent time units or if the
%% simulation time is over. Additionally, bang(1 P)==bang(P),
%% bang(N N P)==next(N-1 P), and bang(tell(false))==abort.
proc {CBang Sc T P R}
   {Wait {IsARecord P}}
   case P
   of bang(X) then case X
		   of var(_) then {CVars X bang R}
		   [] abort then {DoAgent Sc T abort R}
		   [] tell(bool('false')) then {DoAgent Sc T abort R}
		   else
		      {DoAgent Sc T X R}
		      {Wait {DoAgent Sc T next(P)}}
		   end
   [] bang(M X) then M1 in %% Bounded invariance: every point in time from M on.
      case M of int(X) then M1=X else M1=M end
      if M1>1 then case X
		  of var(_) then {CVars X bang(M1) R}
		  else {DoAgent Sc T next(M1-1 bang(X)) R}
		  end
      elseif M1==1 then case X
		       of var(_) then {CVars X bang R}
		       else {DoAgent Sc T bang(X) R}
		       end
      else raise error_review_M_and_N_Values end
      end
   [] bang(M N X) then M1 N1 in %% Bound. inv.: every point in time from M to N.
      case M of int(X) then M1=X else M1=M end
      case N of int(X) then N1=X else N1=N end
      if N1>=M1 andthen T>=N1 then
	 if M1>1 andthen N1>1 then
	    case X
	    of var(_) then {CVars X bang(M1 N1) R}
	    else {DoAgent Sc T next(M1-1 bang(1 N1-M1+1 X)) R}
	    end
	 elseif M1==1 andthen N1>1 then
	    case X
	    of var(_) then {CVars X bang(1 N1) R}
	    else
	       {DoAgent Sc T X R}
	       {Wait {DoAgent Sc T next(bang(1 N1-1 X))}}
	    end
	 elseif M1==1 andthen N1==1 then
	    case X
	    of var(_) then {CVars X bang(1 1) R}
	    else {DoAgent Sc T X R}
	    end
	 else raise error_review_M_and_N_Values end
	 end
      else raise error_review_M_and_N_Values end
      end
   end
end
%-------------------------------------------------------------------%
%% R={CAsync P} is the asynchronous parallel composition, where P is a
%% record in the form async(P1 P2 ... PN). Given to proccesses P1 and P2,
%% this procedure calculates sum(par(P1 star(P2)) par(star(P1) P2)), which
%% is equivalent to P1|P2 (remember this is different to P1||P2==par(P1 P2)).
%% This is how it works: given a record with N proccesses P1,P2,...,PN;
%% the procedure divides it into two subrecords ramdomly, one for those
%% proccesses that will be executed in the current time unit and one for
%% those proccesses that will be eventually executed in the next time units,
%% so that, by the end of the simulation, all the proccesses should have
%% been exectuted. Remember that, in any case, the simulation is
%% terminated if no further proccesses remain to be executed in the
%% subsequent time units or if the simulation time is over. If the time
%% of simulation is over, there might still be proccesses not executed.
proc {CAsync Sc T P R}
   {Wait {IsARecord P}}
   proc {RanDrop P R}
      if {Record.width P}>0 then R1 R2 in
	 {Record.partition P
	  proc {$ X R} A1={WG} mod 2 in R=if A1>0 then true else false end end
	  R1 R2}
	 if {Record.width R1}>0 andthen {Record.width R2}>0
	 then R=R1#R2
	 else {RanDrop P R}
	 end
      else raise error_review_EmptyRecord(P) end
      end
   end
   R3={RanDrop P} R7 in
   case R3
   of X1#X2 then R4 R5 R6 in
      R4={Adjoin X1 par()} R7={DoAgent Sc T R4}#_ % Immediate exec. of proc.
      R5={Record.map X2 proc {$ X R} R=star(X) end}
      R6={Adjoin R5 par()} R7=_#{DoAgent Sc T R6} % Subsequent exec. of proc.
   else skip
   end
   if R7.1==abort orelse R7.2==abort then R=abort else R=unit end 
end
%-------------------------------------------------------------------%
%% R={CTout P} is the non-deterministic time-out, where P is a record in
%% the form tout(G1#P1 G2#P2 ... GN#PN). This procedure is similar to Sum,
%% but instead of using the operator 'when', it is based on the operator
%% 'unless'. This is how it works: given a record of tuples in the form G#P,
%% where G is a guard and P a proccess, this procedure first selects all the
%% proccesses Pi whose guard cannot be entailed by the store in the current
%% time unit. Right after that, the procedure choose, non-deterministically,
%% one of the Pi to be executed in the next time unit. If no choice is
%% possible, then the operator precludes.
proc {CTout Sc T GP R}
   {Wait {IsARecord GP}}
   case GP
   of tout(0) then R=unit
   else
      GP1={Record.map GP
	   proc {$ X R}
	      R=case X of var(_) then {FindProcc X {Q2.get}}.1 else X end
	   end}
      R0={Record.filter GP1
	  proc {$ X R}
	     R=case X
	       of 'true'#_ then false
	       [] bool('true')#_ then false 
	       [] G#_ then
		  case {CAsk Sc G _} of failed then true else false end
	       [] unless(G _) then
		  case G
		  of 'true' then false
		  [] bool('true') then false
		  else case {CAsk Sc G _} of failed then true else false end
		  end
	       else raise error_NotARecord_in_TimeOut(X) end
	       end
	  end}
      R1={Record.map R0
	  proc {$ X R}
	     R=case X
	       of G#P then G#next(P)
	       [] unless(G P) then G#next(P)
	       else raise error_NotARecord_in_TimeOut(X) end
	       end
	  end} Rw={Record.width R0} in
%      if Rw>0 then R2=R1.{Record.waitOr R1} in % Faster select.
      if Rw>0 then R2 in
	 case Rw
	 of 1 then R2=R1.{Record.waitOr R1}
	 else
%	    A1={OS.rand} mod Rw + 1 in % Using Mozart random generator.
	    A1={WG} mod Rw + 1 in
	    R2=R1.{Nth {Record.arity R0} A1}
	 end
	 {DoAgent Sc T R2.2 R}
      else skip
      end
   end
end
%===================================================================%
proc {CVars V Nx R} A={FindProcc V {Q2.get}} in
   case A
   of nil then raise variable_not_defined_yet(V) end
   [] abort#_#_ then R=abort
   else case Nx
	of next then {Wait {CNext A.2 A.3 next(A.1)}}
	[] next(N) then {Wait {CNext A.2 A.3 next(N A.1)}}
	[] bang then
	   {Wait {DoAgent A.2 A.3 A.1}}
	   {Wait {DoAgent A.2 A.3 next(bang(A.1))}}
	[] bang(M) then {Wait {DoAgent A.2 A.3 bang(M A.1)}}
	[] bang(M N) then {Wait {DoAgent A.2 A.3 bang(M N A.1)}}
	[] star then {Wait {DoAgent A.2 A.3 star(A.1)}}
	[] star(M) then {Wait {DoAgent A.2 A.3 star(M A.1)}}
	[] star(M N) then {Wait {DoAgent A.2 A.3 star(M N A.1)}}
	else {Wait {DoAgent A.2 A.3 A.1}}
	end
      R=unit
   end
end
%-------------------------------------------------------------------%
proc {CDefP Sc T P R}
   {Wait {IsARecord P}}
   case P
   of def(V A) then {Wait {Q2.insert V#A#Sc#T}}
   else skip
   end
   R=unit
end
%-------------------------------------------------------------------%
proc {CGuard G Rs}
   Rs=case G
      of '=='(G1 G2) then proc {$ R} {Expression G1 R} =: {Expression G2 R} end
      [] '!='(G1 G2) then proc {$ R} {Expression G1 R} \=: {Expression G2 R} end
      [] '=<'(G1 G2) then proc {$ R} {Expression G1 R} =<: {Expression G2 R} end
      [] '>='(G1 G2) then proc {$ R} {Expression G1 R} >=: {Expression G2 R} end
      [] '<'(G1 G2)  then proc {$ R} {Expression G1 R} <: {Expression G2 R} end
      [] '>'(G1 G2)  then proc {$ R} {Expression G1 R} >: {Expression G2 R} end
      [] '='(G1 G2)  then proc {$ R} {Expression G1 R} =: {Expression G2 R} end
      else raise invalid_Guard(G) end
      end
end
%-------------------------------------------------------------------%
proc {Expression E R Rs}
   Rs=case E
      of '+'(E1 E2) then {FD.plus  {Expression E1 R} {Expression E2 R}}
      [] '-'(E1 E2) then {FD.minus {Expression E1 R} {Expression E2 R}}
      [] '*'(E1 E2) then {FD.times {Expression E1 R} {Expression E2 R}}
      [] '/'(E1 E2) then {FD.divI  {Expression E1 R} {Expression E2 R}}
      []   var(E1)  then  R.res.E1
      []   int(E1)  then  E1
      else raise invalid_Expression(E) end
      end
end
%-------------------------------------------------------------------%
proc {DoAgent Sc T A R}
   {Wait {IsARecord A}}
   R=case A
     of tell(C)     then {CTell Sc C}
     [] when(G P)   then {CWhen Sc T G P}
     [] unless(G P) then {CUnless Sc T G P}
     [] hide(...)   then {CLocal Sc T A}
     [] next(...)   then {CNext Sc T A}
     [] sum(...)    then {CSum Sc T A}
     [] par(...)    then {CPar Sc T A}
     [] star(...)   then {CStar Sc T A}
     [] bang(...)   then {CBang Sc T A}
     [] async(...)  then {CAsync Sc T A}
     [] tout(...)   then {CTout Sc T A}
     [] def(...)    then {CDefP Sc T A}
     [] var(_)      then {CVars A 0}
     [] omit        then {CTell Sc proc {$ _} skip end}
     [] abort       then abort
     end
end

%===================================================================%
proc {Message1 Q}
   {Browse 'End of Simulation'#Q}
   {System.showInfo
    '*************************************************************'}
   {System.showError
    '*** '#'No more proccesses to simulate'#"."#' Simulation '#terminated#' ***'}
   {System.showInfo
    '*************************************************************'}
end
proc {Message2 Q}
   {Browse 'End of Simulation'#Q}
   {System.showInfo '*****************************************'}
   {System.showError '*** '#'Time is up'#"."#' Simulation '#terminated#' ***'}
   {System.showInfo '*****************************************'}
end
proc {Message3 Q}
   {Browse 'End of Simulation'#Q}
   {System.showInfo
    '*************************************************************'}
   {System.showError
    '**** '#'No more proccesses to simulate'#"."#' Simulation '#aborted#' *****'}
   {System.showInfo
    '*************************************************************'}
end
%-------------------------------------------------------------------%
proc {Simulate Vars Doms Tsim Proccs R} V D T
   case Vars
   of vars(...) then V={Record.toList Vars}
   [] _|_ then V=Vars
   else raise invalid_variable_format_Not_a_list_or_record(Vars) end
   end
   case Doms
   of doms(...) then D={Record.toList Doms}
   [] _|_ then D=Doms
   else raise invalid_domain_definition_Not_a_list_or_record(Doms) end
   end
   case Tsim
   of tsim(int(X)) then
      if X>0 then T=X
      else raise invalid_time_of_simulation_Not_a_positive_integer(Tsim) end
      end
   else
      if {IsInt Tsim} andthen Tsim>0 then T=Tsim
      else raise invalid_time_of_simulation_Not_a_positive_integer(Tsim) end
      end
   end
   Q3={CProcList}
   fun {Agent} L={Q1.get} in
      if L==nil then nil else {List.toTuple par L} end
   end
   proc {DoSim Ts Procc}
      S={Space.new proc{$ R} R=store(res:{Raiz V D}) end}
      A={DoAgent S Ts Procc} in
      case A
      of abort then {Wait {Q3.insert aborted}} {Message3 {ReadableSol}/*{Q3.get}*/}
      else case {Space.ask S}
	   of failed then {Wait {Q3.insert failed}}
	   else {Wait {Q3.insert {Space.merge {Space.clone S}}}}
	   end
	 case {Q1.get}
	 of nil then {Message1 {ReadableSol}/*{Q3.get}*/}
	 else {SimProc Ts-1 {Agent}}
	 end
      end
      {Space.kill S}
   end
   proc {SimProc Ts Procc}
      if Ts==T then {DoSim Ts Procc}
      elseif 0<Ts andthen Ts<T then {Q1.clear} {DoSim Ts Procc}
      else {Message2 {ReadableSol}/*{Q3.get}*/}
      end
   end
   proc {ReadableSol R} Rr Rs={Q3.get} in
      Rr={List.map Rs
	  proc {$ X R} case X
		       of store(res:Y)
		       then R={Record.map Y
			       proc {$ X R}
				  Xmin={FD.reflect.min X}
				  Xmax={FD.reflect.max X} in
				  if Xmin==Xmax then R=X else R=Xmin#Xmax end
			       end}
		       else R=X
		       end
	  end}
      R={List.reverse Rr}
   end in
   {SimProc T Proccs} R={ReadableSol} {Q1.clear} {Q2.clear} {Q3.clear}
end
%===================================================================%
%===================================================================%

%-------------------------------------------------------------------%
%{Browser.object option(buffer size:500)}
%{Browser.object option(display depth:500)}
%-------------------------------------------------------------------%

%-------------------------------------------------------------------%
% % Run next two lines first for examples 1--4:
% Vars=[a b c d] Doms=[20 30 40 50] Ts=10
% S={Space.new proc{$ R} R=store(res:{Raiz Vars Doms}) end}
%-------------------------------------------------------------------%
% % Example 1: Tout. Final space is entailed.
% {Browse {DoAgent S Ts par(tout('>='(var(c) int(5))#tell('<'('*'(int(2) var(a)) int(15))) '=<'(var(b) int(8))#tell('<'('*'(int(2) var(d)) int(45))) '=<'(var(a) int(20))#tell('<'('*'(int(2) var(d)) int(25)))) tell('=='('+'(var(a) int(2)) int(15))) tell('>='(var(c) int(5))))}}
% {Browse {Space.merge {Space.clone S}}}
% {Browse {Space.askVerbose S}}
%-------------------------------------------------------------------%
% % Example 2: Sum. Final space is entailed.
% {Browse {DoAgent S Ts par(sum('>='(var(c) int(5))#tell('<'('*'(int(2) var(a)) int(28))) '=<'(var(b) int(8))#tell('<'('*'(int(2) var(d)) int(45))) '=<'(var(a) int(20))#tell('<'('*'(int(2) var(d)) int(25)))) tell('=='('+'(var(a) int(2)) int(15))) tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(c) int(5))))}}
% {Browse {Space.merge {Space.clone S}}}
% {Browse {Space.askVerbose S}}
%-------------------------------------------------------------------%
% % Example 3: Sum. Final space is entailed.
% {Browse {DoAgent S Ts par(sum('>='(var(c) int(5))#tell('<'('*'(int(2) var(a)) int(28))) 'true'#tell('<'('*'(int(2) var(d)) int(45))) '=<'(var(a) int(20))#tell('<'('*'(int(2) var(d)) int(25)))) tell('=='('+'(var(a) int(2)) int(15))) tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(c) int(5))))}}
% {Browse {Space.merge {Space.clone S}}}
% {Browse {Space.askVerbose S}}
%-------------------------------------------------------------------%

% % Example 4a: Using the operator 'hide' (local). Error: variable oculta no
% % se puede ejecutar en otra unidad de tiempo. 'hide' solo funciona en la
% % unidad de tiempo actual.
% {Browse {Simulate [a b] [20 30] 3 hide(vars(x1) unless('>='(var(b) int(5)) tell('=='('-'(var(x1) int(1)) int(7)))))}}
%-------------------------------------------------------------------%
% % Example 4b: Using the operator 'hide' (local).
% {Browse {Simulate [a b] [20 30] 3 unless('>='(var(b) int(5)) hide(vars(x1) par(tell('=='('-'(var(x1) int(1)) int(7))) tell('=='(var(x1) var(b))))))}}
%-------------------------------------------------------------------%
% % Example 4c: Using the operator 'hide' (local). Error: similar al ejemplo
% % 4a, la variable oculta se declara y se asigna en tiempos diferentes.
% {Browse {Simulate [a b] [20 30] 3 par(def(var(a1) tell('=='(var(x1) var(b)))) unless('>='(var(b) int(5)) hide(vars(x1) par(tell('=='('-'(var(x1) int(1)) int(7))) var(a1)))))}}
%-------------------------------------------------------------------%
% % Example 4d: Using the operator 'hide' (local).
% {Browse {Simulate [a b] [20 30] 3 par(def(var(a1) hide(vars(x1) par(tell('=='(var(x1) var(b))) tell('=='('-'(var(x1) int(1)) int(7)))))) unless('>='(var(b) int(5)) var(a1)))}}
%-------------------------------------------------------------------%
% % Example 4e: Using the operator 'hide' (local).
% {Browse {Simulate [a b] [20 30] 5 hide(vars(a) par(tell('=='(var(a) int(5))) when('=<'(var(a) int(6)) tell('=<'(var(b) int(5))))))}}
%-------------------------------------------------------------------%
% % Example 4f: Using the operator 'hide' (local). Note que la segunda
% % variable 'b', está oculta (es local), por lo que en el 'when' la
% % guarda '>='(var(b) int(0)) se cumple, ejecutandose el siguiente 'tell'.
% {Browse {Simulate [a b c] [20 30 30] 5 par(when('>='(var(b) int(0)) tell('>='(var(b) int(5)))) hide(vars(b) when('>='(var(b) int(0)) tell('=<'(var(c) int(5))))))}}
%-------------------------------------------------------------------%
% % Example 4g: Using the operator 'hide' (local). Similar al ejemplo 4f.
% % En este caso, como la segunda variable 'b' está oculta (es local), en
% % el 'when' que sigue la guarda '>='(var(b) int(5)) no se cumple; por
% % lo tanto, el correspondiente 'tell' no se ejecuta.
% {Browse {Simulate [a b c] [20 30 30] 5 par(when('>='(var(b) int(0)) tell('>='(var(b) int(5)))) hide(vars(b) when('>='(var(b) int(5)) tell('=<'(var(c) int(5))))))}}
%-------------------------------------------------------------------%
% % Example 4h: Using the operator 'hide' (local).
% {Browse {Simulate [a b c] [20 30 30] 5 par(when('>='(var(a) int(0)) tell('>='(var(b) int(5)))) hide(vars(a) when('>='(var(a) int(0)) tell('=<'(var(c) int(5))))))}}
%-------------------------------------------------------------------%
% % Example 4i: Using the operator 'hide' (local).
% {Browse {Simulate [a b] [20 30] 5 par(tell('=='(var(a) int(5))) hide(vars(a) par(when('=<'(var(a) int(6)) tell('=<'(var(b) int(5)))) tell('<'(var(a) int(5))))))}}
%-------------------------------------------------------------------%
% % Example 4j: Using the operator 'hide' (local).
% {Browse {Simulate [a b] [20 30] 5 par(def(var(q1) par(tell('=='(var(a) int(1))) next(hide(vars(a) par(var(q1) when('=='(var(a) int(1)) tell('=<'(var(b) int(5))))))))) var(q1))}}
%-------------------------------------------------------------------%
% % Example 4k: Using the operator 'hide' (local).
% {Browse {Simulate [a b c] [20 30 30] 5 par(when('>='(var(a) int(5)) tell('>='(var(b) int(5)))) hide(vars(a) when('=<'(var(a) int(4)) tell('=<'(var(c) int(5))))) tell('>='(var(a) int(5))))}}
%-------------------------------------------------------------------%
% % Example 5a: Using the operator 'par'.
% {Browse {Simulate [a b c d] [20 30 40 50] 2 par(tell('>='(var(d) int(15))))}}
%-------------------------------------------------------------------%
% % Example 5a: Using the operator 'sum'. Sum(0)==skip (no hace nada).
% {Browse {Simulate [a b c d] [20 30 40 50] 2 sum(0)}}
%-------------------------------------------------------------------%
% % Example 5b: Using the operator 'next'.
% {Browse  {Simulate [a b c d] [20 30 40 50] 2 par(next(tell('>='(var(d) int(15)))))}}
%-------------------------------------------------------------------%
% % Example 5c: Using the operator 'next'. El ejemplo 5b es equivalente
% % con el este ejemplo.
% {Browse  {Simulate [a b c d] [20 30 40 50] 2 par(next(tell('>='(var(d) int(15)))) sum(0))}}
%-------------------------------------------------------------------%
% % Example 5d: Using the operator 'next'. Los ejemplos 5b y 5c son
% % equivalentes con el este ejemplo.
% {Browse  {Simulate [a b c d] [20 30 40 50] 2 sum('true'#next(tell('>='(var(d) int(15)))))}}
%-------------------------------------------------------------------%
% % Example 5e: Using the operator 'next'. Pero los ejemplos 5b, 5c y 5d
% % no son equivalentes con el este ejemplo.
% {Browse  {Simulate [a b c d] [20 30 40 50] 2 sum('true'#next(tell('>='(var(d) int(15)))) 'true'#sum(0))}}
%-------------------------------------------------------------------%
% % Example 6: Using the operator 'sum'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(sum('>='(var(c) int(5))#tell('<'('*'(int(2) var(a)) int(28))) 'true'#tell('<'('*'(int(2) var(d)) int(45))) '=<'(var(a) int(20))#tell('<'('*'(int(2) var(d)) int(25)))) tell('=='('+'(var(a) int(2)) int(15))) tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(c) int(5))))}}
%-------------------------------------------------------------------%
% % Example 7: Using the operator 'sum'.
% {Browse {Simulate [a b c d] [20 30 40 50] 1 par(sum('>='(var(c) int(5))#when('=='(var(a) int(13)) par(tell('<'('*'(int(2) var(c)) int(15))) tell('<'('*'(int(2) var(d)) int(28))))) 'true'#tell('<'('*'(int(2) var(d)) int(45))) '=<'(var(a) int(20))#tell('<'('*'(int(2) var(d)) int(25)))) tell('=='('+'(var(a) int(2)) int(15))) tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(c) int(5))))}}
%-------------------------------------------------------------------%
% % Example 8: Using the operator 'sum'.
% {Browse {Simulate [a b c d] [20 30 40 50] 1 par(sum('>='(var(c) int(5))#tell('<'('*'(int(2) var(d)) int(15))) '=<'(var(b) int(8))#tell('<'('*'(int(2) var(d)) int(45))) '=<'(var(a) int(20))#tell('<'('*'(int(2) var(d)) int(25)))) tell('=='('+'(var(a) int(2)) int(15))) tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(c) int(5))))}}
%-------------------------------------------------------------------%
% % Example 9: Using the operator 'next'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 par(sum('>='(var(c) int(5))#next(tell('<'('*'(int(2) var(a)) int(15)))) '=<'(var(b) int(8))#tell('<'('*'(int(2) var(d)) int(45))) '=<'(var(a) int(20))#tell('<'('*'(int(2) var(d)) int(25)))) tell('=='('+'(var(a) int(2)) int(15))) tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(c) int(5))) next(tell('>='(var(d) int(15)))) next(next(tell('>='(var(d) int(15))))))}}
%-------------------------------------------------------------------%
% % Example 10a: Using the operator 'next'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 par(sum('>='(var(c) int(5))#tell('<'('*'(int(2) var(a)) int(15))) '=<'(var(b) int(8))#tell('<'('*'(int(2) var(d)) int(45))) '=<'(var(a) int(20))#tell('<'('*'(int(2) var(d)) int(25)))) tell('<'('+'(var(a) int(2)) int(15))) tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(c) int(5))) next(tell('>='(var(d) int(15)))) next(next(tell('=<'(var(a) int(13))))))}}
%-------------------------------------------------------------------%
% % Example 10b: Using the operator 'next'. Failed.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 par(sum('>='(var(c) int(5))#tell('<'('*'(int(2) var(a)) int(15))) '=<'(var(b) int(8))#tell('<'('*'(int(2) var(d)) int(45))) '=<'(var(a) int(20))#tell('<'('*'(int(2) var(d)) int(25)))) tell('=='('+'(var(a) int(2)) int(15))) tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(c) int(5))) next(par(next(tell('=='(var(b) int(17)))) tell('>='(var(d) int(15))))) next(next(tell('=<'(var(a) int(13))))))}}
%-------------------------------------------------------------------%
% % Example 11a: Using the operator 'tell'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 par(tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(d) int(15))) tell('<'(var(a) int(13))))}}
%-------------------------------------------------------------------%
% % Example 11b: Using the operator 'next'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 par(tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(d) int(15))) next(tell('<'(var(a) int(13)))))}}
%-------------------------------------------------------------------%
% % Example 11c: Using the operator 'next'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 par(tell('=='('-'(var(b) int(1)) int(7))) next(tell('>='(var(d) int(15)))) next(tell('<'(var(a) int(13)))))}}
%-------------------------------------------------------------------%
% % Example 11d: Using the operator 'next'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 par(next(tell('=='('-'(var(b) int(1)) int(7)))) next(tell('>='(var(d) int(15)))) next(tell('<'(var(a) int(13)))))}}
%-------------------------------------------------------------------%
% % Example 11e: Using the operator 'next'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 par(tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(d) int(15))) next(next(tell('<'(var(a) int(13))))))}}
%-------------------------------------------------------------------%
% % Example 11f: Using the operator 'next'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 par(tell('=='('-'(var(b) int(1)) int(7))) next(tell('>='(var(d) int(15)))) next(next(tell('<'(var(a) int(13))))))}}
%-------------------------------------------------------------------%
% % Example 12: Using the operator 'bang'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 bang(tell('<'('*'(int(2) var(a)) int(15))))}}
%-------------------------------------------------------------------%
% % Example 13: Using the operator 'def'.
% {Browse {Simulate [a b c d] [20 30 40 50] 1 par(def(var(a1) tell('='(var(a) int(1)))) def(var(b1) tell('='(var(b) int(1)))) par(var(a1) var(b1)))}}
%-------------------------------------------------------------------%
% % Example 14: Using the operator 'def'.
% {Browse {Simulate [a b] [20 30] 4 par(def(var(t1) tell('<'('*'(int(2) var(a)) int(15)))) def(var(t2) next(tell('=='('-'(var(b) int(4)) int(15))))) def(var(t3) when('>='(var(b) int(0)) next(var(t1)))) def(var(t4) when('=<'(var(a) int(20)) next(var(t2)))) par(var(t3) var(t4)))}}
%-------------------------------------------------------------------%
% % Example 15: Using the operator 'def'.
% {Browse {Simulate [a b] [20 30] 5 par(def(var(t1) tell('<'('*'(int(2) var(a)) int(15)))) def(var(t2) next(tell('=='('-'(var(b) int(4)) int(15))))) par(var(t1) next(3 var(t2))))}}
%-------------------------------------------------------------------%
% % Example 16a: Using the operator 'next'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(def(var(t1) tell('<'('*'(int(2) var(a)) int(15)))) next(next(next(var(t1)))))}}
%-------------------------------------------------------------------%
% % Example 16b: Using the operator 'next'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(next(3 tell('<'('*'(int(2) var(a)) int(15)))))}}
%-------------------------------------------------------------------%
% % Example 16c: Using the operator 'next'. Equivalente al ejercicio 16a.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(def(var(t1) tell('<'('*'(int(2) var(a)) int(15)))) next(3 var(t1)))}}
%-------------------------------------------------------------------%
% % Example 17a: Using the operator 'bang'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(def(var(t1) tell('<'('*'(int(2) var(a)) int(15)))) bang(var(t1)))}}
%-------------------------------------------------------------------%
% % Example 17b: Using the operator 'bang'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(def(var(t1) tell('<'('*'(int(2) var(a)) int(15)))) bang(4 var(t1)))}}
%-------------------------------------------------------------------%
% % Example 18a: Using the operator 'bang'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(def(var(t1) tell('<'('*'(int(2) var(a)) int(15)))) bang(4 4 var(t1)))}}
%-------------------------------------------------------------------%
% % Example 18b: Using the operator 'bang'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(def(var(t1) tell('<'('*'(int(2) var(a)) int(15)))) bang(int(4) int(7) var(t1)))}}
%-------------------------------------------------------------------%
% % Example 19a: Using the operator 'star'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(star(tell('<'('*'(int(2) var(a)) int(15)))))}}
%-------------------------------------------------------------------%
% % Example 19b: Using the operator 'star'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(def(var(t1) tell('<'('*'(int(2) var(a)) int(15)))) star(var(t1)))}}
%-------------------------------------------------------------------%
% % Example 19c: Using the operator 'star'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(def(var(t1) tell('<'('*'(int(2) var(a)) int(15)))) star(4 var(t1)))}}
%-------------------------------------------------------------------%
% % Example 19d: Using the operator 'star'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(def(var(t1) tell('<'('*'(int(2) var(a)) int(15)))) star(1 5 var(t1)))}}
%-------------------------------------------------------------------%
% % Example 19e: Using the operator 'star'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(def(var(t1) tell('<'('*'(int(2) var(a)) int(15)))) star(int(1) int(5) var(t1)))}}
%-------------------------------------------------------------------%
% % Example 20a: Using the operator 'async'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 async(tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(d) int(15))) tell('<'(var(a) int(13))))}}
%-------------------------------------------------------------------%
% % Example 20b: Using the operator 'async'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 par(def(var(t1) tell('=='('-'(var(b) int(1)) int(7)))) def(var(t2) tell('>='(var(d) int(15)))) def(var(t3) tell('<'(var(a) int(13)))) async(var(t1) var(t2) var(t3)))}}
%-------------------------------------------------------------------%
% % Example 21a: Using the operator 'tout'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 tout('>='(var(b) int(0))#tell('=='('-'(var(b) int(1)) int(7))) '>='(var(c) int(5))#tell('>='(var(d) int(15))) '>='(var(d) int(5))#tell('<'(var(a) int(13))))}}
%-------------------------------------------------------------------%
% % Example 21b: Using the operator 'tout'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 par(def(var(t1) '>='(var(b) int(0))#tell('=='('-'(var(b) int(1)) int(7)))) def(var(t2) '>='(var(c) int(5))#tell('>='(var(d) int(15)))) def(var(t3) '>='(var(d) int(5))#tell('<'(var(a) int(13)))) tout(var(t1) var(t2) var(t3)))}}
%-------------------------------------------------------------------%
% % Example 21c: Using the operator 'tout'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 tout(0)}}
%-------------------------------------------------------------------%
% % Example 22a: Using the operator 'sum'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 sum('>='(var(b) int(0))#tell('=='('-'(var(b) int(1)) int(7))) '>='(var(c) int(5))#tell('>='(var(d) int(15))) '>='(var(d) int(5))#tell('<'(var(a) int(13))))}}
%-------------------------------------------------------------------%
% % Example 22b: Using the operator 'sum'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 par(def(var(t1) '>='(var(b) int(0))#tell('=='('-'(var(b) int(1)) int(7)))) def(var(t2) '>='(var(c) int(5))#tell('>='(var(d) int(15)))) def(var(t3) '>='(var(d) int(5))#tell('<'(var(a) int(13)))) sum(var(t1) var(t2) var(t3)))}}
%-------------------------------------------------------------------%
% % Example 23: Using the operator 'unless'.
% {Browse {Simulate [a b] [20 30] 3 unless('>='(var(b) int(5)) tell('=='('-'(var(a) int(1)) int(7))))}}
%-------------------------------------------------------------------%
% % Example 23a: Using the operator 'unless'.
% {Browse {Simulate [x y] [20 20] 2 par(unless('<'(var(x) int(10)) tell('='(var(y) int(5)))) next(when('='(var(y) int(5)) tell('<'(var(x) int(10))))))}}
%-------------------------------------------------------------------%
% % Example 23b: Using the operator 'unless'.
% {Browse {Simulate [x y] [20 20] 2 par(unless(bool('true') tell('='(var(y) int(5)))) next(when('='(var(y) int(5)) tell('<'(var(x) int(10))))))}}
%-------------------------------------------------------------------%
% % Example 23c: Using the operator 'unless'. Equivalente al ejercicio 23b.
% {Browse {Simulate [x y] [20 20] 2 par(unless('=<'(var(x) int(20)) tell('='(var(y) int(5)))) next(when('='(var(y) int(5)) tell('<'(var(x) int(10))))))}}
%-------------------------------------------------------------------%
% % Example 23d: Using the operator 'when'.
% {Browse {Simulate [x y] [20 20] 2 par(when(bool('true') tell('='(var(y) int(5)))) when('='(var(y) int(5)) tell('<'(var(x) int(10)))))}}
%-------------------------------------------------------------------%
% % Example 23e: Using the operator 'when'.
% {Browse {Simulate [x y] [20 20] 2 par(when('='(var(y) int(5)) tell('<'(var(x) int(10)))) when(bool('true') tell('='(var(y) int(5)))))}}
%-------------------------------------------------------------------%
% % Example 23f: Using the operator 'when'.
% {Browse {Simulate [x y] [20 20] 2 par(when('='(var(y) int(5)) tell('<'(var(x) int(10)))) when(bool('true') abort))}}
%-------------------------------------------------------------------%
% % Example 23g: Using the operator 'when'.
% {Browse {Simulate [a b c] [20 30 30] 5 par(when('>='(var(a) int(0)) tell('>='(var(b) int(5)))) when('>='(var(a) int(0)) tell('=<'(var(c) int(5)))))}}
%-------------------------------------------------------------------%
% % Example 23h: Using the operator 'when'.
% {Browse {Simulate [a b c] [20 30 30] 5 when('>='(var(a) int(0)) par(tell('>='(var(b) int(5))) tell('=<'(var(c) int(5)))))}}
%-------------------------------------------------------------------%
% % Example 24a: Using the operator 'unless'.
% {Browse {Simulate [x y] [20 20] 2 par(unless('='(var(y) int(5)) tell('<'(var(x) int(10)))) unless(bool('true') abort))}}
%-------------------------------------------------------------------%
% % Example 24b: Using the operator 'unless'.
% {Browse {Simulate [x y] [20 20] 2 par(unless('='(var(y) int(5)) tell('<'(var(x) int(10)))) unless('='(var(x) int(5)) abort))}}
%-------------------------------------------------------------------%
% % Example 25: Using the operator 'sum'.
% {Browse {Simulate [x y] [20 20] 2 par(tell('<'(var(x) int(10))) sum(0))}}
%-------------------------------------------------------------------%
% % Example 26: Using the operator 'omit'.
% {Browse {Simulate [x y] [20 20] 2 par(tell('<'(var(x) int(10))) omit)}}
%-------------------------------------------------------------------%
% % Example 27a: Using the operator 'abort'.
% {Browse {Simulate [x y] [20 20] 3 abort}}
%-------------------------------------------------------------------%
% % Example 27b: Using the operator 'abort'.
% {Browse {Simulate [x y] [20 20] 3 par(tell('<'(var(x) int(10))) abort)}}
%-------------------------------------------------------------------%
% % Example 27c: Using the operator 'abort'.
% {Browse {Simulate [x y] [20 20] 5 par(next(next(tell('<'(var(x) int(10))))) next(abort))}}
%-------------------------------------------------------------------%
% % Example 27d: Using the operator 'abort'.
% {Browse {Simulate [x y] [20 20] 5 par(next(next(tell('<'(var(x) int(10))))) next(4 abort))}}
%-------------------------------------------------------------------%
% % Example 27e: Using the operator 'abort'.
% {Browse {Simulate [x y] [20 20] 5 par(next(next(tell('<'(var(x) int(10))))) bang(abort))}}
%-------------------------------------------------------------------%
% % Example 27f: Using the operator 'abort'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(sum('>='(var(c) int(5))#tell('<'('*'(int(2) var(a)) int(28))) 'true'#tell('<'('*'(int(2) var(d)) int(45))) '=<'(var(a) int(20))#tell('<'('*'(int(2) var(d)) int(25)))) next(6 abort) tell('=='('+'(var(a) int(2)) int(15))) tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(c) int(5))))}}
%-------------------------------------------------------------------%
% % Example 27g: Using the operator 'abort'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(sum('true'#next(6 abort) '>='(var(c) int(5))#tell('<'('*'(int(2) var(a)) int(28))) '=<'(var(a) int(20))#tell('<'('*'(int(2) var(d)) int(25)))) tell('=='('+'(var(a) int(2)) int(15))) tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(c) int(5))))}}
%-------------------------------------------------------------------%
% % Example 27h: Using the operator 'abort'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 tout('>='(var(b) int(0))#tell('=='('-'(var(b) int(1)) int(7))) '>='(var(c) int(5))#tell('>='(var(d) int(15))) 'true'#next(6 abort) '>='(var(d) int(5))#tell('<'(var(a) int(13))))}}
%-------------------------------------------------------------------%
% % Example 27i: Using the operator 'abort'.
% {Browse {Simulate [a b c d] [20 30 40 50] 3 tout('>='(var(b) int(0))#tell('=='('-'(var(b) int(1)) int(7))) '>='(var(c) int(5))#abort '>='(var(d) int(5))#tell('<'(var(a) int(13))))}}
%-------------------------------------------------------------------%
% % Example 28a: Using the operator 'tell'. Fallo.
% {Browse {Simulate [x y] [20 20] 3 par(next(tell('<'(var(x) int(10)))) tell(bool('false')))}}
%-------------------------------------------------------------------%
% % Example 28b: Using the operator 'tell'. Omit no es una restricción.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 tell(omit)}}
%-------------------------------------------------------------------%
% % Example 28c: Using the operator 'tell'. Abort no es una restricción.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 tell(abort)}}
%-------------------------------------------------------------------%
% % Example 29: Using the operator 'bang'.
% {Browse {Simulate [x y] [20 20] 3 par(next(tell('<'(var(x) int(10)))) bang(tell(bool('false'))))}}
%-------------------------------------------------------------------%
% % Example 30a: Using the operator 'def'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(def(var(t1) abort) var(t1))}}
%-------------------------------------------------------------------%
% % Example 30b: Using the operator 'def'.
% {Browse {Simulate [a b c d] [20 30 40 50] 10 par(var(t1) def(var(t1) abort))}}
%-------------------------------------------------------------------%
% % Example 31a: Using the operator 'star'.
% {Browse {Simulate [x y] [20 20] 3 par(next(tell('<'(var(x) int(10)))) star(tell(bool('false'))))}}
%-------------------------------------------------------------------%
% % Example 31b: Using the operator 'star'.
% {Browse {Simulate [x y] [20 20] 6 par(next(tell('<'(var(x) int(10)))) star(int(3) tell(bool('false'))))}}
%-------------------------------------------------------------------%
% % Example 31c: Using the operator 'star'.
% {Browse {Simulate [x y] [20 20] 6 par(next(tell('<'(var(x) int(10)))) star(int(3) int(5) tell(bool('false'))))}}
%-------------------------------------------------------------------%
% % Example 31d: Using the operator 'star'.
% {Browse {Simulate [x y] [20 20] 6 par(next(tell('<'(var(x) int(10)))) star(int(3) abort))}}
%-------------------------------------------------------------------%
% % Example 31e: Using the operator 'star'.
% {Browse {Simulate [x y] [20 20] 6 par(next(tell('<'(var(x) int(10)))) star(int(3) int(5) abort))}}
%-------------------------------------------------------------------%
% % Example 32a: Using the operator 'async'.
% {Browse {Simulate [a b c d] [20 30 40 50] 4 async(tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(d) int(15))) abort tell('<'(var(a) int(13))))}}
%-------------------------------------------------------------------%
% % Example 32b: Using the operator 'async'.
% {Browse {Simulate [a b c d] [20 30 40 50] 4 async(tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(d) int(15))) omit tell('<'(var(a) int(13))))}}
%-------------------------------------------------------------------%
% % Example 32c: Using the operator 'async'.
% {Browse {Simulate [a b c d] [20 30 40 50] 4 async(tell('=='('-'(var(b) int(1)) int(7))) tell('>='(var(d) int(15))) tell(bool('false')) tell('<'(var(a) int(13))))}}
%-------------------------------------------------------------------%
% % Example 33a: Using the operator 'star'.
% {Browse {Simulate [x y] [20 20] 3 star(abort)}}
%-------------------------------------------------------------------%
% % Example 33b: Using the operator 'star'.
% {Browse {Simulate [x y] [20 20] 6 star(int(3) int(5) tell(bool('false')))}}
%-------------------------------------------------------------------%
% % Example 34a: Using the operator 'unless' for recursion.
% {Browse {Simulate [a b] [20 30] 5 par(def(var(q1) par(tell('=='(var(a) int(1))) unless('=='(var(b) int(1)) var(q1)))) next(2 tell('=='(var(b) int(1)))) var(q1))}}
%-------------------------------------------------------------------%
% % Example 34b: Using the operator 'unless' for recursion.
% {Browse {Simulate [a b] [20 30] 10 par(def(var(q1) par(tell('=='(var(a) int(1))) when('=='(var(b) int(1)) next(par(tell('=='(var(b) int(0))) var(q1)))) unless('=='(var(b) int(1)) var(q1)))) next(3 tell('=='(var(b) int(1)))) var(q1))}}
%-------------------------------------------------------------------%
% % Example 34c: Using the operator 'hide' and recursion.
% {Browse {Simulate [a b] [20 30] 5 par(par(tell('=='(var(a) int(1))) def(var(q1) next(hide(vars(a x) par(var(q1) when('>='(var(a) int(0)) par(tell('='(var(x) int(1))) tell('='(var(b) var(x))))))))) var(q1)))}}
%-------------------------------------------------------------------%
% % Example 34d: Using the operator 'unless' for recursion. No funciona.
% {Browse {Simulate [a b] [20 30] 10 par(tell('=='(var(b) int(0))) def(var(q1) unless('=='(var(b) int(1)) par(tell('=='(var(b) int(1))) var(q2)))) def(var(q2) unless('=='(var(b) int(0)) par(tell('=='(var(b) int(2))) var(q1)))) next(3 tell('=='(var(b) int(1)))) par(var(q1) var(q2)))}}
%-------------------------------------------------------------------%
% % Example 35: Using the operator 'sum' and recursion. No funciona.
% {Browse {Simulate [dir] [1#4] 10 par(tell('=='(var(dir) int(1))) def(var(tr) sum('=='(var(dir) int(1))#next(tell('=='(var(dir) int(2)))) '=='(var(dir) int(2))#next(tell('=='(var(dir) int(3)))) '=='(var(dir) int(3))#next(tell('=='(var(dir) int(4)))) '=='(var(dir) int(4))#next(tell('=='(var(dir) int(1)))))) var(tr))}}
%-------------------------------------------------------------------%
% % Example 35: Using the operator 'sum' and recursion. Revisar
% {Browse {Simulate [dir] [1#4] 10 par(def(var(tr) sum('=='(var(dir) int(1))#next(par(tell('=='(var(dir) int(2))) var(tr))) '=='(var(dir) int(2))#next(par(tell('=='(var(dir) int(3))) var(tr))) '=='(var(dir) int(3))#next(par(tell('=='(var(dir) int(4))) var(tr))) '=='(var(dir) int(4))#next(par(tell('=='(var(dir) int(1))) var(tr))))) tell('=='(var(dir) int(1))) var(tr))}}
%-------------------------------------------------------------------%
% % Example 36a: Using 'bang' for recursion. TurnR (Ejemplo ORV, 2013)
% {Browse {Simulate [dir] [1#4] 10 par(bang(sum('=='(var(dir) int(1))#next(tell('=='(var(dir) int(2)))) '=='(var(dir) int(2))#next(tell('=='(var(dir) int(3)))) '=='(var(dir) int(3))#next(tell('=='(var(dir) int(4)))) '=='(var(dir) int(4))#next(tell('=='(var(dir) int(1)))))) tell('=='(var(dir) int(1))))}}
%-------------------------------------------------------------------%
% % Example 36b: Using 'bang' for recursion. TurnL (Ejemplo ORV, 2013)
% {Browse {Simulate [dir] [1#4] 10 par(bang(sum('=='(var(dir) int(1))#next(tell('=='(var(dir) int(4)))) '=='(var(dir) int(4))#next(tell('=='(var(dir) int(3)))) '=='(var(dir) int(3))#next(tell('=='(var(dir) int(2)))) '=='(var(dir) int(2))#next(tell('=='(var(dir) int(1)))))) tell('=='(var(dir) int(1))))}}
%-------------------------------------------------------------------%
% % Example 37a: Using 'bang' for recursion. Robot1 (Ejemplo ORV, 2013)
% {Browse {Simulate [turn dir] [0#1 1#4] 10 par(bang(sum('=='(var(turn) int(1))#next(tell('=='(var(turn) int(0)))) '=='(var(turn) int(0))#next(tell('=='(var(turn) int(1)))))) tell('=='(var(turn) int(1))))}}
%-------------------------------------------------------------------%
% % Example 37b: Using 'bang' for recursion. Robot2 (Ejemplo ORV, 2013). Revisar
% {Browse {Simulate [turn dir] [0#1 1#4] 10 par(bang(sum('=='(var(dir) int(1))#unless('=='(var(turn) int(1)) tell('=='(var(dir) int(2)))) '=='(var(dir) int(2))#unless('=='(var(turn) int(1)) tell('=='(var(dir) int(3)))) '=='(var(dir) int(3))#unless('=='(var(turn) int(1)) tell('=='(var(dir) int(4)))) '=='(var(dir) int(4))#unless('=='(var(turn) int(1)) tell('=='(var(dir) int(1)))))) tell('=='(var(dir) int(1))))}}
%-------------------------------------------------------------------%
% % Example 37c: Using 'bang' for recursion. Robot3 (Ejemplo ORV, 2013)
 % {Browse {Simulate [turn dir] [0#2 1#4] 10
 % 	 par(
 % 	    bang(
 % 	       par(
 % 		  when('>'(var(turn) int(0))
 % 		       sum(
 % 			  '=='(var(turn) int(1))#
 % 			  sum(
 % 			     '=='(var(dir) int(1))#
 % 			     next(tell('=='(var(dir) int(2))))
 % 			     '=='(var(dir) int(2))#
 % 			     next(tell('=='(var(dir) int(3))))
 % 			     '=='(var(dir) int(3))#
 % 			     next(tell('=='(var(dir) int(4))))
 % 			     '=='(var(dir) int(4))#
 % 			     next(tell('=='(var(dir) int(1)))))
 % 			  '=='(var(turn) int(2))#
 % 			  sum(
 % 			     '=='(var(dir) int(1))#
 % 			     next(tell('=='(var(dir) int(4))))
 % 			     '=='(var(dir) int(4))#
 % 			     next(tell('=='(var(dir) int(3))))
 % 			     '=='(var(dir) int(3))#
 % 			     next(tell('=='(var(dir) int(2))))
 % 			     '=='(var(dir) int(2))#
 % 			     next(tell('=='(var(dir) int(1)))))))
 % 		  when('=='(var(turn) int(0))
 % 			 sum(
 % 			    '=='(var(dir) int(1))#
 % 			    next(tell('=='(var(dir) int(1))))
 % 			    '=='(var(dir) int(2))#
 % 			    next(tell('=='(var(dir) int(2))))
 % 			    '=='(var(dir) int(3))#
 % 			    next(tell('=='(var(dir) int(3))))
 % 			    '=='(var(dir) int(4))#
 % 			    next(tell('=='(var(dir) int(4))))))
 % 		  sum(
 % 		     'true'#next(tell('=='(var(turn) int(0))))
 % 		     'true'#next(tell('=='(var(turn) int(1))))
 % 		     'true'#next(tell('=='(var(turn) int(2)))))))
 % 	    tell('=='(var(dir) int(1)))
 % 	    tell('=='(var(turn) int(1))))}}
%-------------------------------------------------------------------%
