%===================================================================%
%%% Author:
%%%   Rodrigo Botero Ibarra <rbotero001@gmail.com>
%%%
%%% Copyright:
%%%   Rodrigo Botero Ibarra, 2022
%===================================================================%
\insert NtccSimulator_1c.oz
\insert Interpreter_1.oz
\insert LexerParser_1.oz
\insert TreeBuilder_1.oz
%-------------------------------------------------------------------%
declare
%-------------------------------------------------------------------%
[QTk]={Module.link ["x-oz://system/wp/QTk.ozf"]} Results={NewCell nil}
Pr=[begin 'end' 'declare' 'in' tell when 'do' unless par sum next
    hide star bang async tout omit abort 'fun' 'lazy' 'if' 'then'
    'else' 'and' 'or' 'true' 'false' domain tsim]
Pa=['NtccSim']  % Lista de palabras adicionales.
%===================================================================%
%% Transforma coordenadas desde el formato 'l.c' al formato c(l c),
%% donde 'l' es la línea y 'c' es el carácter.
proc {Coordinates Lc R}
   Ct={String.tokens {Atom.toString Lc} &.}
   L={String.toInt {List.nth Ct 1}}
   C={String.toInt {List.nth Ct 2}} in
   R=c(L C)
end
%-------------------------------------------------------------------%
%% Obtiene coordenadas del cursor dadas en pos(l c), donde 'l' es línea
%% y 'c' es carácter, a partir de los índices con formato 'l.c'.
fun {CursorPos}
   L = {NewCell 1#0}
   proc {GetLine R} R=@L.1 end
   proc {GetChar R} R=@L.2 end
   proc {Update Th}
      Cr={Tk.returnAtom o(Th index insert)} Ct={Coordinates Cr} in
      L:=Ct.1#@L.2
      L:=@L.1#Ct.2
   end in
   pos(update:Update l:GetLine c:GetChar)
end
%-------------------------------------------------------------------%
Coords={CursorPos}
%-------------------------------------------------------------------%
%% Función para adicionar a lista: ej. lista de letras.
proc {AppendPos L1 I R}
   R=case L1
     of H|T then H|{AppendPos T I}
     [] nil then I|nil
     end
end
%-------------------------------------------------------------------%
%% Elimina último elemento de la lista L1.
proc {DropLast L1 R}
   L2={List.reverse L1} in
   case L2
   of _|T then R={List.reverse T}
   else R=nil
   end
end
%-------------------------------------------------------------------%
%% Entrega el índice de la primera ocurrencia de X en L.
proc {IsIndList X L R}
   proc{BelongTo X L N P}
      case L
      of nil then P=nil
      [] H|T then if X==H then P=N else {BelongTo X T N+1 P} end
      end
   end in
   R={BelongTo X L 1}
end
%-------------------------------------------------------------------%
%% 'True' si el carácter es alfanumérico. Tomado de CTMCP (Pág. 199).
fun {WordChar C}
   (&a=<C andthen C=<&z) orelse (&A=<C andthen C=<&Z) orelse
   (&0=<C andthen C=<&9) orelse {SymbChar2 C} %orelse {SymbChar1 C}
end
%-------------------------------------------------------------------%
%% 'True' si el átomo es un símbolo. Adaptado de CTMCP (Pág. 166).
fun {SymbChar0 S} % Símbolos compuestos no son necesarios.
   S=='<' orelse S=='>' orelse S=='+' orelse S=='-' orelse
   S=='=' orelse S=='/' orelse S=='*' orelse S==':' orelse
   S=='~' orelse S=='==' orelse S==':=' orelse S=='/=' orelse 
   S=='=<' orelse S=='>='
end
%-------------------------------------------------------------------%
fun {SymbChar1 S} % Símbolos compuestos no son necesarios.
   S==&< orelse S==&> orelse S==&+ orelse S==&- orelse
   S==&= orelse S==&/ orelse S==&* orelse S==&: orelse
   S==&~
end
%-------------------------------------------------------------------%
%% 'True' si el carácter es un símbolo. Adaptado de CTMCP (Pág. 166).
fun {SymbChar2 S}
   (&!=<S andthen S=<&/) orelse (&:=<S andthen S=<&@) orelse
   (&[=<S andthen S=<&`) orelse (&{=<S andthen S=<&~)
end
%-------------------------------------------------------------------%
%% Convierte lista de carácteres a un átomo. Tomado de CTMCP (Pág. 199).
fun {WordToAtom PW} {StringToAtom {Reverse PW}} end
%-------------------------------------------------------------------%
%% Entrega lista de átomos a partir de una lista de carácteres Cs.
%% Tomado de CTMCP (Pág. 199).
fun {CharsToWords PW Cs}
   case Cs
   of nil andthen PW==nil then nil
   [] nil then [{WordToAtom PW}]
   [] C|Cr andthen {WordChar C} then {CharsToWords C|PW Cr}
   [] _|Cr andthen PW==nil then {CharsToWords nil Cr}
   [] _|Cr then {WordToAtom PW}|{CharsToWords nil Cr}
   end
end
%-------------------------------------------------------------------%
%% Función que adiciona a lista de letras o de coordenadas o ambas,
%% permite borrar el último elemento de la lista o borrar el contenido
%% de la misma.
fun {AddToList}
   A={NewCell nil}
   proc {AddToList1 C}   % Pone un elemento a la vez en cola.
      A:={AppendPos @A C}
   end
   proc {GetList R}      % Recupera el contenido del buffer.
      R=@A
   end
   proc {ClearLast}      % Elimina último elemento del buffer
      A:={DropLast @A}
   end
   proc {CleanList}      % Borra todos los elementos del buffer.
      A:=nil
   end in
   addlist(add:AddToList1 get:GetList clear:ClearLast clean:CleanList)
end
%-------------------------------------------------------------------%
L={AddToList} P={AddToList} C={AddToList} Cm={AddToList}
Cd={AddToList} Ct={AddToList} Fn={AddToList}
%-------------------------------------------------------------------%
%% Procedimiento para recuperar carácteres de una palabra.
proc {ForWord Li R}
   R=for I in Li while:{WordChar I} collect:C do {C I} end
end
%-------------------------------------------------------------------%
%% Procedimiento para recuperar línea de texto actual.
proc {RecoverLine}
   Th=TextHandle
   Line={Tk.returnAtom o(Th get 'insert linestart' 'insert lineend')} in
   if {L.get}==nil then skip else {L.clean} end
   for I in {Atom.toString Line} do {L.add I} end
end
%-------------------------------------------------------------------%
%% Procedimiento para recuperar línea de texto anterior a la línea actual.
proc {RecoverPLine R}
   Th=TextHandle
   Line={Tk.returnAtom
	 o(Th get 'insert - 1 l linestart' 'insert - 1 l lineend + 1 c')} in
   R=for I in {Atom.toString Line} collect:C do {C I} end
end
%-------------------------------------------------------------------%
%% Entrega listas de carácteres, con R1 carácteres a la izquierda
%% del cursor, inclusive, y R2 carácteres a la derecha del cursor.
proc {PrevNextChars ?R1 ?R2} Y1 Z1
   Lw={L.get} Cl={Coords.l} Cc={Coords.c} in
   if Cl==1 then
      if Cc>0 andthen Cc<{List.length Lw} then
	 {List.takeDrop Lw Cc Y1 Z1} R1 = {List.reverse Y1} R2 = Z1
      elseif Cc==0 then R1=nil R2=Lw
      elseif Cc=={List.length Lw} then R1={List.reverse Lw} R2=nil
      else skip
      end
   elseif Cl>1 then
      if Cc>0 andthen Cc<{List.length Lw} then
	 {List.takeDrop Lw Cc Y1 Z1} R1 = {List.reverse Y1} R2 = Z1
      elseif Cc==0 then R1={List.reverse {RecoverPLine}} R2=Lw
      elseif Cc=={List.length Lw} then R1={List.reverse Lw} R2 = nil
      else skip
      end
   else skip
   end
end
%-------------------------------------------------------------------%
%% Procedimiento para recuperar carácteres de última palabra antes de
%% un espacio.
proc {LastWord ?R}
   Y W Cw Y1 LoopW Cl={Coords.l} Cc={Coords.c} Th=TextHandle in
   {PrevNextChars Y _}
   proc {LoopW L} L1 in
      case L of nil then Y1=L
      else if L.1==9 orelse L.1==10 orelse L.1==32 then %% Espacios
	      L1={List.subtract L L.1} {LoopW L1}       %% Elimina espacios.
	   else Y1=L
	   end
      end
   end
   if Y==nil then R=nil
   else
      {LoopW Y}
      if Y1==nil then R=nil
      else
	 W={List.reverse {ForWord Y1}}
	 Cw={Tk.returnAtom o(Th search '-exact' '-backwards' '--' W p(Cl Cc))}
	 R=W#Cw
      end
   end
end
%-------------------------------------------------------------------%
%% Procedimiento para recuperar palabra y ponerla en el buffer P.
proc {RecoverWord} Y Z in
   {PrevNextChars Y Z} {P.clean} % Y: Previous, Z: Next.
   if Y\=nil andthen Z\=nil then Y1={ForWord Y} Z1={ForWord Z} W0 in
      W0={List.append {List.reverse Y1} Z1}
      for I in W0 do {P.add I} end
   elseif Y==nil andthen Z\=nil then Z2={ForWord Z} in
      for I in Z2 do {P.add I} end
   elseif Y\=nil andthen Z==nil then Y2={ForWord Y} in
      for I in {List.reverse Y2} do {P.add I} end
   else skip
   end
end
%-------------------------------------------------------------------%
%% Entrega las coordenadas de la primer palabra antes del cursor que
%% coincide exactamente con la palabra buscada.
proc {SearchWord W}
   Th=TextHandle Cl={Coords.l} Cc={Coords.c} R Y Z in
   {C.clean} {PrevNextChars Y Z}
   if Y\=nil andthen Z\=nil then
      if {WordChar Y.1} then 
	 R={Tk.returnAtom o(Th search '-exact' '-backwards' '--' W p(Cl Cc))}
      else
	 if {WordChar Z.1} then
	    R={Tk.returnAtom o(Th search '-exact' '-forwards' '--' W p(Cl Cc))}
	 else R=nil
	 end
      end
   elseif Y==nil andthen Z\=nil then
      if {WordChar Z.1} then
	 R={Tk.returnAtom o(Th search '-exact' '-forwards' '--' W p(Cl Cc))}
      else R=Y
      end
   elseif Y\=nil andthen Z==nil then
      if {WordChar Y.1} then
	 R={Tk.returnAtom o(Th search '-exact' '-backwards' '--' W p(Cl Cc))}
      else R=Z
      end
   else R=Y
   end
   % Si no se encuentra palabra, R es '' (empty string).
   if R=='' then {C.add nil} else {C.add R} end
end
%-------------------------------------------------------------------%
%% Procedimiento para cambiar el color de las palabras después de que
%% una palabra reservada o adicional es detectada y no antes.
proc {SetWord W} Cr Lw Word in
   case W of _ then Word={P.get} else Word=W end
   {SearchWord Word} Lw={LastWord} Cr={C.get}     % Coords. de palabra buscada.
   if Cr.1==nil then skip
   else
      if Lw==nil then skip                        % Si no hay palabra atrás.
      else Cw={Coordinates Lw.2} in
	 if {List.member {StringToAtom Lw.1} Pr}  % ¿Es palabra reservada?
	 then {Tg tk(add p(Cw.1 Cw.2) p(Cw.1 Cw.2+{List.length Lw.1}))}
	 else {Tg tk(remove p(Cw.1 Cw.2) p(Cw.1 Cw.2+{List.length Lw.1}))}
	 end
	 if {List.member {StringToAtom Lw.1} Pa}  % ¿Es palabra adicional?
	 then {Ta tk(add p(Cw.1 Cw.2) p(Cw.1 Cw.2+{List.length Lw.1}))}
	 else {Ta tk(remove p(Cw.1 Cw.2) p(Cw.1 Cw.2+{List.length Lw.1}))}
	 end
      end
      if Word==nil then skip                      % Si no hay palabra adelante.
      else Ct={Coordinates Cr.1} in
	 if {List.member {StringToAtom Word} Pr}  % ¿Es palabra reservada?
	 then {Tg tk(add p(Ct.1 Ct.2) p(Ct.1 Ct.2+{List.length Word}))}
	 else {Tg tk(remove p(Ct.1 Ct.2) p(Ct.1 Ct.2+{List.length Word}))}
	 end
	 if {List.member {StringToAtom Word} Pa}  % ¿Es palabra adicional?
	 then {Ta tk(add p(Ct.1 Ct.2) p(Ct.1 Ct.2+{List.length Word}))}
	 else {Ta tk(remove p(Ct.1 Ct.2) p(Ct.1 Ct.2+{List.length Word}))}
	 end
      end
   end
end
%-------------------------------------------------------------------%
proc {SetWord2 Lw}
   case Lw
   of nil then skip %¿?
   [] H|T then
      case H        % X1:Lexem, X2:Line, X3:Initial Char., X4:Final Char.
      of X1#X2#X3#X4 then
	 if {List.member X1 Pr} then {Tg tk(add p(X2 X3) p(X2 X4))} end
	 if {List.member X1 Pa} then {Ta tk(add p(X2 X3) p(X2 X4))} end
	 if {SymbChar0 X1} then {Ts tk(add p(X2 X3) p(X2 X4))} end
	 if X1=='#' then {Ts tk(add p(X2 X3) p(X2 X4))} end
	 if X1=='%' then {Tc tk(add p(X2 X3) p(X2 X4))} {SetCommt2 X2 T} end
	 if X1=='fun' then {Tg tk(add p(X2 X3) p(X2 X4))} {SetFun2 T} end
      end
      {SetWord2 T}
   else skip
   end
end
%-------------------------------------------------------------------%
proc {SetCommt2 X Lw}
   case Lw
   of nil then skip %¿?
   [] H|T then
      case H        % X1:Lexem, X2:Line, X3:Initial Char., X4:Final Char.
      of _#X2#X3#X4 then
	 if X==X2 then {Tc tk(add p(X2 X3) p(X2 X4))} {SetCommt2 X T} end
      end
   end
end
%-------------------------------------------------------------------%
proc {SetFun2 Lw}
   case Lw
   of nil then skip %¿?
   [] H|T then
      case H        % X1:Lexem, X2:Line, X3:Initial Char., X4:Final Char.
      of X1#X2#X3#X4 then
	 if X1=='lazy' then {Tg tk(add p(X2 X3) p(X2 X4))} {SetFun2 T}
	 else case T
	      of H1|_ then
		 case H1
		 of Y1#Y2#Y3#Y4 then
		    if Y1=='$' then {Tf tk(add p(Y2 Y3) p(Y2 Y4))} end
		 end
	      end
	 end
      end
   end
end
%-------------------------------------------------------------------%
%% Entrega las coordenadas, en Cm, del primer símbolo de comentario
%% antes del cursor.
proc {SearchCommt} B F R Y Z L Cl={Coords.l} Cc={Coords.c}
   proc {ForLine Li R} % Descarta carácteres después de '\n'.
      R=for I in Li while:I\=10 collect:C do {C I} end
   end in
   {PrevNextChars Y Z} L={ForLine Y}
   if Y\=nil andthen Z\=nil then
      B={IsIndList &% {List.reverse L}} F={IsIndList &% Z}
      if B\=nil andthen F\=nil then R=Cl#B
      elseif B==nil andthen F\=nil then R=Cl#F+Cc
      elseif B\=nil andthen F==nil then R=Cl#B
      else R=nil
      end
   elseif Y==nil andthen Z\=nil then
      F={IsIndList &% Z} R=if F==nil then Cl#F else Cl#F+Cc end
   elseif Y\=nil andthen Z==nil then
      B={IsIndList &% {List.reverse L}} R=Cl#B
   else R=Y
   end
   case R
   of nil then {Cm.clean}
   [] (_#nil) then {Cm.clean}
   else if {Cm.get}==nil then {Cm.add R}
	else if {Cm.get}.1==R then skip else {Cm.clean} {Cm.add R} end
	end
   end
end
%-------------------------------------------------------------------%
%% Procedimiento para crear tag de comentario según las coordenadas
%% del primer símbolo de comentario guardadas en Cm.
proc {SetCommt} Ct in
   {SearchCommt}
   if {Cm.get}==nil then Ct=nil else Ct={Cm.get} end
   if Ct\=nil then
      {Tc tk(remove p({Coords.l} {Coords.c}) 'insert lineend')}
      {Tc tk(add p(Ct.1.1 Ct.1.2-1) 'insert lineend')}
   else {Tc tk(remove p({Coords.l} {Coords.c}) 'insert lineend')}
   end
end
%-------------------------------------------------------------------%
%% Procedimiento para eliminar comentarios antes de lexemizar; en el
%% que L es el texto de entrada, en forma de lista de carácteres, y
%% Lc=M=nil inicialmente.
proc {NoCommts L Lc M R}
   R=case L
     of nil then Lc
     [] H|Lr then
	if H==&% then
	   if M==nil then {NoCommts Lr Lc 1} else {NoCommts Lr Lc M} end
	elseif H==&\r orelse H==&\n then {NoCommts Lr H|Lc nil}
	else if M==nil then {NoCommts Lr H|Lc M} else {NoCommts Lr Lc M} end
	end
     end
end
%-------------------------------------------------------------------%
%% Procedimiento para crear tag de símbolo, Ts, según sus coordenadas.
proc {SetSymb Y Z} Cl={Coords.l} Cc={Coords.c} in
   case Y#Z
   of nil#nil then skip
   [] nil#Z then
      case Z
      of H|_ then if {SymbChar1 H} orelse H==10
		  then {Ts tk(add p(Cl Cc-1) p(Cl Cc))}
		  else {Ts tk(remove p(Cl Cc) p(Cl Cc))}
		  end
      else skip
      end
   [] Y#nil then
      case Y
      of H|_ then if {SymbChar1 H} then {Ts tk(add p(Cl Cc-1) p(Cl Cc))}
		  else {Ts tk(remove p(Cl Cc) p(Cl Cc))}
		  end
      else skip
      end
   [] Y#Z then
      case Y
      of H1|_ then
	 case Z
	 of H2|_ then
	    if {SymbChar1 H1} andthen {SymbChar1 H2} then
	       {Ts tk(add p(Cl Cc-1) p(Cl Cc))}
	       {Ts tk(add p(Cl Cc) p(Cl Cc+1))}
	    elseif {SymbChar1 H1}==false andthen {SymbChar1 H2} then
	       {Ts tk(remove p(Cl Cc-1) p(Cl Cc))}
	       {Ts tk(add p(Cl Cc) p(Cl Cc+1))}
	    elseif {SymbChar1 H1} andthen {SymbChar1 H2}==false then
	       {Ts tk(add p(Cl Cc-1) p(Cl Cc))}
	       {Ts tk(remove p(Cl Cc) p(Cl Cc+1))}
	    else
	       {Ts tk(remove p(Cl Cc-1) p(Cl Cc))}
	       {Ts tk(remove p(Cl Cc) p(Cl Cc+1))}
	    end
	 else skip
	 end
      else skip
      end
   end
end

%-------------------------------------------------------------------%
%% Procedimiento para crear tag de símbolo, Ts, según sus coordenadas.
proc {SetSymbol2 Lw}
   case Lw
   of nil then skip %¿?
   [] H|T then
      case H        % X1:Lexem, X2:Line, X3:Initial Char., X4:Final Char.
      of X1#X2#X3#X4 then if {SymbChar0 X1} then
			     {Ts tk(add p(X2 X3) p(X2 X4))} {SetSymbol2 T}
			  else {SetSymbol2 T}
			  end
      end
   end
end
%-------------------------------------------------------------------%
%% Función que busca el símbolo de tupla '#' y entrega sus coordenadas
%% en forma de tupla L#C, donde L es la línea y C el carácter.
proc {SearchTuple Y Z} R Cl={Coords.l} Cc={Coords.c}
   Cy={IsIndList &# {Reverse Y}} Cz={IsIndList &# Z} in
   if Y\=nil andthen Z\=nil then
      if Cy\=nil andthen Cz\=nil then R=Cl#Cy
      elseif Cy==nil andthen Cz\=nil then R=Cl#Cz+Cc
      elseif Cy\=nil andthen Cz==nil then R=Cl#Cy
      else R=nil
      end
   elseif Y==nil andthen Z\=nil then R=if Cz==nil then Cl#Cz else Cl#Cz+Cc end
   elseif Y\=nil andthen Z==nil then R=Cl#Cy
   else R=Y
   end
   case R
   of nil then {Ct.clean}
   [] (_#nil) then {Ct.clean}
   else if {Ct.get}==nil then {Ct.add R}
	else if {Ct.get}.1==R then skip else {Ct.clean} {Ct.add R} end
	end
   end
end
%-------------------------------------------------------------------%
%% Procedimiento para crear tag de tupla según sus coordenadas.
proc {SetTuple Y Z} Cd in
   {SearchTuple Y Z}
   if {Ct.get}==nil then Cd=nil else Cd={Ct.get} end
   if Cd\=nil then {Ts tk(add p(Cd.1.1 Cd.1.2-1) p(Cd.1.1 Cd.1.2))}
   else {Ts tk(remove p({Coords.l} {Coords.c}) p({Coords.l} {Coords.c}-1))}
   end
end
%-------------------------------------------------------------------%
proc {SetTuple2 Lw}
   case Lw
   of nil then skip %¿?
   [] H|T then
      case H        % X1:Lexem, X2:Line, X3:Initial Char., X4:Final Char.
      of X1#X2#X3#X4 then
	 case X1 of '#' then {Ts tk(add p(X2 X3) p(X2 X4))} {SetTuple2 T}
	 else {SetTuple2 T} end
      end
   end
end
%-------------------------------------------------------------------%
%% Función que busca el símbolo de dolar y entrega sus coordenadas en
%% forma de tupla L#C, donde L es la línea y C el carácter.
proc {SearchDollar Y Z} R Cl={Coords.l} Cc={Coords.c}
   Cy={IsIndList &$ {Reverse Y}} Cz={IsIndList &$ Z} in
   if Y\=nil andthen Z\=nil then
      if Cy\=nil andthen Cz\=nil then R=Cl#Cy
      elseif Cy==nil andthen Cz\=nil then R=Cl#Cz+Cc
      elseif Cy\=nil andthen Cz==nil then R=Cl#Cy
      else R=nil
      end
   elseif Y==nil andthen Z\=nil then R=if Cz==nil then Cl#Cz else Cl#Cz+Cc end
   elseif Y\=nil andthen Z==nil then R=Cl#Cy
   else R=Y
   end
   case R
   of nil then {Cd.clean}
   [] (_#nil) then {Cd.clean}
   else if {Cd.get}==nil
	then {Cd.add R}
	else if {Cd.get}.1==R then skip else {Cd.clean} {Cd.add R} end
	end
   end
end
%-------------------------------------------------------------------%
%% Procedimiento para crear tag del símbolo de dolar según sus coordenadas.
proc {SetDollar Y Z} Ct in
   {SearchDollar Y Z}
   if {Cd.get}==nil then Ct=nil else Ct={Cd.get} end
   if Ct\=nil then {Tf tk(add p(Ct.1.1 Ct.1.2-1) p(Ct.1.1 Ct.1.2))}
   else {Tf tk(remove p({Coords.l} {Coords.c}) p({Coords.l} {Coords.c}-1))}
   end
end
%-------------------------------------------------------------------%
%% Función que cambia el color del símbolo de dolar si pertenece a una
%% función y está precedida por las palabras reservadas 'fun' y 'lazy'
%% y por el símbolo '{' o solo por 'fun' y '{'.
proc {SetFunA Y Z} R1 R2 Cl={Coords.l} Cc={Coords.c} Word={P.get} in
   {Reverse {CharsToWords4 {Reverse Y} nil} R1} {CharsToWords4 Z nil R2}
   case Y#Z
   of nil#nil then skip
   [] _#nil then
      case R1
      of '$'|'{'|'fun'|_ then {SetDollar Y Z}
      [] '$'|'{'|lazy|'fun'|_ then {SetDollar Y Z}
      else {Tf tk(remove p(Cl Cc) 'insert lineend')}
      end
   [] _#_ then
      case {StringToAtom Word}
      of 'fun' then {SetDollar Y Z}
      [] lazy then case R1
		   of _|'fun'|_ then {SetDollar Y Z}
		   [] 'fun'|_ then {SetDollar Y Z}
		   else
		      {Tf tk(remove p(Cl Cc) 'insert lineend')}
		   end
      else {Tf tk(remove p(Cl Cc) 'insert lineend')}
      end
      case R1
      of '$'|'{'|'fun'|_ then {SetDollar Y Z}
      [] '$'|'{'|lazy|'fun'|_ then {SetDollar Y Z}
      [] '{'|'fun'|_ andthen R2.1=='$' then {SetDollar Y Z}
      [] '{'|lazy|'fun'|_ andthen R2.1=='$' then {SetDollar Y Z}
      [] 'fun'|_ then case R2 of '{'|_ then {SetDollar Y Z} else skip end
      [] lazy|'fun'|_ then case R2 of '{'|_ then {SetDollar Y Z} else skip end
      else skip
      end
   else skip
   end
end
%===================================================================%

%-------------------------------------------------------------------%
proc{SaveText}
   Contents={TextHandle get($)}
   Message="No program to save. Please write or load a ntcc program first." in
   case Contents of nil then
      {TextHandle2 set(Message)}
      raise no_program_to_save(Contents) end
   else
      Name={QTk.dialogbox save($)}
      WTitle="ntcc Simulator: "#{StringToAtom
				 {List.last {String.tokens Name &/}}} in
      {Window set(title:WTitle)}
      try
	 File={New Open.file init(name:Name flags:[write create truncate])}
	 Contents={TextHandle get($)}
      in
	 {File write(vs:Contents)}
	 {File close}
      catch _ then skip
      end
   end
end
%-------------------------------------------------------------------%
proc{SaveResults}
   Contents={TextHandle2 get($)}
   Message="No results to save. Please run a ntcc program first." in
   case Contents of nil then
      {TextHandle2 set(Message)}
      raise no_results_to_save(Contents) end
   [] X1|X2|X3|_ andthen (X1==&N andthen X2==&o andthen X3==& ) then
      {TextHandle2 set(Message)}
      raise no_results_to_save() end
   else
      Name={QTk.dialogbox save($)} in
      try
	 File={New Open.file init(name:Name flags:[write create truncate])}
      in
	 {File write(vs:@Results)}
	 {File close}
      catch _ then skip
      end
   end
end
%-------------------------------------------------------------------%
proc{LoadText}
   proc {SetToken Q} {SetWord2 {CharsToWords8 Q nil 1 0}} end
   Name={QTk.dialogbox load($)} WTitle in
   case Name
   of nil then {Window get(title:WTitle)}
   else WTitle="ntcc Simulator: "#{StringToAtom
			    {List.last {String.tokens Name &/}}}
   end
   {Window set(title:WTitle)}
   try
      File={New Open.file init(name:Name)}
      Contents={File read(list:$ size:all)}
   in
      {TextHandle set(Contents)}
      {SetToken Contents}
      if {TextHandle2 get($)}==nil
      then skip
      else {TextHandle2 set(nil)}
      end
      {File close}
   catch _ then skip
   end
end
%-------------------------------------------------------------------%
proc{RunTree}
   Contents={TextHandle get($)}
   proc {EvalLexer Q R}
      {CharsToWords4 {Reverse {NoCommts Q nil nil}} nil R}
   end
   proc {EvalParser Q R}
      {SolveOne fun {$} {Program Q _} end R}
   end
   proc {EvalTree Q C}
      {ShowTree Q C}
   end
   Message="No tree to build. Please load or write a ntcc program first." in
   if Contents==nil then
      {TextHandle2 set(Message)}
      raise tree_Needed(Contents) end
   else
      {EvalTree {EvalParser {EvalLexer Contents}}.1.4 _}
   end
end
%-------------------------------------------------------------------%
proc{RunText}
   Contents={TextHandle get($)}
   proc {EvalLexer Q R}
      {CharsToWords4 {Reverse {NoCommts Q nil nil}} nil R}
   end
   proc {EvalParser Q R}
      {SolveOne fun {$} {Program Q _} end R}
   end
   proc {EvalSim Q R} S={EvalParser {EvalLexer Q}}.1 in
      case S
      of nil then raise error_in_code end
      else case S.4
	   of sim(Sx) then R={Simulate S.1 S.2 S.3 Sx}
	   [] par(...) then R={Simulate S.1 S.2 S.3 S.4}
	   end
      end
      {Browse 'Parse Tree of the ntcc Program'#S}
   end
   proc {ResultsToTxt L N R}
      R=case L
	of nil then nil
	[] X|Xr then
	   case X
	   of aborted then
	      Xu={Append
		  {Append ['Time of simulation '#N#': '] [X]} '\n'|nil} in
	      Xu|{ResultsToTxt Xr N+1}
	   [] failed then
	      Xu={Append
		  {Append ['Time of simulation '#N#': '] [X]} '\n'|nil} in
	      Xu|{ResultsToTxt Xr N+1}
	   else
	      Xs=case X of var(...) then {Record.toListInd X} end
	      Xt=for I in Xs collect:C do
		    X0=case I
		       of X1#X2 andthen {IsInt X2} then X1#':'#X2#'  '
		       [] X1#(X2#X3) then X1#':'#X2#'..'#X3#' '
		       end in
		    {C X0}
		 end
	      Xu={Append {Append ['Time of simulation '#N#': '] Xt} '\n'|nil} in
	      Xu|{ResultsToTxt Xr N+1}
	   end
	end
   end
   Message="No simulation to show. Please load or write a ntcc program first."
in
   if Contents==nil then
      {TextHandle2 set(Message)}
      raise ntcc_Program_needed(Contents) end
   else
      R={List.toTuple '#' {List.flatten {ResultsToTxt {EvalSim Contents} 1}}} in
      {TextHandle2 set('Result of the simulation:'#'\n'#R#'End of simulation.')}
      Results:=R %{Browse 'ResultsToTxt EvalSim'#{EvalSim Contents}}
   end
end
%proc {RunGaphics} end %% To be defined.
%proc {RunTProver} end %% To be defined.
%===================================================================%

%-------------------------------------------------------------------%
TextHandle TextHandle2 SaveButton
%-------------------------------------------------------------------%
Toolbar=lr(glue:we
	   tbbutton(text:"Load"  glue:w action:LoadText)
	   tbbutton(text:"Save"  glue:w handle:SaveButton)
	   tbbutton(text:"Run"   glue:w action:RunText)
	   tbbutton(text:"Tree"  glue:w action:RunTree)
%	   tbbutton(text:"Graph" glue:w action:RunGaphics)  % Definir.
%	   tbbutton(text:"Prove" glue:w action:RunTProver)  % Definir.
	   tbbutton(text:"Clear"  glue:w action:
					    proc {$}
					       {TextHandle set('')}
					       {TextHandle2 set('')}
					       {Window
						set(title:"ntcc Simulator")}
					    end)
	   tbbutton(text:"Quit"  glue:w action:
					   proc {$} {Application.exit 0} end))
%-------------------------------------------------------------------%
Window={QTk.build td(Toolbar
		     title:"ntcc Simulator"
		     text(glue       :nswe
			  handle     :TextHandle
			  bg         :white
			  tdscrollbar:true)
		     tdrubberframe(glue:nswe
				   td(glue:nswe
				      text(glue    :nswe
					   bg      :white
					   height  :3
					   handle  :TextHandle2
					   tdscrollbar:true))))}
{TextHandle tk(configure font:{New Tk.font tkInit(family:courier size:11)})}
{TextHandle2 tk(configure font:{New Tk.font tkInit(family:courier size:10)})}
%-------------------------------------------------------------------%
Menu={QTk.buildMenu menu(tearoff:false
			 command(text:"Save Program" action:SaveText)
			 separator
			 command(text:"Save Results" action:SaveResults)
			 parent:Window)}
%-------------------------------------------------------------------%
{Window show}
%-------------------------------------------------------------------%
Ft={New Tk.font tkInit(family:courier weight:bold size:11)}
Tc={New Tk.textTag tkInit(parent     :TextHandle  % Tag comentario.
			  font       :Ft
			  foreground :brown)}
Tg={New Tk.textTag tkInit(parent     :TextHandle  % Tag palabra reservada.
			  font       :Ft
			  foreground :c(190 60 255))}
Ta={New Tk.textTag tkInit(parent     :TextHandle  % Tag palabra adicional.
			  font       :Ft
			  foreground :c(10 130 125))}
Ts={New Tk.textTag tkInit(parent     :TextHandle  % Tag símbolo.
			  font       :Ft
			  foreground :blue)}
Tf={New Tk.textTag tkInit(parent     :TextHandle  % Tag funciones.
			  font       :Ft
			  foreground :blue)}
{TextHandle tk(tag lower Tg Tc)}
{TextHandle tk(tag lower Ts Tc)}
{TextHandle tk(tag lower Tf Tc)}
%-------------------------------------------------------------------%
{SaveButton bind(event:"<1>"                      % Menu save.
		 args:[int('X') int('Y')]
		 action:proc {$ X Y} {Menu post(X Y)} end)}
%-------------------------------------------------------------------%
{TextHandle bind(event:"<KeyPress>"
		 args:[list(string('K'))]
		 action:proc{$ K}
			   {Coords.update TextHandle}       % Actualiza coords.
			   if {TextHandle get($)}==nil
			   then {L.clean} {P.clean} {C.clean}
			   else Y Z in
			      {RecoverLine} {SetCommt}
			      {RecoverWord} {SetWord _}     % Adicionar a tag.
			      {PrevNextChars Y Z} {SetFunA Y Z}
			      {SetSymb Y Z} {SetFunA Y Z}
			      {SetTuple2
			       {CharsToWords8 {L.get} nil {Coords.l} 0}}
			   end
			end)}
%-------------------------------------------------------------------%
{TextHandle bind(event:"<1>"
		 args:[list(string('K'))]
		 action:proc{$ K}
			   {Coords.update TextHandle}       % Actualiza coords.
			   if {TextHandle get($)}==nil then {L.clean} {P.clean}
			   else
			      {RecoverLine} {SetCommt}
			      {SetWord2
			       {CharsToWords8 {L.get} nil {Coords.l} 0}}
			   end
			end)}
%-------------------------------------------------------------------%
{TextHandle bind(event :"<Control-KeyPress-v>"
		 args  :[list(string('K'))]
		 action:proc{$ K}
			   {Coords.update TextHandle}       % Actualiza coords.
			   Th={TextHandle get($)} in
			   if Th==nil then {L.clean} {P.clean}
			   else
			      {RecoverLine} {SetCommt}
			      {SetWord2 {CharsToWords8 Th nil 1 0}}
			   end
			end)}
%===================================================================%
%===================================================================%



