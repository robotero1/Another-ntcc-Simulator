%===================================================================%
%%% Author:
%%%   Rodrigo Botero Ibarra <rbotero001@gmail.com>
%%%
%%% Copyright:
%%%   Rodrigo Botero Ibarra, 2022
%%=======================================================================
%% Adapted from CTM, Van Roy and Haridi, 2004, pag. 198, Section 3.7.3:
%% A word frequency application.
%-------------------------------------------------------------------%
declare
%-------------------------------------------------------------------%
fun {IsASpace C} {Char.isSpace C} end
fun {CommtChar C} C==&% end
fun {DollarChar C} C==&$ end
fun {SymbChar1 S}
   S=="<" orelse S==">" orelse S=="+" orelse S=="-" orelse
   S=="=" orelse S=="/" orelse S=="*" orelse S==":" orelse
   S=="~" orelse S=="==" orelse S==":=" orelse S=="/=" orelse 
   S=="=<" orelse S==">="
end
fun {GrpSymbs X}
   X==&( orelse X==&) orelse X==&[ orelse X==&] orelse X==&{ orelse X==&}
   orelse X==&# %orelse X==&$  % Dollar symbol is not a grouping symbol.
end
proc {WordToAtom PW R} %% Adaptado de CTM (Pág. 199).
   R=if {String.isInt PW}
     then {String.toInt {Reverse PW}}
     else {StringToAtom {Reverse PW}}
     end
end
%%=======================================================================
%% Procedimiento para lexemizar una lista Cs de carácteres, siendo W=nil.
%% La salida R es una lista de átomos de palabras o símbolos.
proc {CharsToWords4 Cs W R}
   R=case Cs
     of nil andthen W==nil then nil
     [] nil andthen W\=nil then [{WordToAtom W}]
     [] C|Cr andthen W==nil then
	if {GrpSymbs C} orelse {SymbChar1 C} orelse {DollarChar C}
	then {WordToAtom C|nil}|{CharsToWords4 Cr W}
	elseif {IsASpace C}
	then {CharsToWords4 Cr nil}
	else {CharsToWords4 Cr C|W}
	end
     [] C|Cr andthen W\=nil then
	if {GrpSymbs C} orelse {SymbChar1 C} orelse {DollarChar C}
	then {WordToAtom W}|{WordToAtom C|nil}|{CharsToWords4 Cr nil}
	elseif {IsASpace C}
	then {WordToAtom W}|{CharsToWords4 Cr nil}
	else {CharsToWords4 Cr C|W}
	end
     end
end
%%=======================================================================
%% Procedimiento para tokenizar una lista Cs de carácteres, siendo W=nil,
%% M=1 y N=0 inicialmente. La salida R es una lista de tuplas de la forma:
%% Lexema#Línea#CarácterInicial#CarácterFinal; en otras palabras, entrega
%% una lista de átomos por cada palabra y símbolo con sus respectivas
%% coordenadas L y C de inicio y fin de palabra.
proc {CharsToWords8 Cs W M N R}
   R=case Cs
     of nil andthen W==nil then nil
     [] nil andthen W\=nil then [{WordToAtom W}#M#N-{Length W}#N]
     [] C|Cr andthen W==nil then
	if {GrpSymbs C}
	   orelse {SymbChar1 C} orelse {CommtChar C} orelse {DollarChar C}
	then {WordToAtom C|nil}#M#N#N+1|{CharsToWords8 Cr W M N+1}
	elseif {IsASpace C}
	then
	   if C==&\n
	   then {CharsToWords8 Cr nil M+1 0}
	   else {CharsToWords8 Cr nil M N+1}
	   end
	else {CharsToWords8 Cr C|W M N+1}
	end
     [] C|Cr andthen W\=nil then
	if {GrpSymbs C}
	   orelse {SymbChar1 C} orelse {CommtChar C} orelse {DollarChar C}
	then
	   {WordToAtom W}#M#N-{Length W}#N|{WordToAtom C|nil}#M#N#N+1|{CharsToWords8 Cr nil M N+1}
	elseif {IsASpace C}
	then
	   if C==&\n
	   then {WordToAtom W}#M#N-{Length W}#N|{CharsToWords8 Cr nil M+1 0}
	   else {WordToAtom W}#M#N-{Length W}#N|{CharsToWords8 Cr nil M N+1}
	   end
	else {CharsToWords8 Cr C|W M N+1}
	end
     end
end
%%=======================================================================


