%===================================================================%
%%% Author:
%%%   Rodrigo Botero Ibarra <rbotero001@gmail.com>
%%%
%%% Copyright:
%%%   Rodrigo Botero Ibarra, 2022
%=======================================================================
% Este generador es arcaico, ingenuo y poco eficiente, pero es suficiente para
% el proposito de generar seudoaleatorios aparentemente no deterministas (que
% no se repiten cada vez que se reinician las simulaciones).
%=======================================================================
declare
%-----------------------------------------------------------------------
Xa = {NewCell 0} Ya = {NewCell 0} Za = {NewCell 0}
%-----------------------------------------------------------------------
% Procedimiento para obtener una semilla para el aleatorio.
proc {Sa ?DeltaT}
   T1 T2
   fun {Loop B}
      {Delay 1}
      if B < 0 then nil else B|{Loop B-1} end
   end
in
   T1 = {Property.get 'time.total'}
   {OS.srand T1*T1+T1} % Semilla provisional para el aleatorio de Mozart-Oz.
   {Wait {List.last {Loop {OS.rand} mod 500 + 101}} == 0} % Entre 100 y 600.
   T2 = {Property.get 'time.total'}
   DeltaT = T2 + T1    % ¿Se puede mejorar?
end
%-----------------------------------------------------------------------
Xa := {Sa} mod 30000 + 1 Ya := {Sa} mod 30000 + 1 Za := {Sa} mod 30000 + 1
%-----------------------------------------------------------------------
% Procedimiento {WG} para generar pseudo-aleatorios. Basado en el algoritmo
% AS 183 de Wichmann y Hill, 1982. Ver Wichmann-Hill en Wikipedia.
proc {WG ?R} % Algoritmo de Wichmann y Hill.
   Xa := (@Xa*171) mod 30269
   Ya := (@Ya*172) mod 30307
   Za := (@Za*170) mod 30323
   % Se toma la parte fraccional para formar un entero aleatorio.
   R = {FloatToInt ({IntToFloat @Xa}/30269.0 + {IntToFloat @Ya}/30307.0 +
		    {IntToFloat @Za}/30323.0) * 1000000.0} mod 1000000
end
%=======================================================================


