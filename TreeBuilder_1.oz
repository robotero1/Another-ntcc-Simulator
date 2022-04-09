%===================================================================%
%%% Author:
%%%   Rodrigo Botero Ibarra <rbotero001@gmail.com>
%%%
%%% Copyright:
%%%   Rodrigo Botero Ibarra, 2022
%===================================================================%
%% Adapted from CTM, Van Roy and Haridi, 2004, pag. 158, Section 3.4.7:
%% Drawing trees.
%-------------------------------------------------------------------%
declare
%-------------------------------------------------------------------%
[QTk] = {Module.link ["x-oz://system/wp/QTk.ozf"]}
DepthFirst Scale=30 ShowTree H T Rr Ss Tt Uu Vv
%===================================================================%
proc{CreateLine Canvas X1 Y1 X2 Y2}
   TagL={Canvas newTag($)} in
   {Canvas create(line X1 Y1 X2 Y2 fill:red width:2 tags:TagL)}
end
proc{CreateOval Canvas X Y}
   TagO={Canvas newTag($)} in
   {Canvas create(oval X-3 Y-3 X+3 Y+3 fill:blue tags:TagO)}
end
proc{CreateLabel Canvas X Y Text} Tx in
   if {IsAtom Text} then Tx={AtomToString Text}
   elseif {IsInt Text} then Tx={IntToString Text}
   else skip
   end
   {Canvas create(text X+12 Y-2 text:Tx fill:black)}
end
%-------------------------------------------------------------------%
proc {ToBinary PTree PTl PTr}
   proc {RecCycle Rec1 Rec2 N R}
      if N=<{Record.width Rec2} then
	 Rn={Record.adjoinAt Rec1 N Rec2.(N+1)} in {RecCycle Rn Rec2 N+1 R}
      else R=Rec1
      end
   end
   R1={Record.make {Record.label PTree} nil}
   R2={Record.subtract PTree 1} in
   PTl={Record.adjoinAt R1 1 PTree.1}
   PTr={RecCycle R1 R2 1}
end
%===================================================================%
proc {ParseToTree PTree R}
   Tr=tree(x:_ y:_ key:_ left:_ right:_) in
   R=if {IsTuple PTree}
     then
	if {Record.width PTree}>2
	then PTl PTr in
	   {ToBinary PTree PTl PTr}
	   {Adjoin Tr tree(key:{Record.label PTree}
			     left:{ParseToTree PTl}
			     right:{ParseToTree PTr} x:_ y:_)}
	elseif {Record.width PTree}==2
	then
	   {Adjoin Tr tree(key:{Record.label PTree}
			     left:{ParseToTree PTree.1}
			     right:{ParseToTree PTree.2} x:_ y:_)}
	elseif {Record.width PTree}==1
	then
	   {Adjoin Tr tree(key:{Record.label PTree}
			     left:{ParseToTree PTree.1} right:leaf x:_ y:_)}
	else
	   {Adjoin Tr tree(key:{Record.label PTree}
			   left:leaf right:leaf x:_ y:_)}
	end
     else
	{Adjoin Tr tree(x:_ y:_ key:PTree left:leaf right:leaf)}
     end
end
proc {Traverse PosTree Level Canvas}
   case PosTree
   of tree(x:X y:Y left:L=tree(x:XL y:YL ...) ...) then
      {CreateLine Canvas X Y XL YL}
      {Traverse L Level+1 Canvas}
   else skip end
   case PosTree
   of tree(x:X y:Y right:R=tree(x:XR y:YR ...) ...) then
      {CreateLine Canvas X Y XR YR}
      {Traverse R Level+1 Canvas}
   else skip end
   case PosTree
   of tree(x:X y:Y left:L right:R key:Z ...) then
      {CreateOval Canvas X Y}
      {CreateLabel Canvas X Y Z}
      {Traverse L Level+1 Canvas}
      {Traverse R Level+1 Canvas}
   [] leaf then
      skip
   end
end in
proc {DepthFirst Tree Level LeftLimit RootX RightLimit}
   case Tree
   of tree(x:X y:Y left:leaf right:leaf key:_ ...) then
      thread X=LeftLimit end
      thread Y=Scale*Level end
      thread RootX=X end
      thread RightLimit=X end
   [] tree(x:X y:Y left:L right:leaf key:_ ...) then
      thread X=RootX end
      thread Y=Scale*Level end
      {DepthFirst L Level+1 LeftLimit RootX RightLimit}
   [] tree(x:X y:Y left:leaf right:R key:_ ...) then
      thread X=RootX end
      thread Y=Scale*Level end
      {DepthFirst R Level+1 LeftLimit RootX RightLimit}
   [] tree(x:X y:Y left:L right:R key:_ ...) then
      LRootX LRightLimit RRootX RLeftLimit
   in
      thread X=(LRootX+RRootX) div 2 end
      thread Y=Scale*Level end
      thread RootX=X end
      thread RLeftLimit=LRightLimit+Scale end
      {DepthFirst L Level+1 LeftLimit LRootX LRightLimit}
      {DepthFirst R Level+1 RLeftLimit RRootX RightLimit}
   else skip
   end
end
%===================================================================%
proc {ShowTree PTree Canvas}
   Desc=td(canvas(handle:Canvas
		  glue:nswe
		  bg:white
		  width:500
		  height:400)
	   lr(glue:we
	      bg:white
	      label(text:" Parse Tree of the Simulation."
		    font:{New Tk.font tkInit(slant:italic size:9)}
		    bg:white
		    glue:w)
	      button(text:"Close"
		     glue:e
		     action:toplevel#close)))
   Win={QTk.build Desc}
   Sr={ParseToTree PTree} in
   {DepthFirst Sr 1 Scale _ _}
   {Traverse Sr 0 Canvas}
   {Win show(wait:true)}
end
%===================================================================%
%===================================================================%



