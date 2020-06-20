IsConnected:=function(G) 
   return NumberOfConnectedComponents(G)=1;
end;

IsLocalCutpoint:=function(G,x) 
   local H;
   if VertexDegree(G,x)= 0 then return false; fi;
   H:=InducedSubgraph(G,Adjacency(G,x));
  return not IsConnected(H);
end;

LocalCutpoints:=function(G) 
   return Filtered([1..Order(G)],x->IsLocalCutpoint(G,x));
end;

HasLocalCutpoints:=function(G) 
   return LocalCutpoints(G)<>[];
end;

LocalCutGraph:=function (G)
  local LCP,LCPV,G1,H,x,NewV,i;
   LCP:=LocalCutpoints(G);
   Filtered(LCP,x->VertexDegree(G,x)>1);
   if LCP=[] then return G; fi;
   x:=LCP[1];
   H:=InducedSubgraph(G,Adjacency(G,x));
   LCPV:=ConnectedComponents(H);
   LCPV:=List(LCPV,CC->List(CC,x->VertexNames(H)[x]));
   G1:=RemoveEdges(G,Cartesian([x],Union(List([2..Length(LCPV)],z->LCPV[z]))));
   NewV:=[1..Length(LCPV)-1]+Order(G);
   G1:=DisjointUnion(G1,DiscreteGraph(Length(NewV)));
   for i in [1..Length(LCPV)-1] do 
     G1:=AddEdges(G1,Cartesian([i+Order(G)],LCPV[i+1]));
   od;
   return G1;
end;

CompletelyCutGraph:=function(G) 
   local G0;
   G0:=G;
   while HasLocalCutpoints(G0) do
      G0:=LocalCutGraph(G0);
   od;
   return G0;
end;
