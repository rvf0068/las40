maxc:=500;
smallretmax:=21;

FalseDominatedVertices:=function(g) 
  local L,x,y;
   L:=[];
   for x in Vertices(g) do 
     for y in [x+1..Order(g)] do 
       if IsSubset(Adjacency(g,x),Adjacency(g,y)) then
         AddSet(L,y); 
       fi;
       if IsSubset(Adjacency(g,y),Adjacency(g,x)) then
         AddSet(L,x); 
       fi;
     od;
   od;
  return L;
end;

VerifyRetraction:=function(G,R) #Octahedra only.
 local G0,m,fuentes,V;
 if R=fail then return false; fi;

 m:=Length(R)/2;
 G0:=InducedSubgraph(G,R);
 if m=1 and not IsIsomorphicGraph(G0,DiscreteGraph(2)) then 
    return false;
 fi;
 if not IsIsomorphicGraph(G0,OctahedralGraph(m)) then
    return false;
 fi;
 fuentes:=R{[1,3..Length(R)-1]};
 V:=Union(List(fuentes,x->Difference([1..Order(G)],Adjacency(G,x))));
 if V<>[1..Order(G)] then return false; fi;
 return true;
end;

SpecialRetraction:=function(G,Q) # regresa la retraccion a la que se extiende Q o 'fail'.
  local H,V,Q1,x,KH,B,i;
  if (not IsSubsetSet([1..Order(G)],Q)) or Intersection(List(Q,x->Adjacency(G,x)))<>[] then 
      Info(YAGSInfo.InfoClass,2,"Error: Q must be a clique of G in SpecialRetraction(G,Q) ");
                         #Print("Error: Q must be a clique of G in SpecialRetraction(G,Q) ");
      return fail;
  fi;
  V:=[];
  for i in [1..Length (Q)] do 
    Q1:=Difference(Q,[Q[i]]);
    V[i]:=Intersection(List(Q1,x->Adjacency(G,x)));
    V[i]:=Difference(V[i],[Q[i]]);
    V[i]:=Intersection(V[i],Difference([1..Order(G)],Adjacency(G,Q[i])));
    if V[i]=[] then
      Info(YAGSInfo.InfoClass,2,"No candidates for vertex ",Q[i],"\n" );
               #PrintTo(AuxInfo,"No candidates for vertex ",Q[i],"\n" );
      return fail;
    fi;
  od;
  H:=GraphByRelation(Union(V),function(x,y)  
       return IsEdge(G,[x,y]) and 
        PositionProperty(V,z-> x in z)<> PositionProperty(V,z-> y in z);
     end);
  SetInfoLevel(YAGSInfo.InfoClass,0);
  KH:=ShallowCopy(Cliques(H,maxc));
  SetInfoLevel(YAGSInfo.InfoClass,1);
  Sort(KH,function(x,y) return Length(x)<Length(y); end);
  B:=KH[Length(KH)];
  B:=List(B,x->VertexNames(H)[x]);
  if Length(B)< Length(Q) then
    Info(YAGSInfo.InfoClass,2,"No complementary clique for Q=",Q,"\nBest found =", B, "\n");
             #PrintTo(AuxInfo,"No complementary clique for Q=",Q,"\nBest found =", B, "\n");
    return fail;
  fi;
  return Concatenation(List([1..Length(Q)],z->[Q[z],B[z]]));
end; 

SearchRetraction:=function(arg)#SpecialRetractions
   local Q,G,maxc,KG,r,minc;
   G:=arg[1]; 
   if IsBound(arg[2]) then maxc:=arg[2]; else maxc:=infinity; fi;
   SetInfoLevel(YAGSInfo.InfoClass,0);
   KG:=ShallowCopy(Cliques(G,maxc));;
   SetInfoLevel(YAGSInfo.InfoClass,1);
   Sort(KG,function(x,y) return Length(x)<Length(y); end);
   minc:=Length(KG[1]);
   Info(YAGSInfo.InfoClass,2,"Minimum Clique Size found:=",minc,"\n");
                      #Print("Minimum Clique Size found:=",minc,"\n");
   for Q in KG do
     if Length(Q)< 3 then continue; fi;
     Info(YAGSInfo.InfoClass,2,".");#Print("."); 
     Info(YAGSInfo.InfoClass,2,"Q=",Q,"\n");#PrintTo(AuxInfo,"Q=",Q,"\n");
     r:=SpecialRetraction(G,Q);
     if VerifyRetraction(G,r) then
        Info(YAGSInfo.InfoClass,2,"\n");#Print("\n");
        Info(YAGSInfo.InfoClass,2,"Minimum Clique Size found:=",minc,"\n");
                 #PrintTo(AuxInfo,"Minimum Clique Size found:=",minc,"\n");
        return r; 
     fi;
   od;
   Info(YAGSInfo.InfoClass,2,"\n");#Print("\n");
   Info(YAGSInfo.InfoClass,2,"Minimum Clique Size found:=",minc,"\n");
            #PrintTo(AuxInfo,"Minimum Clique Size found:=",minc,"\n");
   return fail;
end;


VerifyMorphism:=function(g,h,morph)
  local i,n;
  for i in Vertices(g) do
    if CHK_WEAK(g,h,morph{[1..i]})<> true then return false; fi;
  od;
  return true;
end;

VerifyGeneralRetraction:=function(g,morph) 
    local S;#m1,j;
    if VerifyMorphism(g,g,morph)<> true then return false; fi;
    S:=Set(morph);
    if not IsSubset([1..Order(g)],S) then return false; fi;
    #m1:=List([1..Length(morph)],i->morph[morph[i]]);
    return Filtered(S,x->morph[x]=x)=S;
end;


SmallRetraction:=function(g,r)#general retractions only for small graphs.
    local L1,L2,g1,V,CHK_SPEC,ret,M,i;
    L1:=[];M:=[];
    if Order(g)-Order(r)>=smallretmax then return fail; fi; 
      CHK_SPEC:=function(g1,g2,morph) 
        local len;
        len:=Length(morph);
        if len=0 then return true; fi;
        if len<=Length(L1) then #external var L1.
          return morph[len]=len; 
        fi;
        return true;
      end;
    while NextFullMonoMorphism(r,g,L1)<> fail do
      V:=Concatenation(L1,Difference(Vertices(g),L1));
      g1:=InducedSubgraph(g,V);
      L2:=PropertyMorphism(g1,r,[CHK_WEAK,CHK_SPEC]);
      if L2<> fail then 
         for i in [1..Order(g)] do M[i]:=L1[L2[Position(V,i)]]; od;
         #Print([L1,V,L2,M],"\n"); 
         if VerifyGeneralRetraction(g,M)<> true then 
           Print("Horror\n");
           return [M];
         fi;
         return M;
      fi;
    od;
    return fail;
end;


######################################
#No parecen ser muy útiles estas más que para gráficas aleatorias
######################################   

RandomMinimizer:=function(L,Func) 
     local x,val;
     if L=[] then return fail; fi;
     val:=Minimum(List(L,x->Func(x)));
     x:=Random(Filtered(L,x->Func(x)=val));
     return x;
end;

RRCH:=function(arg) #random, small-clique first.
    local G,A,B,Cand,Cand1,x,y,i,L;
    G:=arg[1];
    if IsBound(arg[2]) then 
      A:=arg[2]; 
    else
      A:=RandomMinimizer(Cliques(G,500),
          function(x)
            if Length(x)>=3 then return Length(x); else return 1000; fi;
          end);
      if Length(A)<=2 then Print("Horror\n"); return fail; fi;#Print(A);
    fi;
    B:=[];Cand:=[1..Order(G)];
    for x in A do
       Cand1:=Intersection(List(A,
         function(z) 
           if z=x then 
             return Difference([1..Order(G)],Union([z],Adjacency(G,z)));
           else 
             return Adjacency(G,z); 
           fi; 
         end));
       Cand1:=Intersection(Cand,Cand1);
       if Cand1=[] then #Print("\n"); 
          return fail; fi;
       Add(B,Random(Cand1)); #Print("y");
       Cand:=Intersection(Cand,Adjacency(G,B[Length(B)]));
    od;
    return Concatenation(List([1..Length(A)],z->[A[z],B[z]]));
end;


Retry:=function(arg)
  local func, args, num,i,res;
  func:= arg[1];
  args:= arg[2];
  if IsBound(arg[3]) then num:=arg[3]; else num:=100; fi;
  for i in [1..num] do
    res:=CallFuncList(func,args);
    Info(YAGSInfo.InfoClass,2,".");#PrintTo(AuxInfo,".");
    if res<> fail then break; fi; 
  od;
  Info(YAGSInfo.InfoClass,2,"\n");#PrintTo(AuxInfo,"\n");
  return res;
end;

RRRCH:=function(arg)
   local G,num;
   if IsBound(arg[2]) then
     return Retry(RRCH,[arg[1]],arg[2]);
   else
     return Retry(RRCH,[arg[1]]);
   fi;
end;
