RequirePackage("yags");
SetInfoLevel(YAGSInfo.InfoClass,1);
Read("retraction.g");

maxc:=500;

K:=CliqueGraph;
PK:=function(g) return CompletelyParedGraph(K(g)); end;

PinchVertices:=function(g,L) 
  local j,m,C4;
  m:=Length(L);C4:=CycleGraph(4);
  j:=GraphSum(DiscreteGraph(m),List([1..m],x->C4));
  return QuotientGraph(DisjointUnion(g,j),L,Order(g)+[1,5..4*m-3]);
end;

PinchSurface:=function(g) 
  local L;
  if not IsCompactSurface(g) then return fail; fi;
  L:=Filtered(Vertices(g),x->MinDegree(Link(g,x))<2);
  return PinchVertices(g,L);
end;

SC:=function(n) 
    return Suspension(CycleGraph(n));
end;
C4:=CycleGraph(4);
C5:=CycleGraph(5);
C6:=CycleGraph(6);
K2:=CompleteGraph(2);
I2:=DiscreteGraph(2);

CatDiv:=[];
auxg:=SC(5);auxg!.name:="Suspension(CycleGraph(5))";Add(CatDiv,auxg);
auxg:=SC(6);auxg!.name:="Suspension(CycleGraph(6))";Add(CatDiv,auxg);
auxg:=SC(7);auxg!.name:="Suspension(CycleGraph(7))";Add(CatDiv,auxg);
auxg:=OctahedralGraph(3);auxg!.name:="OctahedralGraph(3)";Add(CatDiv,auxg);
auxg:=OctahedralGraph(4);auxg!.name:="OctahedralGraph(3)";Add(CatDiv,auxg);
auxg:=OctahedralGraph(5);auxg!.name:="OctahedralGraph(3)";Add(CatDiv,auxg);
auxg:=OctahedralGraph(6);auxg!.name:="OctahedralGraph(3)";Add(CatDiv,auxg);
auxg:=OctahedralGraph(7);auxg!.name:="OctahedralGraph(3)";Add(CatDiv,auxg);
auxg:=OctahedralGraph(8);auxg!.name:="OctahedralGraph(3)";Add(CatDiv,auxg);
auxg:=ClockworkGraph([[0],[0],[0]],(1,2));
      auxg!.name:="ClockworkGraph([[0],[0],[0]],(1,2))";Add(CatDiv,auxg);
auxg:=ComplementGraph(CycleGraph(10));
      auxg!.name:="ComplementGraph(CycleGraph(10))";Add(CatDiv,auxg);
auxg:=ClockworkGraph([[0,1],[1],[1,2]],(1,2));
      auxg!.name:="ClockworkGraph([[0,1],[1],[1,2]],(1,2))";Add(CatDiv,auxg);
auxg:=ClockworkGraph([[0,1],[1,2],[0,1,2]],(1,2));
      auxg!.name:="ClockworkGraph([[0,1],[1,2],[0,1,2]],(1,2))";Add(CatDiv,auxg);
auxg:=ClockworkGraph([[0],[0],[1]],(1,2));
      auxg!.name:="ClockworkGraph([[0],[0],[1]],(1,2))";Add(CatDiv,auxg);
auxg:=ClockworkGraph([[0],[1],[1]],(1,2));
      auxg!.name:="ClockworkGraph([[0],[1],[1]],(1,2))";Add(CatDiv,auxg);
auxg:=GraphSum(K2,[C4,C5]);
      auxg!.name:="GraphSum(K2,[C4,C5])";Add(CatDiv,auxg);
auxg:=GraphSum(K2,[I2,ComplementGraph(Circulant(7,[1,2]))]);
      auxg!.name:="GraphSum(K2,[I2,ComplementGraph(Circulant(7,[1,2]))])";Add(CatDiv,auxg);
#
CatUnk:=[];
auxg:=SnubDisphenoid;auxg!.name:="SnubDisphenoid";Add(CatUnk,auxg);


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

IsKConvergent:=function(arg)
  local g,maxc,g0,L,gname,reason,r,i,pos;
  #Print
  if arg=[] then
     return fail;
  fi;
  g:=arg[1];gname:="g";
  if Length(arg) >=2 then
    maxc:=arg[2];
  else
    maxc:=infinity; 
  fi;
  SetInfoLevel(YAGSInfo.InfoClass,0);
  g0:=CompletelyParedGraph(g);;
  SetInfoLevel(YAGSInfo.InfoClass,1);
  gname:="P(g)";
  if IsCliqueHelly(g0) then
    Info(YAGSInfo.InfoClass,1,gname," is Clique Helly\n");
    return true;
  fi;
  #Retracts to some in CatDiv.
  pos:=PositionProperty(CatDiv,h->SmallRetraction(g,h)<>fail);
  if pos <>fail then 
      Info(YAGSInfo.InfoClass,1,gname," retracts to ",CatDiv[pos]!.name,"\n");
      return false;
  fi;
  #Retracts to Octahedra.
  r:=SearchRetraction(g0,maxc);
  if r <> fail then 
    Info(YAGSInfo.InfoClass,1,gname," retracts to OctahedralGraph(",Length(r)/2,")\n");
    return false; 
  fi;
  L:=[g0];
  while L[Length(L)] <> fail do 
    #Clanear 
    g:=L[Length(L)];
    SetInfoLevel(YAGSInfo.InfoClass,0);
    g0:=CliqueGraph(g,maxc);
    SetInfoLevel(YAGSInfo.InfoClass,1);
    if g0=fail then
      Add(L,fail);
      continue;
    fi;
    #Desmontar
    SetInfoLevel(YAGSInfo.InfoClass,0);
    g0:=CompletelyParedGraph(g0);
    SetInfoLevel(YAGSInfo.InfoClass,1);
    #Helly?
    gname:=Concatenation("P(K^",String(Length(L)),"(g))");
    if IsCliqueHelly(g0) then
      Info(YAGSInfo.InfoClass,1,gname," is Clique Helly\n");
      return true;
    fi;
    #IsIso
    for g in L do
      if IsIsomorphicGraph(g,g0) then
        i:=Position(L,g);
        Info(YAGSInfo.InfoClass,1,gname," is isomorphic to P(K^",i,"(g))\n### Warning\n");
        return true; 
      fi; 
    od;
    #Retracts to some in CatDiv.
    pos:=PositionProperty(CatDiv,h->SmallRetraction(g0,h)<>fail);
    if pos <>fail then 
      Info(YAGSInfo.InfoClass,1,gname," retracts to ",CatDiv[pos]!.name,"\n");
      return false;
    fi;
    #Retracts to Octahedra.
    r:=SearchRetraction(g0,maxc);
    if r <> fail then 
      Info(YAGSInfo.InfoClass,1,gname," retracts to OctahedralGraph(",Length(r)/2,")\n");
      return false; 
    fi;
    Add(L,g0);   
  od;
  Info(YAGSInfo.InfoClass,1,"No more tests available\n");
  return fail; 
end;

