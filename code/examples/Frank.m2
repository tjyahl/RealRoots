---
---
--
restart
path = {"./RealRoots/code"} | path 
recursionLimit=10000
loadPackage("RealRoots", Reload => true)
needsPackage "RealRoots";
check  "RealRoots";
installPackage("RealRoots", RemakeAllDocumentation => true, Verbose => false)
viewHelp "RealRoots"


restart
loadPackage("RealRoots");
---  Section1
printWidth =70
restart
path = {"./RealRoots/code"} | path 
truncateOutput 70
loadPackage("RealRoots");
variations({2,-3,0,-8,12,0,0,8,-12,0})
R = QQ[x];
f = x*(2*x-3)*(x^4-2)^2
BudanFourierBound(f, 0, infinity)
BudanFourierBound(f, -2, 1)
SylvesterCount(f, x^2-1, -2, 3)
SturmCount(f)
realRootIsolation(f,1/5)
SturmCount(f, -1, 2, Multiplicity=>true)
HurwitzMatrix( x^4 + 5*x^3 + 7*x^2 + 11*x + 13 ) 
isHurwitzStable( x^4 + 5*x^3 + 7*x^2 + 11*x + 13 ) 
isHurwitzStable( x^4 + 9*x^3 + 7*x^2 + 5*x + 3 )
-------------   end Section 1   ---------------
S=QQ[x,y]
I = ideal(5-3*x^2-3*y^2+x^2*y^2, 1+2*x*y+4*x*y^2-3*x^2*y)
f = x+y 
regularRepresentation(f,I)
g = univariateEliminant(f,I)
T=ring(g)
gens gb ideal(g,diff(Z,g))
SturmCount(g)
rationalUnivariateRepresentation(I)
--(h,k,l)=rationalUnivariateRepresentation(I);
-------------   end Section 2   ---------------
rank traceForm(1_S,I)
traceCount(I)
traceSignature(y^2+2*y,I)
traceSignature(y,I)

