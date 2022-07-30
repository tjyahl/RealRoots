--- allSections.m2
-------------   Section 1   ---------------
3!  -- dummy line to get the numbnering right loadPackage("RealRoots");
variations({2,-3,0,-8,12,0,0,8,-12,0})
R = QQ[x];
f = x*(2*x-3)*(x^4-2)^2
BudanFourierBound(f, 0, infinity)
BudanFourierBound(f, -2, 1)
SylvesterCount(f, x^2-1, -2, 3)
SturmCount(f)
realRootIsolation(f,1/5)
SturmCount(f, -1, 2, Multiplicity=>true)
HurwitzMatrix(x^4 + 5*x^3 + 7*x^2 + 11*x + 13) 
isHurwitzStable(x^4 + 5*x^3 + 7*x^2 + 11*x + 13) 
isHurwitzStable(x^4 + 9*x^3 + 7*x^2 + 5*x + 3)
-------------   Section 2   ---------------
S=QQ[x,y]
I = ideal(x^2*y^2-3*x^2-3*y^2+5, -3*x^2*y+2*x*y+4*x*y^2+1)
f = x+y 
regularRepresentation(f,I)
g = univariateEliminant(f,I)
T = ring(g)
gens gb ideal(g,diff(Z,g))
SturmCount(g)
(f,ch,ph) = rationalUnivariateRepresentation(I);
f
ch
ph
-------------   Section 3   ---------------
rank traceForm(1_S,I)
signature traceForm(1_S,I)
signature traceForm(y^2+2*y,I)
