loadPackage("RealRoots");
variations({2,-3,0,-8,12,0,0,8,-12,0})
R = QQ[x];
f = x*(2*x-3)*(x^4-2)^2
BudanFourierBound(f, 0, infinity)
BudanFourierBound(f, -2, 1)
SylvesterCount(f, x^2-1, -2, 3)
SturmCount(f)
realRootIsolation(f,1/2)
SturmCount(f, -1, 2, Multiplicity=>true)
HurwitzMatrix( x^4 + 5*x^3 + 7*x^2 + 11*x + 13 ) 
isHurwitzStable( x^4 + 5*x^3 + 7*x^2 + 11*x + 13 ) 
isHurwitzStable( x^4 + 9*x^3 + 7*x^2 + 5*x + 3 )
