--
restart
loadPackage("RealRoots",FileName=>"../RealRoots.m2")

R = QQ[x,y]
I = ideal(x^2,x*y,y^2)
rationalUnivariateRepresentation(I)


