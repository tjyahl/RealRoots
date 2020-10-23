--Small file showing how M2 and realroots_old.m2 work.


--The load command loads the contents of a file.
----The "realroots_old.m2" file is in a higher folder, ".." goes up one folder.
----This isn't how to load packages, but the old version isn't written as a package.
restart
load("Documents/RealRoots/code/realroots_old.m2") --for Kelly
load("Downloads/RealRoots/code/realroots_old.m2") --for Jordy sometimes
load("realroots_old.m2") --for Jordy
load("../realroots_old.m2") --for Thomas


--This package is loaded for the command "solveSystem" to compute the solutions.
loadPackage("NumericalAlgebraicGeometry",Reload=>true)


--Consider the system
--  y^2 - x^2 - 1 = 0
--  x - y^2 + 4y - 2 = 0.
--We can see that 2 of the 4 solutions are real.
R = QQ[x,y]
F = {y^2-x^2-1,x-y^2+4*y-2}
sols = solveSystem F

I = ideal F
S = R/I


--This is the multiplication matrix m_x from Frank's paper
----can run "basis S" to see what basis this matrix is given in.
mx = regularRep(x)
basis S


--Note that the characteristic polynomial of m_x has degree 4,
----equal to the number of solutions. So this is an eliminant.
--The eigenvalues of m_x, which are the solutions of charPoly(x,Z) == 0,
----are the x-values of the solutions.
U = QQ[u]
f = charPoly(x,u)
roots f
apply(sols,z->first coordinates z)


--The real solutions to the system correspond to the real solutions 
----of the eliminant.
--First, we can count real solutions with Sturm sequences.
c = SturmSequence(f)


--we can check the variation at different points
----no command for this currently (worry about exact arithmetic over other fields?)
c/(f->sub(f,u=>1))
variations (c/(f->sub(f,u=>1)))


--can check variation at infinity and -infinity
c/signAtInfinity
variations (c/signAtInfinity)

c/signAtMinusInfinity
variations (c/signAtMinusInfinity)


--Sturm's theorem says the number of real roots in [a,b) is the variation at 'a' - variation at 'b'
variations (c/signAtMinusInfinity) - variations (c/signAtInfinity)
numRealSturm(f)

variations (c/signAtZero) - variations(c/signAtInfinity)
numPosRoots(f)


--The trace form can give more information about the roots themselves (that is, not about specific coordinates like above).
--As verified by the Sturm sequence, there are 2 real roots
numRealTrace(S)


--Both real roots are such that x-y is negative 
traceFormSignature(x-y)


--One real root is such that x-y+1>0 and the other is such that x-y+1<0
traceFormSignature(x-y+1)


--One real root has norm less than 3 and one has norm greater than 3
traceFormSignature(9-x^2-y^2)

