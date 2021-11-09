------------------------------------------------------
---Code to run the 27 lines example-------------------
------------------------------------------------------
restart
loadPackage("RealRoots")--load our package
loadPackage("NumericalAlgebraicGeometry")---package used for solving system of coeffs
R = QQ[c,d,e,f];
S = R[t];
T = QQ[x,y,z];
for i from 1 to 10 do {
    h = random(-100,100)*random(3,T)+random(-100,100)*random(2,T)+random(-100,100)*random(1,T) + random(-100,100);--creates random  cubic polynomial in T
    print h;
    --parametrize h with equations x(t),y(t),z(t)
    use R;
    F = sub(h,{x => t, y => c + d*t, z => e + f*t}); --x=a+bt, assume a = 0 and b = 1
    C = sub(last coefficients F, coefficientRing S);
    s = flatten entries C;
    X = solveSystem s;--check for 27 solutions
    if #X != 27 then (print "Error, not 27 solutions"; continue);
    R' = R / (ideal s);
    f = eliminant(c);
    print numSturm(f);
    }
--possibly change h in loop above using basis or two random polys and subtracting them and run more than 10 times






---------------------------------------
--code for running example one time
g = 81*(x^3+y^3+z^3)-189*(x^2*y+x^2*z+x*y^2+x*z^2+y^2*z+y*z^2)+54*x*y*z+126*(x*y+x*z+y*z)-9*(x^2+y^2+z^2)-9*(x+y+z)+1;--is a cubic surface with lines at "infinity", so we do not get 27 solutions with the code
T = QQ[x,y,z];
h = random(3,T)+random(2,T)+random(1,T) + random(QQ)--creates random  cubic polynomial in T
R = QQ[c,d,e,f];
S = R[t];
F = sub(h,{x => t, y => c + d*t, z => e + f*t});--x=a+bt, assume a = 0 and b = 1
C = sub(last coefficients F, coefficientRing S);
s = flatten entries C;
X = solveSystem s;--checks for 27 solutions
#X
R' = R / (ideal s);
f = eliminant(c);
numSturm(f)