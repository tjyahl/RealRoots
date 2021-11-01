---Load RealRoots.m2 as a package & view documentation for the package
loadPackage("RealRoots")
viewHelp("RealRoots") --opens documentation page

------------------------------------------
-----variation examples-----
------------------------------------------

c1 = {4, 5, -1, -11, 13, -9, 8}
variations(c1)
c2 = {9, 0, 1, 0, -1, -2, 11, 0, 14}
variations(c2)
l = for i to 5 list random(-50,50)
variations(l)
R = QQ[t];
f = (t-4)*(t-1)^2*(t+1)*(t+3)*(t+5)*(t-6);
fp = diff(t,f);
fpp = diff(t,fp);
q = diff(t,fpp);
a = -2;
variations({substitute(f, t=>a),substitute(fp, t=>a), substitute(fpp, t=>a),substitute(q, t=>a)})--variation of sequence of polys at a

------------------------------------------
-----Budan Fourier examples-----
------------------------------------------

R = QQ[t];
f = (t-4)*(t-1)^2*(t+1)*(t+3)*(t+5)*(t-6)--roots at 6, 4, 1 (mult 2), -1, -3, -5
g = (2*t-1)*(3*t+8)*(t-9)*(6*t+1)--rational roots at -8/3, -1/6, 1/2, 9
p = (t-5)*(t-2)*(t+3)*(t+4)*(t-8)*(t+13)*(t-1)--roots at -13, -5, -4, -3, 1, 2, 8
BudanFourierBound(f)
BudanFourierBound(g)
BudanFourierBound(p)


------------------------------------------
-----Sturm examples-----
------------------------------------------

numSturm(f)
numSturm(f,-6,0)
numSturm(f,-1,10)

numSturm(g)
numSturm(g,-3,1)
numSturm(g,0,10)

numSturm(p)
numSturm(p,-15,0)
numSturm(p,0,10)


-------------------------------------------

---Code to generate polynomials and run the 27 lines example
restart
loadPackage("RealRoots")
---package used for solving the system of coeff equations
loadPackage("NumericalAlgebraicGeometry")
--g is a cubic surface with lines at "infinity", so we do not get 27 solutions with the code
T = QQ[x,y,z];
g = 81*(x^3+y^3+z^3)-189*(x^2*y+x^2*z+x*y^2+x*z^2+y^2*z+y*z^2)+54*x*y*z+126*(x*y+x*z+y*z)-9*(x^2+y^2+z^2)-9*(x+y+z)+1;
h = random(3,T)+random(2,T)+random(1,T) + random(QQ)--creates random  cubic polynomial in T
--parametrize h with equations x(t),y(t),z(t)
R = QQ[c,d,e,f]
S = R[t]
F = sub(h,{x => t, y => c + d*t, z => e + f*t}) --x=a+bt, assume a = 0 and b = 1
C = sub(last coefficients F, coefficientRing S)
s = flatten entries C
X = solveSystem s;
#X
