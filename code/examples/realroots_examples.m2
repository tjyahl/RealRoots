--Examples for new package
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


------------------------------------------
-----Budan Fourier examples-----
------------------------------------------

R = QQ[t];
f = (t-4)*(t-1)^2*(t+1)*(t+3)*(t+5)*(t-6)--roots at 6, 4, 1 (mult 2), -1, -3, -5
g = (2*t-1)*(3*t+8)*(t-9)*(6*t+1)--rational roots at -8/3, -1/6, 1/2, 9
p = (t-5)*(t-2)*(t+3)*(t+4)*(t-8)*(t+13)*(t-1)--roots at -13, -4, -3, 1, 2, 5, 8
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
numSturm(p,2,10)

