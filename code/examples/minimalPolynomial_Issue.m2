R = QQ[x,y]
I = ideal(y^2 - x^2 - 1,x - y^2 + 4*y - 2)
g = 2*x + y
minimalPolynomial(g,I)
