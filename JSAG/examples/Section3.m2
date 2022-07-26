S=QQ[x,y]
I = ideal(5-3*x^2-3*y^2+x^2*y^2, 1+2*x*y-4*x*y^2+3*x^2*y)
rank traceForm(1_S,I)
traceCount(I)
traceSignature(y,I)
