

from pysmt.shortcuts import *

from pysmt.typing import UFXPType, SFXPType, FXP_OM, FXP_RM


from pysmt.rewritings import *


#x = Symbol("x", UFXPType(2,2))

#y = Symbol("y", UFXPType(10,5))
#z = Symbol("z", UFXPType(10,5))

#o = Symbol('o', FXP_OM)

#r = Symbol('r', FXP_RM)


#z = Equals(x, y)

#z = x == y

#z = UFXPLt(x, y)

#zz = UFXPAdd(o, x, y)
#zzz = UFXPSub(WP, x, zz)
#zzzz = UFXPMul(o, r, x, y)
#zzzzz = UFXPDiv(o, r, x, y)

#kk = UFXPMul(o, r, x, y)

b1 = BV(5, 4)
b2 = BV(13, 4)
b3 = BV(2, 4)
conv =  get_fp_real_converter()

a = UFXP(b1,2)
b = UFXP(b2,2)
c = UFXP(b3,2)

#k = RealToInt(conv.convert(b))
kk=Real(3)
#print(Ceiling(conv.convert(b)))
#pip install z3-solver
res = UFXPAdd(ST,a,b)
print(conv.convert(res))
model = get_model(conv.convert(Equals(c, res)))

if model:
    print ('sat')
    print (model)
else:
    print ('unsat')
#print (conv.convert(res))
#print conv.convert(zzz)
#kk = Equals(zzz, zzz)
#kkk = Equals(k,k)
#print conv.convert(kk)
# consts
