

from pysmt.shortcuts import *

from pysmt.typing import UFXPType, SFXPType, FXP_OM, FXP_RM


from pysmt.rewritings import *


x = Symbol("x", UFXPType(2,1))

#y = Symbol("y", UFXPType(10,5))
#z = Symbol("z", UFXPType(10,5))

o = Symbol('o', FXP_OM)

r = Symbol('r', FXP_RM)


#z = Equals(x, y)

#z = x == y

#z = UFXPLt(x, y)

#zz = UFXPAdd(o, x, y)
#zzz = UFXPSub(WP, x, zz)
#zzzz = UFXPMul(o, r, x, y)
#zzzzz = UFXPDiv(o, r, x, y)

#kk = UFXPMul(o, r, x, y)

b1 = BV(1, 2)
b2 = BV(3, 2)

conv =  get_fp_bv_converter()

#a = UFXP(b1,2)
b = UFXP(b2,1)
print(conv.convert(b))
#res = UFXPAdd(ST,a,b)
model = get_model(conv.convert(UFXPLE(x, b)))
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
