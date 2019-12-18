

from pysmt.shortcuts import SBV, Symbol, is_valid, Equals, Not

from pysmt.typing import UFXPType, SFXPType, FXP_OM, FXP_RM

from pysmt.shortcuts import *

from pysmt.rewritings import get_fp_real_converter


x = Symbol("x", UFXPType(10,5))

y = Symbol("y", UFXPType(10,5))
z = Symbol("z", UFXPType(10,5))

o = Symbol('o', FXP_OM)

r = Symbol('r', FXP_RM)

#z = Equals(x, y)

#z = x == y

#z = UFXPLt(x, y)

zz = UFXPAdd(o, x, y)
zzz = UFXPSub(WP, x, zz)
zzzz = UFXPMul(o, r, x, y)
zzzzz = UFXPDiv(o, r, x, y)

conv =  get_fp_real_converter()
print(conv.convert(SFXP(SBV(-1, 4), 2)))
