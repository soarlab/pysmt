

from pysmt.shortcuts import SBV, Symbol, is_valid, Equals

from pysmt.typing import UFXPType, SFXPType, FXP_OM, FXP_RM

from pysmt.shortcuts import UFXPAdd, UFXPSub, UFXPMul, UFXPDiv, \
                            SFXPAdd, SFXPSub, SFXPMul, SFXPDiv, \
                            UFXP, SFXP, BV 


x = Symbol("x", UFXPType(10,5))

y = Symbol("y", UFXPType(10,5))

o = Symbol('o', FXP_OM)

r = Symbol('r', FXP_RM)

#z = Equals(x, y)

#z = x == y

#z = UFXPLt(x, y)

zz = UFXPAdd(o, x, y)
zzz = UFXPSub(o, x, y)
zzzz = UFXPMul(o, r, x, y)
zzzzz = UFXPDiv(o, r, x, y)

wrong = SFXPAdd(o, x, y)
