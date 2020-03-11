import sys
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO # Py2-Py3 Compatibility
from pysmt.shortcuts import get_model
import time

BV = True
if BV:
    from pysmt.rewritings import get_fp_bv_converter
else:
    from pysmt.rewritings import get_fp_real_converter

with open(sys.argv[1], 'r') as f:
    QUERY=f.read()

# We read the SMT-LIB Script by creating a Parser.
# From here we can get the SMT-LIB script.
parser = SmtLibParser()

# The method SmtLibParser.get_script takes a buffer in input. We use
# cStringIO to simulate an open file.
# See SmtLibParser.get_script_fname() if to pass the path of a file.
script = parser.get_script(cStringIO(QUERY))

# The SmtLibScript provides an iterable representation of the commands
# that are present in the SMT-LIB file.
#
# Printing a summary of the issued commands
f = script.get_last_formula()

if BV:
    conv = get_fp_bv_converter()
else:
    conv = get_fp_real_converter()

F = conv.convert(f)

if BV:
    print("(set-logic QF_BV)")
else:
    print("(set-logic QF_NIRA)")

for x in F.get_free_variables():
    print("(declare-fun {} () {})".format(x.to_smtlib(), x._content.payload[1].as_smtlib(funstyle=False)))
print("(assert {})".format(F.to_smtlib()))
print("(check-sat)")

# start = time.clock()
# model = get_model(F, solver_name='cvc4', logic='QF_NIRA')
# end = time.clock()
# with open(sys.argv[1]+'-out', 'w') as out:
#     out.write("TIME: " + str(end - start) + '\n')
#     if model:
#         out.write(str(model) + '\n')
#     else:
#         out.write("UNSAT\n")
    
