import sys
import os
currentdirectory = os.path.dirname(os.path.realpath(__file__))
sys.path.append(currentdirectory+"/packages/setuptools/")
currentdirectory = os.path.dirname(os.path.realpath(__file__))
sys.path.append(currentdirectory+"/packages/z3/python/")
from z3 import *
init(currentdirectory+"/packages/z3")
set_param(proof=True)

try:
	_p1=Int('_p1')
	_p2=Int('_p2')
	_n=Int('_n')
	_bool=Int('_bool')
	arraySort = DeclareSort('arraySort')
	_f=Function('_f',IntSort(),IntSort())
	_ToReal=Function('_ToReal',RealSort(),IntSort())
	_ToInt=Function('_ToInt',IntSort(),RealSort())
	LARGE_INT=Int('LARGE_INT')
	_k1=Const('_k1',IntSort())
	_n1=Int('_n1')
	z6=Function('z6',IntSort(),IntSort())
	_N1=Const('_N1',IntSort())
	w6=Function('w6',IntSort(),IntSort())
	__VERIFIER_nondet_int2=Function('__VERIFIER_nondet_int2',IntSort(),IntSort())
	w1=Int('w1')
	y1=Int('y1')
	LARGE_INT1=Int('LARGE_INT1')
	x1=Int('x1')
	x6=Function('x6',IntSort(),IntSort())
	z1=Int('z1')
	y6=Function('y6',IntSort(),IntSort())
	main=Int('main')
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
	_s.add(LARGE_INT1 == LARGE_INT)
	_s.add(y1 == y6(_N1))
	_s.add(x1 == x6(_N1))
	_s.add(z1 == z6(_N1))
	_s.add(w1 == w6(_N1))
	_s.add(ForAll([_n1],Implies(_n1>=0,y6(_n1 + 1) == If(((((z6(_n1))%(2)))==(0)),y6(_n1) + 1,y6(_n1)))))
	_s.add(ForAll([_n1],Implies(_n1>=0,x6(_n1 + 1) == If(((((w6(_n1))%(2)))==(1)),x6(_n1) + 1,x6(_n1)))))
	_s.add(ForAll([_n1],Implies(_n1>=0,z6(_n1 + 1) == If(((((z6(_n1))%(2)))==(0)),z6(_n1) + 1,z6(_n1)))))
	_s.add(ForAll([_n1],Implies(_n1>=0,w6(_n1 + 1) == If(((((w6(_n1))%(2)))==(1)),w6(_n1) + 1,w6(_n1)))))
	_s.add(y6(0) == 0)
	_s.add(x6(0) == 0)
	_s.add(z6(0) == 0)
	_s.add(w6(0) == 1)
	_s.add(Or(Or(((x6(_N1))>=(LARGE_INT)),((y6(_N1))>=(LARGE_INT))),((__VERIFIER_nondet_int2(_N1))<=(0))))
	_s.add(ForAll([_n1],Implies(And(_n1 < _N1,_n1>=0),And(And(((x6(_f(_n1)))<(LARGE_INT)),((y6(_f(_n1)))<(LARGE_INT))),((__VERIFIER_nondet_int2(_f(_n1)))>(0))))))
	_s.add(Or(_N1==0,And(And(((x6((_N1-1)))<(LARGE_INT)),((y6((_N1-1)))<(LARGE_INT))),((__VERIFIER_nondet_int2((_N1-1)))>(0)))))
	_s.add(_N1>=0)
	_s.add(_k1>=0)
	_s.add(Not(Implies(x6(_k1) <= 1,((If(((((w6(_k1))%(2)))==(1)),x6(_k1) + 1,x6(_k1)))<=(1)))))

except Exception as e:
	print "Error(Z3Query)"
	file = open('j2llogs.logs', 'a')

	file.write(str(e))

	file.close()

	sys.exit(1)

try:
	result=_s.check()
	if sat==result:
		print "Counter Example"
		print _s.model()
	elif unsat==result:
		result
		try:
			if os.path.isfile('j2llogs.logs'):
				file = open('j2llogs.logs', 'a')
				file.write("\n**************\nProof Details\n**************\n"+str(_s.proof().children())+"\n")
				file.close()
			else:
				file = open('j2llogs.logs', 'w')
				file.write("\n**************\nProof Details\n**************\n"+str(_s.proof().children())+"\n")
				file.close()
		except Exception as e:
			file = open('j2llogs.logs', 'a')
			file.write("\n**************\nProof Details\n**************\n"+"Error"+"\n")
			file.close()
		print "Successfully Proved"
	else:
		print "Failed To Prove"
except Exception as e:
	print "Error(Z3Query)"
	file = open('j2llogs.logs', 'a')

	file.write(str(e))

	file.close()
