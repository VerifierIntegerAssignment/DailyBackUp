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
	__VERIFIER_nondet_int3=Int('__VERIFIER_nondet_int3')
	__VERIFIER_nondet_int2=Int('__VERIFIER_nondet_int2')
	__VERIFIER_nondet_int4=Function('__VERIFIER_nondet_int4',IntSort(),IntSort())
	i1=Int('i1')
	x1=Int('x1')
	_N1=Const('_N1',IntSort())
	t1=Int('t1')
	_k1=Const('_k1',IntSort())
	_n1=Int('_n1')
	y1=Int('y1')
	y3=Function('y3',IntSort(),IntSort())
	main=Int('main')
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
	_s.add(i1 == 0)
	_s.add(y1 == If(((__VERIFIER_nondet_int2)!=(__VERIFIER_nondet_int3)),y3(_N1),__VERIFIER_nondet_int3))
	_s.add(t1 == __VERIFIER_nondet_int3)
	_s.add(main == If(((__VERIFIER_nondet_int2)==(__VERIFIER_nondet_int3)),__VERIFIER_nondet_int2,0))
	_s.add(x1 == __VERIFIER_nondet_int2)
	_s.add(ForAll([_n1],Implies(_n1>=0,y3(_n1 + 1) == If(((__VERIFIER_nondet_int2)>(0)),((y3(_n1))+(__VERIFIER_nondet_int2)),y3(_n1)))))
	_s.add(y3(0) == __VERIFIER_nondet_int3)
	_s.add(((0)<=(-(__VERIFIER_nondet_int4(_N1)))))
	_s.add(ForAll([_n1],Implies(And(_n1 < _N1,_n1>=0),((__VERIFIER_nondet_int4(_f(_n1)))>(0)))))
	_s.add(Or(_N1==0,((__VERIFIER_nondet_int4((_N1-1)))>(0))))
	_s.add(_N1>=0)
	_s.add(_k1>=0)
	_s.add(Not(Implies(Implies(((__VERIFIER_nondet_int2)!=(__VERIFIER_nondet_int3)),((y3(_k1))>=(__VERIFIER_nondet_int3))),Implies(((__VERIFIER_nondet_int2)!=(__VERIFIER_nondet_int3)),((If(((__VERIFIER_nondet_int2)>(0)),((y3(_k1))+(__VERIFIER_nondet_int2)),y3(_k1)))>=(__VERIFIER_nondet_int3))))))

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
