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
	__VERIFIER_nondet_int3=Function('__VERIFIER_nondet_int3',IntSort(),IntSort())
	_N1=Const('_N1',IntSort())
	v1=Int('v1')
	i1=Int('i1')
	j=Int('j')
	v=Int('v')
	j1=Int('j1')
	c2_var1=Int('c2_var1')
	k1=Int('k1')
	__VERIFIER_nondet_int2=Int('__VERIFIER_nondet_int2')
	k7=Function('k7',IntSort(),IntSort())
	_n1=Int('_n1')
	v7=Function('v7',IntSort(),IntSort())
	c1_var1=Int('c1_var1')
	n1=Int('n1')
	main=Int('main')
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
	_s.add(j1 == j)
	_s.add(i1 == _N1)
	_s.add(k1 == k7(_N1))
	_s.add(c2_var1 == 2000)
	_s.add(main == 0)
	_s.add(n1 == __VERIFIER_nondet_int2)
	_s.add(v1 == v7(_N1))
	_s.add(c1_var1 == 4000)
	_s.add(ForAll([_n1],Implies(_n1>=0,k7(_n1 + 1) == If(((If(((((__VERIFIER_nondet_int3(_n1))%(2)))==(0)),0,1))==(0)),k7(_n1) + 4000,k7(_n1) + 2000))))
	_s.add(ForAll([_n1],Implies(_n1>=0,v7(_n1 + 1) == If(((((__VERIFIER_nondet_int3(_n1))%(2)))==(0)),0,1))))
	_s.add(k7(0) == 0)
	_s.add(v7(0) == v)
	_s.add(((_N1)>=(((-(0))+(__VERIFIER_nondet_int2)))))
	_s.add(ForAll([_n1],Implies(And(_n1 < _N1,_n1>=0),((_f(_n1))<(__VERIFIER_nondet_int2)))))
	_s.add(Or(_N1==0,(((_N1-1))<(__VERIFIER_nondet_int2))))
	_s.add(_N1>=0)
	_s.add(((__VERIFIER_nondet_int2)<(10)))
	_s.add(((__VERIFIER_nondet_int2)>(0)))
	_s.add(Not(((k7(_N1))>(__VERIFIER_nondet_int2))))

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
