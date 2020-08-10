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
	i9=Function('i9',IntSort(),IntSort())
	_n2=Int('_n2')
	__VERIFIER_nondet_int3=Int('__VERIFIER_nondet_int3')
	__VERIFIER_nondet_int2=Int('__VERIFIER_nondet_int2')
	i=Int('i')
	i1=Int('i1')
	_N3=Const('_N3',IntSort())
	_N1=Function('_N1',IntSort(),IntSort())
	_N2=Function('_N2',IntSort(),IntSort())
	k1=Int('k1')
	l1=Int('l1')
	n1=Int('n1')
	_n1=Int('_n1')
	_n3=Int('_n3')
	main=Int('main')
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
	_s.add(i1 == i9(_N3))
	_s.add(k1 == _N3 + 1)
	_s.add(l1 == __VERIFIER_nondet_int3)
	_s.add(n1 == __VERIFIER_nondet_int2)
	_s.add(ForAll([_n3],Implies(_n3>=0,((_N1(_n3))>=(((-(__VERIFIER_nondet_int3))+(__VERIFIER_nondet_int2)))))))
	_s.add(ForAll([_n1,_n3],Implies(And(_n1 < _N1(_n3),And(_n1>=0,_n3>=0)),((((_f(_n1))+(__VERIFIER_nondet_int3)))<(__VERIFIER_nondet_int2)))))
	_s.add(ForAll([_n3],Implies(_n3>=0,Or(_N1(_n3)==0,(((((_N1(_n3)-1))+(__VERIFIER_nondet_int3)))<(__VERIFIER_nondet_int2))))))
	_s.add(ForAll([_n3],Implies(_n3>=0,((_N2(_n3))>=(((-(__VERIFIER_nondet_int3))+(__VERIFIER_nondet_int2)))))))
	_s.add(ForAll([_n3,_n2],Implies(And(_n2 < _N2(_n3),And(_n3>=0,_n2>=0)),((((_f(_n2))+(__VERIFIER_nondet_int3)))<(__VERIFIER_nondet_int2)))))
	_s.add(ForAll([_n3],Implies(_n3>=0,Or(_N2(_n3)==0,(((((_N2(_n3)-1))+(__VERIFIER_nondet_int3)))<(__VERIFIER_nondet_int2))))))
	_s.add(ForAll([_n3],Implies(_n3>=0,i9(_n3 + 1) == ((_N2(_n3))+(__VERIFIER_nondet_int3)))))
	_s.add(i9(0) == i)
	_s.add(((_N3)>=(((-1)+(__VERIFIER_nondet_int2)))))
	_s.add(ForAll([_n3],Implies(And(_n3 < _N3,_n3>=0),((_f(_n3) + 1)<(__VERIFIER_nondet_int2)))))
	_s.add(Or(_N3==0,(((_N3-1) + 1)<(__VERIFIER_nondet_int2))))
	_s.add(ForAll([_n3],_N1(_n3)>=0))
	_s.add(ForAll([_n3],_N2(_n3)>=0))
	_s.add(_N3>=0)
	_s.add(((__VERIFIER_nondet_int3)>(0)))
	_s.add(Not(ForAll([_n3],Implies(And(_n3<_N3,_n3>=0),1 <= _n3 + 1))))

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
