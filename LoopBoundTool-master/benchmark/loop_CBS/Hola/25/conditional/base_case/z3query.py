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
	_n2=Int('_n2')
	LARGE_INT=Int('LARGE_INT')
	i2=Function('i2',IntSort(),IntSort(),IntSort())
	__VERIFIER_nondet_int3=Function('__VERIFIER_nondet_int3',IntSort(),IntSort())
	i1=Int('i1')
	_n1=Int('_n1')
	j1=Int('j1')
	i6=Function('i6',IntSort(),IntSort())
	_N2=Const('_N2',IntSort())
	__VERIFIER_nondet_int2=Function('__VERIFIER_nondet_int2',IntSort(),IntSort(),IntSort())
	_N1=Function('_N1',IntSort(),IntSort())
	y1=Int('y1')
	LARGE_INT1=Int('LARGE_INT1')
	x1=Int('x1')
	x6=Function('x6',IntSort(),IntSort())
	y6=Function('y6',IntSort(),IntSort())
	main=Int('main')
        _k1=Int('_k1')
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
	_s.add(LARGE_INT1 == LARGE_INT)
	_s.add(i1 == i6(_N2))
	_s.add(y1 == y6(_N2))
	_s.add(j1 == 0)
	_s.add(x1 == x6(_N2))
	_s.add(ForAll([_n1,_n2],Implies(And(_n1>=0,_n2>=0),i2(_n1 + 1, _n2) == If(((x6(_n2))==(y6(_n2))),i2(_n1, _n2) + 1,i2(_n1, _n2)))))
	_s.add(ForAll([_n2],i2(0, _n2) == i6(_n2)))
	_s.add(ForAll([_n2],Implies(_n2>=0,((0)<=(-(__VERIFIER_nondet_int2(_N1(_n2),_n2)))))))
	_s.add(ForAll([_n1,_n2],Implies(And(_n1 < _N1(_n2),And(_n1>=0,_n2>=0)),((__VERIFIER_nondet_int2(_f(_n1),_f(_n2)))>(0)))))
	_s.add(ForAll([_n2],Implies(_n2>=0,Or(_N1(_n2)==0,((__VERIFIER_nondet_int2((_N1(_n2)-1),_n2))>(0))))))
	_s.add(ForAll([_n2],Implies(_n2>=0,i6(_n2 + 1) == i2(_N1(_n2), _n2))))
	_s.add(ForAll([_n2],Implies(_n2>=0,y6(_n2 + 1) == If(i2(_N1(_n2), _n2) >= 0,y6(_n2) + 1,y6(_n2)))))
	_s.add(ForAll([_n2],Implies(_n2>=0,x6(_n2 + 1) == If(i2(_N1(_n2), _n2) >= 0,x6(_n2) + 1,x6(_n2)))))
	_s.add(i6(0) == 0)
	_s.add(y6(0) == 0)
	_s.add(x6(0) == 0)
	_s.add(Or(Or(((x6(_N2))>(LARGE_INT)),((y6(_N2))>(LARGE_INT))),((__VERIFIER_nondet_int3(_N2))<=(0))))
	_s.add(ForAll([_n2],Implies(And(_n2 < _N2,_n2>=0),And(And(((x6(_f(_n2)))<=(LARGE_INT)),((y6(_f(_n2)))<=(LARGE_INT))),((__VERIFIER_nondet_int3(_f(_n2)))>(0))))))
	_s.add(Or(_N2==0,And(And(((x6((_N2-1)))<=(LARGE_INT)),((y6((_N2-1)))<=(LARGE_INT))),((__VERIFIER_nondet_int3((_N2-1)))>(0)))))
	_s.add(ForAll([_n2],_N1(_n2)>=0))
	_s.add(_N2>=0)
        _s.add(Not(((x6(0))==(y6(0)))))


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
