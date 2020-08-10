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
	break_1_flag13=Function('break_1_flag13',IntSort(),IntSort())
	j1=Int('j1')
	LARGE_INT1=Int('LARGE_INT1')
	__VERIFIER_nondet_int3=Function('__VERIFIER_nondet_int3',IntSort(),IntSort())
	__VERIFIER_nondet_int2=Int('__VERIFIER_nondet_int2')
	__VERIFIER_nondet_int4=Function('__VERIFIER_nondet_int4',IntSort(),IntSort())
	_N2=Const('_N2',IntSort())
	k1=Int('k1')
	main=Int('main')
	LARGE_INT=Int('LARGE_INT')
	i1=Int('i1')
	_N3=Const('_N3',IntSort())
	_N1=Const('_N1',IntSort())
	pvlen1=Int('pvlen1')
	t6=Function('t6',IntSort(),IntSort())
	_n3=Int('_n3')
	_n1=Int('_n1')
	t1=Int('t1')
	_n2=Int('_n2')
	break_1_flag1=Int('break_1_flag1')
	t=Int('t')
	n1=Int('n1')
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
	_s.add(LARGE_INT1 == LARGE_INT)
	_s.add(break_1_flag1 == break_1_flag13(_N3))
	_s.add(i1 == _N2 - _N3)
	_s.add(k1 == _N2 - _N3)
	_s.add(j1 == _N3)
	_s.add(main == 0)
	_s.add(n1 == _N2)
	_s.add(t1 == t6(_N2))
	_s.add(pvlen1 == If(((_N1)>(__VERIFIER_nondet_int2)),_N1,__VERIFIER_nondet_int2))
	_s.add(Or(((_N1)>=(LARGE_INT)),((__VERIFIER_nondet_int3(_N1))<=(0))))
	_s.add(ForAll([_n1],Implies(And(_n1 < _N1,_n1>=0),And(((_f(_n1))<(LARGE_INT)),((__VERIFIER_nondet_int3(_f(_n1)))>(0))))))
	_s.add(Or(_N1==0,And((((_N1-1))<(LARGE_INT)),((__VERIFIER_nondet_int3((_N1-1)))>(0)))))
	_s.add(ForAll([_n2],Implies(_n2>=0,t6(_n2 + 1) == _n2)))
	_s.add(t6(0) == t)
	_s.add(Or(((_N2)>=(LARGE_INT)),((__VERIFIER_nondet_int4(_N2))<=(0))))
	_s.add(ForAll([_n2],Implies(And(_n2 < _N2,_n2>=0),And(((_f(_n2))<(LARGE_INT)),((__VERIFIER_nondet_int4(_f(_n2)))>(0))))))
	_s.add(Or(_N2==0,And((((_N2-1))<(LARGE_INT)),((__VERIFIER_nondet_int4((_N2-1)))>(0)))))
	_s.add(ForAll([_n3],Implies(_n3>=0,break_1_flag13(_n3 + 1) == If(_n3 + 1 >= _N2,1,0))))
	_s.add(break_1_flag13(0) == 0)
	_s.add(Or(((1)<=(0)),((break_1_flag13(_N3))!=(0))))
	_s.add(ForAll([_n3],Implies(And(_n3 < _N3,_n3>=0),And(((1)>(0)),((break_1_flag13(_f(_n3)))==(0))))))
	_s.add(Or(_N3==0,And(((1)>(0)),((break_1_flag13((_N3-1)))==(0)))))
	_s.add(_N1>=0)
	_s.add(_N2>=0)
	_s.add(_N3>=0)
	_s.add(Not(ForAll([_n3],Implies(And(_n3<_N3,_n3>=0),_N2 - _n3 >= 0))))

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
