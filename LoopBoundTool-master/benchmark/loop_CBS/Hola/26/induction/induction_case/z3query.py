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
	w6=Function('w6',IntSort(),IntSort(),IntSort())
	w1=Int('w1')
	y1=Int('y1')
	LARGE_INT1=Int('LARGE_INT1')
	y4=Function('y4',IntSort(),IntSort(),IntSort())
	w8=Function('w8',IntSort(),IntSort())
	__VERIFIER_nondet_int3=Function('__VERIFIER_nondet_int3',IntSort(),IntSort(),IntSort())
	__VERIFIER_nondet_int2=Function('__VERIFIER_nondet_int2',IntSort(),IntSort(),IntSort())
	__VERIFIER_nondet_int4=Function('__VERIFIER_nondet_int4',IntSort(),IntSort())
	LARGE_INT=Int('LARGE_INT')
	_N2=Function('_N2',IntSort(),IntSort())
	_N3=Const('_N3',IntSort())
	_N1=Function('_N1',IntSort(),IntSort())
	x8=Function('x8',IntSort(),IntSort())
	z8=Function('z8',IntSort(),IntSort())
	z6=Function('z6',IntSort(),IntSort(),IntSort())
	x1=Int('x1')
	z1=Int('z1')
	x4=Function('x4',IntSort(),IntSort(),IntSort())
	y8=Function('y8',IntSort(),IntSort())
	_n2=Int('_n2')
	_n3=Int('_n3')
	_n1=Int('_n1')
        _k1=Int('_k1')
	main=Int('main')
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
	_s.add(LARGE_INT1 == LARGE_INT)
	_s.add(y1 == y8(_N3))
	_s.add(x1 == x8(_N3))
	_s.add(z1 == z8(_N3))
	_s.add(w1 == w8(_N3))
	_s.add(ForAll([_n3],Implies(_n3>=0,Or(Or(((x4(_N1(_n3), _n3))>(LARGE_INT)),((y4(_N1(_n3), _n3))>(LARGE_INT))),((__VERIFIER_nondet_int2(_N1(_n3),_n3))<=(0))))))
	_s.add(ForAll([_n1,_n3],Implies(And(_n1 < _N1(_n3),And(_n1>=0,_n3>=0)),And(And(((x4(_f(_n1), _f(_n3)))<=(LARGE_INT)),((y4(_f(_n1), _f(_n3)))<=(LARGE_INT))),((__VERIFIER_nondet_int2(_f(_n1),_f(_n3)))>(0))))))
	_s.add(ForAll([_n3],Implies(_n3>=0,Or(_N1(_n3)==0,And(And(((x4((_N1(_n3)-1), _n3))<=(LARGE_INT)),((y4((_N1(_n3)-1), _n3))<=(LARGE_INT))),((__VERIFIER_nondet_int2((_N1(_n3)-1),_n3))>(0)))))))
	_s.add(ForAll([_n3,_n2],Implies(And(_n3>=0,_n2>=0),z6(_n2 + 1, _n3) == x8(_n3)+_N1(_n3) + y8(_n3)+_N1(_n3))))
	_s.add(ForAll([_n3,_n2],Implies(And(_n3>=0,_n2>=0),w6(_n2 + 1, _n3) == x8(_n3)+_N1(_n3) + y8(_n3)+_N1(_n3) + 1)))
	_s.add(ForAll([_n3],z6(0, _n3) == z8(_n3)))
	_s.add(ForAll([_n3],w6(0, _n3) == w8(_n3)))
	_s.add(ForAll([_n3],Implies(_n3>=0,Or(((w6(_N2(_n3), _n3))>(LARGE_INT)),((__VERIFIER_nondet_int3(_N2(_n3),_n3))<=(0))))))
	_s.add(ForAll([_n3,_n2],Implies(And(_n2 < _N2(_n3),And(_n3>=0,_n2>=0)),And(((w6(_f(_n2), _f(_n3)))<=(LARGE_INT)),((__VERIFIER_nondet_int3(_f(_n2),_f(_n3)))>(0))))))
	_s.add(ForAll([_n3],Implies(_n3>=0,Or(_N2(_n3)==0,And(((w6((_N2(_n3)-1), _n3))<=(LARGE_INT)),((__VERIFIER_nondet_int3((_N2(_n3)-1),_n3))>(0)))))))
	_s.add(ForAll([_n3],Implies(_n3>=0,y8(_n3 + 1) == y8(_n3)+_N1(_n3))))
	_s.add(ForAll([_n3],Implies(_n3>=0,x8(_n3 + 1) == x8(_n3)+_N1(_n3))))
	_s.add(ForAll([_n3],Implies(_n3>=0,z8(_n3 + 1) == z6(_N2(_n3), _n3))))
	_s.add(ForAll([_n3],Implies(_n3>=0,w8(_n3 + 1) == w6(_N2(_n3), _n3))))
	_s.add(y8(0) == 0)
	_s.add(x8(0) == 0)
	_s.add(z8(0) == 0)
	_s.add(w8(0) == 1)
	_s.add(((0)<=(-(__VERIFIER_nondet_int4(_N3)))))
	_s.add(ForAll([_n3],Implies(And(_n3 < _N3,_n3>=0),((__VERIFIER_nondet_int4(_f(_n3)))>(0)))))
	_s.add(Or(_N3==0,((__VERIFIER_nondet_int4((_N3-1)))>(0))))
	_s.add(ForAll([_n3],_N1(_n3)>=0))
	_s.add(ForAll([_n3],_N2(_n3)>=0))
	_s.add(_N3>=0)
        _s.add(_k1>=0)
        _s.add(Not(Implies((x8(_k1)==y8(_k1)),(x8(_k1+1)==y8(_k1+1)))))


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
