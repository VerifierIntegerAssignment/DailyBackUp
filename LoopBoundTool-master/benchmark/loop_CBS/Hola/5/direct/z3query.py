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
	z7=Function('z7',IntSort(),IntSort())
	_N2=Const('_N2',IntSort())
	_n1=Int('_n1')
	__VERIFIER_nondet_int3=Function('__VERIFIER_nondet_int3',IntSort(),IntSort())
	z1=Int('z1')
	w7=Function('w7',IntSort(),IntSort())
	_n2=Int('_n2')
	__VERIFIER_nondet_int2=Function('__VERIFIER_nondet_int2',IntSort(),IntSort(),IntSort())
	x4=Function('x4',IntSort(),IntSort(),IntSort())
	w1=Int('w1')
	y1=Int('y1')
	LARGE_INT1=Int('LARGE_INT1')
	x1=Int('x1')
	y4=Function('y4',IntSort(),IntSort(),IntSort())
	x7=Function('x7',IntSort(),IntSort())
	y7=Function('y7',IntSort(),IntSort())
	_N1=Function('_N1',IntSort(),IntSort())
	main=Int('main')
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
	_s.add(LARGE_INT1 == LARGE_INT)
	_s.add(y1 == y7(_N2))
	_s.add(x1 == x7(_N2))
	_s.add(z1 == z7(_N2))
	_s.add(w1 == w7(_N2))
	_s.add(ForAll([_n2],Implies(_n2>=0,Or(Or(((x4(_N1(_n2), _n2))>=(LARGE_INT)),((y4(_N1(_n2), _n2))>=(LARGE_INT))),((__VERIFIER_nondet_int2(_N1(_n2),_n2))<=(0))))))
	_s.add(ForAll([_n1,_n2],Implies(And(_n1 < _N1(_n2),And(_n1>=0,_n2>=0)),And(And(((x4(_f(_n1), _f(_n2)))<(LARGE_INT)),((y4(_f(_n1), _f(_n2)))<(LARGE_INT))),((__VERIFIER_nondet_int2(_f(_n1),_f(_n2)))>(0))))))
	_s.add(ForAll([_n2],Implies(_n2>=0,Or(_N1(_n2)==0,And(And(((x4((_N1(_n2)-1), _n2))<(LARGE_INT)),((y4((_N1(_n2)-1), _n2))<(LARGE_INT))),((__VERIFIER_nondet_int2((_N1(_n2)-1),_n2))>(0)))))))
	_s.add(ForAll([_n2],Implies(_n2>=0,y7(_n2 + 1) == _N1(_n2))))
	_s.add(ForAll([_n2],Implies(_n2>=0,x7(_n2 + 1) == _N1(_n2))))
	_s.add(ForAll([_n2],Implies(_n2>=0,z7(_n2 + 1) == _N1(_n2) + _N1(_n2))))
	_s.add(ForAll([_n2],Implies(_n2>=0,w7(_n2 + 1) == _N1(_n2) + _N1(_n2) + 1)))
	_s.add(y7(0) == 0)
	_s.add(x7(0) == 0)
	_s.add(z7(0) == 0)
	_s.add(w7(0) == 1)
	_s.add(Or(Or(((z7(_N2))>=(LARGE_INT)),((w7(_N2))>=(LARGE_INT))),((__VERIFIER_nondet_int3(_N2))<=(0))))
	_s.add(ForAll([_n2],Implies(And(_n2 < _N2,_n2>=0),And(And(((z7(_f(_n2)))<(LARGE_INT)),((w7(_f(_n2)))<(LARGE_INT))),((__VERIFIER_nondet_int3(_f(_n2)))>(0))))))
	_s.add(Or(_N2==0,And(And(((z7((_N2-1)))<(LARGE_INT)),((w7((_N2-1)))<(LARGE_INT))),((__VERIFIER_nondet_int3((_N2-1)))>(0)))))
	_s.add(ForAll([_n2],_N1(_n2)>=0))
	_s.add(_N2>=0)
	_s.add(Not(((x7(_N2))==(y7(_N2)))))

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
