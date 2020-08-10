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
	_n1=Int('_n1')
	t6=Function('t6',IntSort(),IntSort())
	s1=Int('s1')
	_N1=Const('_N1',IntSort())
	__VERIFIER_nondet_int3=Function('__VERIFIER_nondet_int3',IntSort(),IntSort())
	t1=Int('t1')
	a1=Int('a1')
	_N2=Const('_N2',IntSort())
	flag=Int('flag')
	__VERIFIER_nondet_int2=Function('__VERIFIER_nondet_int2',IntSort(),IntSort())
	b1=Int('b1')
	flag1=Int('flag1')
	y1=Int('y1')
	LARGE_INT1=Int('LARGE_INT1')
	x1=Int('x1')
	y10=Function('y10',IntSort(),IntSort())
	main=Int('main')
	power=Function('power',IntSort(),IntSort(),IntSort())
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
	_s.add(LARGE_INT1 == LARGE_INT)
	_s.add(flag1 == flag)
	_s.add(a1 == _N1)
	_s.add(b1 == _N1)
	_s.add(s1 == ((_N1 + _N1*_N1)/(2)))
	_s.add(t1 == _N1 + _N1*_N1)
	_s.add(y1 == y10(_N2))
	_s.add(x1 == ((((_N1 + _N1*_N1)-(((2)*(((_N1 + _N1*_N1)/(2)))))))+(2)))
	_s.add(Or(((_N1 + _N1*_N1)>=(LARGE_INT)),((__VERIFIER_nondet_int2(_N1))<=(0))))
	_s.add(ForAll([_n1],Implies(And(_n1 < _N1,_n1>=0),And(((_f(_n1)*_f(_n1) + _f(_n1))<(LARGE_INT)),((__VERIFIER_nondet_int2(_f(_n1)))>(0))))))
	_s.add(Or(_N1==0,And((((_N1-1) + (_N1-1)*(_N1-1))<(LARGE_INT)),((__VERIFIER_nondet_int2((_N1-1)))>(0)))))
	_s.add(ForAll([_n2],Implies(_n2>=0,y10(_n2 + 1) == If(((__VERIFIER_nondet_int3(_n2))>(0)),y10(_n2) + 1,y10(_n2) + 2))))
	_s.add(y10(0) == 0)
	_s.add(((y10(_N2))>(((((_N1 + _N1*_N1)-(((2)*(((_N1 + _N1*_N1)/(2)))))))+(2)))))
	_s.add(ForAll([_n2],Implies(And(_n2 < _N2,_n2>=0),((y10(_f(_n2)))<=(If(flag > 0,((((_N1 + _N1*_N1)-(((2)*(((_N1 + _N1*_N1)/(2)))))))+(2)),1))))))
	_s.add(Or(_N2==0,((y10((_N2-1)))<=(If(flag > 0,((((_N1 + _N1*_N1)-(((2)*(((_N1 + _N1*_N1)/(2)))))))+(2)),1)))))
	_s.add(_N1>=0)
	_s.add(_N2>=0)
	_s.add(Not(y10(_N2) <= 4))

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
