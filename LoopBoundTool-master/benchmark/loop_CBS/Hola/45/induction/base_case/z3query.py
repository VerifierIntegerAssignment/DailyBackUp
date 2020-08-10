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
	z15=Function('z15',IntSort(),IntSort())
	w15=Function('w15',IntSort(),IntSort())
	j1=Int('j1')
	w1=Int('w1')
	y1=Int('y1')
	LARGE_INT1=Int('LARGE_INT1')
	d1=Int('d1')
	__VERIFIER_nondet_int3=Function('__VERIFIER_nondet_int3',IntSort(),IntSort())
	__VERIFIER_nondet_int2=Int('__VERIFIER_nondet_int2')
	__VERIFIER_nondet_int5=Function('__VERIFIER_nondet_int5',IntSort(),IntSort())
	__VERIFIER_nondet_int4=Function('__VERIFIER_nondet_int4',IntSort(),IntSort(),IntSort())
	_N2=Function('_N2',IntSort(),IntSort())
	flag1=Int('flag1')
	j6=Function('j6',IntSort(),IntSort())
	LARGE_INT=Int('LARGE_INT')
	i1=Int('i1')
	_N3=Const('_N3',IntSort())
	_N1=Const('_N1',IntSort())
	c1=Int('c1')
	x1=Int('x1')
	z1=Int('z1')
	_n2=Int('_n2')
	_n3=Int('_n3')
	_n1=Int('_n1')
	y15=Function('y15',IntSort(),IntSort())
	x12=Function('x12',IntSort(),IntSort(),IntSort())
	x15=Function('x15',IntSort(),IntSort())
	y12=Function('y12',IntSort(),IntSort(),IntSort())
	main=Int('main')
        _k1=Int('_k1')
	power=Function('power',IntSort(),IntSort(),IntSort())
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
	_s.add(LARGE_INT1 == LARGE_INT)
	_s.add(c1 == 0)
	_s.add(d1 == 1)
	_s.add(i1 == ((_N1 + _N1*_N1)/(2)))
	_s.add(j1 == If(((__VERIFIER_nondet_int2)>(0)),(_N1*_N1-_N1)/2 + 2*_N1,(_N1*_N1-_N1)/2 + _N1))
	_s.add(flag1 == __VERIFIER_nondet_int2)
	_s.add(w1 == w15(_N3))
	_s.add(y1 == y15(_N3))
	_s.add(x1 == x15(_N3))
	_s.add(z1 == z15(_N3))
	_s.add(ForAll([_n1],Implies(_n1>=0,j6(_n1 + 1) == If(((__VERIFIER_nondet_int2)>(0)),(_n1*_n1-_n1)/2 + j6(_n1) + 2*_n1,(_n1*_n1-_n1)/2 + j6(_n1) + _n1))))
	_s.add(j6(0) == 0)
	_s.add(Or(((j6(_N1))>=(LARGE_INT)),((__VERIFIER_nondet_int3(_N1))<=(0))))
	_s.add(ForAll([_n1],Implies(And(_n1 < _N1,_n1>=0),And(((If(((__VERIFIER_nondet_int2)>(0)),(_n1*_n1-_N1)/2 + 2*_n1,(_n1*_n1-_n1)/2 + _n1))<(LARGE_INT)),((__VERIFIER_nondet_int3(_f(_n1)))>(0))))))
	_s.add(Or(_N1==0,And(((j6((_N1-1)))<(LARGE_INT)),((__VERIFIER_nondet_int3((_N1-1)))>(0)))))
	_s.add(ForAll([_n3,_n2],Implies(And(_n3>=0,_n2>=0),y12(_n2 + 1, _n3) == If(((((z15(_n3))%(2)))==(0)),y12(_n2, _n3) + 1,y12(_n2, _n3)))))
	_s.add(ForAll([_n3,_n2],Implies(And(_n3>=0,_n2>=0),x12(_n2 + 1, _n3) == If(((((w15(_n3))%(2)))==(1)),x12(_n2, _n3) + 1,x12(_n2, _n3)))))
	_s.add(ForAll([_n3],y12(0, _n3) == y15(_n3)))
	_s.add(ForAll([_n3],x12(0, _n3) == x15(_n3)))
	_s.add(ForAll([_n3],Implies(_n3>=0,((0)<=(-(__VERIFIER_nondet_int4(_N2(_n3),_n3)))))))
	_s.add(ForAll([_n3,_n2],Implies(And(_n2 < _N2(_n3),And(_n3>=0,_n2>=0)),((__VERIFIER_nondet_int4(_f(_n2),_f(_n3)))>(0)))))
	_s.add(ForAll([_n3],Implies(_n3>=0,Or(_N2(_n3)==0,((__VERIFIER_nondet_int4((_N2(_n3)-1),_n3))>(0))))))
	_s.add(ForAll([_n3],Implies(_n3>=0,y15(_n3 + 1) == y12(_N2(_n3), _n3))))
	_s.add(ForAll([_n3],Implies(_n3>=0,x15(_n3 + 1) == x12(_N2(_n3), _n3))))
	_s.add(ForAll([_n3],Implies(_n3>=0,z15(_n3 + 1) == x12(_N2(_n3), _n3) + y12(_N2(_n3), _n3))))
	_s.add(ForAll([_n3],Implies(_n3>=0,w15(_n3 + 1) == x12(_N2(_n3), _n3) + y12(_N2(_n3), _n3) + 1)))
	_s.add(y15(0) == _N1)
	_s.add(x15(0) == If(((If(((__VERIFIER_nondet_int2)>(0)),(_N1*_N1-_N1)/2 + 2*_N1,(_N1*_N1-_N1)/2 + _N1))>=(((_N1 + _N1*_N1)/(2)))),_N1,_N1 + 1))
	_s.add(z15(0) == 0)
	_s.add(w15(0) == 1)
	_s.add(Or(((w15(_N3))>=(LARGE_INT)),((__VERIFIER_nondet_int5(_N3))<=(0))))
	_s.add(ForAll([_n3],Implies(And(_n3 < _N3,_n3>=0),And(((w15(_f(_n3)))<(LARGE_INT)),((__VERIFIER_nondet_int5(_f(_n3)))>(0))))))
	_s.add(Or(_N3==0,And(((w15((_N3-1)))<(LARGE_INT)),((__VERIFIER_nondet_int5((_N3-1)))>(0)))))
	_s.add(_N1>=0)
	_s.add(ForAll([_n3],_N2(_n3)>=0))
	_s.add(_N3>=0)
        _s.add(_k1>=0)
        _s.add(Not(((x15(0))==(y15(0)))))


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
