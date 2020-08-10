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
	__VERIFIER_nondet_int3=Function('__VERIFIER_nondet_int3',IntSort(),IntSort(),IntSort())
	x1=Int('x1')
	__VERIFIER_nondet_int5=Function('__VERIFIER_nondet_int5',IntSort(),IntSort())
	__VERIFIER_nondet_int4=Function('__VERIFIER_nondet_int4',IntSort(),IntSort(),IntSort())
	_N2=Function('_N2',IntSort(),IntSort())
	_N3=Const('_N3',IntSort())
	_n1=Int('_n1')
	z13=Function('z13',IntSort(),IntSort())
	c=Int('c')
	c13=Function('c13',IntSort(),IntSort())
	k1=Int('k1')
	__VERIFIER_nondet_int2=Int('__VERIFIER_nondet_int2')
	y7=Function('y7',IntSort(),IntSort(),IntSort())
	_N1=Function('_N1',IntSort(),IntSort())
	_n3=Int('_n3')
	y1=Int('y1')
	c1=Int('c1')
	x13=Function('x13',IntSort(),IntSort())
	z1=Int('z1')
	y13=Function('y13',IntSort(),IntSort())
	main=Int('main')
        _k1=Int('_k1')
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
	_s.add(y1 == y13(_N3))
	_s.add(x1 == x13(_N3))
	_s.add(c1 == c13(_N3))
	_s.add(z1 == z13(_N3))
	_s.add(k1 == __VERIFIER_nondet_int2)
	#_s.add(ForAll([_n1,_n3],Implies(And(_n1>=0,_n3>=0),y7(_n1 + 1, _n3) == If(((z13(_n3))==(((((__VERIFIER_nondet_int2)+(y7(_n1, _n3))))-(_n1)))),y7(_n1, _n3) + 1,y7(_n1, _n3) - 1))))
	#_s.add(ForAll([_n3],y7(0, _n3) == y13(_n3)))
	_s.add(ForAll([_n3],Implies(_n3>=0,((0)<=(-(__VERIFIER_nondet_int3(_N1(_n3),_n3)))))))
	_s.add(ForAll([_n1,_n3],Implies(And(_n1 < _N1(_n3),And(_n1>=0,_n3>=0)),((__VERIFIER_nondet_int3(_f(_n1),_f(_n3)))>(0)))))
	_s.add(ForAll([_n3],Implies(_n3>=0,Or(_N1(_n3)==0,((__VERIFIER_nondet_int3((_N1(_n3)-1),_n3))>(0))))))
	_s.add(ForAll([_n3],Implies(_n3>=0,((0)<=(-(__VERIFIER_nondet_int4(_N2(_n3),_n3)))))))
	_s.add(ForAll([_n3,_n2],Implies(And(_n2 < _N2(_n3),And(_n3>=0,_n2>=0)),((__VERIFIER_nondet_int4(_f(_n2),_f(_n3)))>(0)))))
	_s.add(ForAll([_n3],Implies(_n3>=0,Or(_N2(_n3)==0,((__VERIFIER_nondet_int4((_N2(_n3)-1),_n3))>(0))))))
	_s.add(ForAll([_n3],Implies(_n3>=0,y13(_n3 + 1) == -_N2(_n3) + _N1(_n3)+ y13(_n3))))
	_s.add(ForAll([_n3],Implies(_n3>=0,x13(_n3 + 1) == _N1(_n3) - _N2(_n3) + x13(_n3))))
	_s.add(ForAll([_n3],Implies(_n3>=0,c13(_n3 + 1) == _N1(_n3))))
	_s.add(ForAll([_n3],Implies(_n3>=0,z13(_n3 + 1) == ((__VERIFIER_nondet_int2)+(-_N2(_n3) + _N1(_n3) + y13(_n3))))))
	_s.add(y13(0) == 0)
	_s.add(x13(0) == 0)
	_s.add(c13(0) == c)
	_s.add(z13(0) == __VERIFIER_nondet_int2)
	_s.add(((0)<=(-(__VERIFIER_nondet_int5(_N3)))))
	_s.add(ForAll([_n3],Implies(And(_n3 < _N3,_n3>=0),((__VERIFIER_nondet_int5(_f(_n3)))>(0)))))
	_s.add(Or(_N3==0,((__VERIFIER_nondet_int5((_N3-1)))>(0))))
	_s.add(ForAll([_n3],_N1(_n3)>=0))
	_s.add(ForAll([_n3],_N2(_n3)>=0))
	_s.add(_N3>=0)
        _s.add(Not(((x13(0))==(y13(0)))))

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
