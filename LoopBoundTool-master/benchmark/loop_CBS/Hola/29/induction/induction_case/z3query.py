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
	y9=Function('y9',IntSort(),IntSort())
	__VERIFIER_nondet_int3=Function('__VERIFIER_nondet_int3',IntSort(),IntSort())
	__VERIFIER_nondet_int2=Function('__VERIFIER_nondet_int2',IntSort(),IntSort(),IntSort())
	_N2=Const('_N2',IntSort())
	_N1=Function('_N1',IntSort(),IntSort())
	a1=Int('a1')
	y1=Int('y1')
	c9=Function('c9',IntSort(),IntSort())
	x9=Function('x9',IntSort(),IntSort())
	_n2=Int('_n2')
	b1=Int('b1')
	_n1=Int('_n1')
	d9=Function('d9',IntSort(),IntSort())
	a9=Function('a9',IntSort(),IntSort())
	c1=Int('c1')
	x1=Int('x1')
	b9=Function('b9',IntSort(),IntSort())
	d1=Int('d1')
	main=Int('main')
        _k1=Int('_k1')
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
	_s.add(a1 == 1+_N2)
	_s.add(c1 == c9(_N2))
	_s.add(b1 == b9(_N2))
	_s.add(d1 == 2+_N2)
	_s.add(y1 == 3+(((_N2*_N2)-_N2)/2)+_N2)
	_s.add(x1 == 3+(((_N2*_N2)-_N2)/2)+_N2)
	_s.add(ForAll([_n2],Implies(_n2>=0,((0)<=(-(__VERIFIER_nondet_int2(_N1(_n2),_n2)))))))
	_s.add(ForAll([_n1,_n2],Implies(And(_n1 < _N1(_n2),And(_n1>=0,_n2>=0)),((__VERIFIER_nondet_int2(_f(_n1),_f(_n2)))>(0)))))
	_s.add(ForAll([_n2],Implies(_n2>=0,Or(_N1(_n2)==0,((__VERIFIER_nondet_int2((_N1(_n2)-1),_n2))>(0))))))
	_s.add(ForAll([_n2],Implies(_n2>=0,c9(_n2 + 1) == -_N1(_n2) + c9(_n2))))
	_s.add(ForAll([_n2],Implies(_n2>=0,b9(_n2 + 1) == -_N1(_n2) + b9(_n2))))
	_s.add(ForAll([_n2],Implies(_n2>=0,y9(_n2 + 1) == 2+_n2 + d9(_n2))))
	_s.add(ForAll([_n2],Implies(_n2>=0,x9(_n2 + 1) == 1+_n2 + c9(_n2))))
	_s.add(c9(0) == 2)
	_s.add(b9(0) == 1)
	_s.add(((0)<=(-(__VERIFIER_nondet_int3(_N2)))))
	_s.add(ForAll([_n2],Implies(And(_n2 < _N2,_n2>=0),((__VERIFIER_nondet_int3(_f(_n2)))>(0)))))
	_s.add(Or(_N2==0,((__VERIFIER_nondet_int3((_N2-1)))>(0))))
	_s.add(ForAll([_n2],_N1(_n2)>=0))
	_s.add(_N2>=0)
        _s.add(_k1>=0)
        _s.add(Not(Implies(((1+_k1+c9(_k1))==(2+_k1+b9(_k1))),((1+(_k1+1)+c9((_k1+1)))==(2+(_k1+1)+b9((_k1+1)))))))


except Exception as e:
	print "Error(Z3Query)"
	file = open('j2llogs.logs', 'a')

	file.write(str(e))
        
        print str(e)

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
