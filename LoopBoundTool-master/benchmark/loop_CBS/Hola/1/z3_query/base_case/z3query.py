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
        _power=Function('_power',IntSort(),IntSort(),IntSort())
	t2_var1=Int('t2_var1')
	_n1=Int('_n1')
	t1_var=Int('t1_var')
	t2_var4=Function('t2_var4',IntSort(),IntSort())
	_N1=Const('_N1',IntSort())
	t2_var=Int('t2_var')
	__VERIFIER_nondet_int2=Function('__VERIFIER_nondet_int2',IntSort(),IntSort())
	y1=Int('y1')
	t1_var4=Function('t1_var4',IntSort(),IntSort())
	x1=Int('x1')
	y4=Function('y4',IntSort(),IntSort())
	x4=Function('x4',IntSort(),IntSort())
	t1_var1=Int('t1_var1')
	main=Int('main')
	_s=Solver()
	_s.add(ForAll([_n],Implies(_n>=0, _f(_n)==_n)))
	_s.set("timeout",50000)
        _s.add(ForAll([_p1],Implies(_p1>=0, _power(0,_p1)==0)))
        _s.add(ForAll([_p1,_p2],Implies(_power(_p2,_p1)==0,_p2==0)))
        _s.add(ForAll([_p1],Implies(_p1>0, _power(_p1,0)==1)))
        _s.add(ForAll([_p1,_p2],Implies(_power(_p1,_p2)==1,Or(_p1==1,_p2==0))))
        _s.add(ForAll([_p1,_p2],Implies(And(_p1>0,_p2>=0), _power(_p1,_p2+1)==_power(_p1,_p2)*_p1)))
	_s.add(y1 == If(_N1==0,1,If(_N1==1,2,_power(2,(_N1+1)))))
	_s.add(x1 == If(_N1==0,1,If(_N1==1,2,_power(2,(_N1+1)))))
	_s.add(t2_var1 == If(_N1==0,1,If(_N1==1,2,_power(2,(_N1+1)))))
	_s.add(t1_var1 == If(_N1==0,1,If(_N1==1,2,_power(2,(_N1+1)))))
	_s.add(((0)<=(-(__VERIFIER_nondet_int2(_N1)))))
	_s.add(ForAll([_n1],Implies(And(_n1 < _N1,_n1>=0),((__VERIFIER_nondet_int2(_f(_n1)))>(0)))))
	_s.add(Or(_N1==0,((__VERIFIER_nondet_int2((_N1-1)))>(0))))
	_s.add(_N1>=0)
        _s.add(Not(Implies(_N1==0,(If(_N1==0,1,If(_N1==1,2,_power(2,(_N1+1))))) >= 1)))



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
