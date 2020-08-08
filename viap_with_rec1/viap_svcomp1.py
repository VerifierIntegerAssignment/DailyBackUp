# February 20, 2016

# February 29, 2016: 1. change axioms for if1 and if2 to make all axioms of the form x = ... 2. add last label as an output of translate0

# March 10 - April 27: a new translation for while-loop that parameterizes loop input variables and replaces smallest macros by inductive definition. Also a small correction to simplify()

# April 29: combining the two translations (c2l.py.old3 and c2l.py.old4): keep the old translation for program variables but use a new way to inductively define smallest macro: 
# N(x,y) = if C(x,y) then 0 else C(f(x),g(x)), where f and g is the new value of x and y, respectively, after one iteration
# in c2l.py.old4, f and g are the output functions for the body, here we parameterize f and g first, and use f(1,x) and g(1,y) to replace f(x) and g(y), respectively

# May 18: (not done yet) making functions first-order objects by using "+": f+[t1,...,tk,v] stands for the
# function f1 such that forall x1,...,xk: 
# f1(x1,...,xk) = ite(x1=t1 & ... & xk=tk, v, f(x1,...,xk))
# A translator from C to FOL in python 

# June 18: add solve_rec() by Pritom to solve recurrences in translating while-loop
# assume that the only dynamic functions are the program variables given by v and the system generated temporary functions including big N (is_program_var())
# this makes _base redundant

# August 30: add function definitions and function calls and define program as a sequence of functions. See program definitions just before translate1()

#example run: translate1(fact,vfact,1) or translate1(fact,vfact,2)


"""
Assumptions:
1. Program variables:
  - can be any word \w+
  - cannot be _x\d*, _n\d*, _N\d*,_y\d* 
    (these are reserved for general variables,
    natural number variables, and smallest macro constants
    in our axioms)
  - for a variable, its temporary variants are constructed 
    by adding to it TEMP+number
    and its output values after a labeled statement are 
    constructed by adding to it LABEL+number.
    (Currently, TEMP is empty and LABEL is '_'.) 
    This menas that if V is a variable, then
    V+TEMP+\d+ and V+LABEL+\d+ are not allowed to be variables 
    (right now it means that
    V1,V2,... and V_1,V_2,... cannot be variables).
  - smallest is a reserved word so cannot be a variable
"""


import sys
import os

currentdirectory = os.path.dirname(os.path.realpath(__file__))

sys.path.append(currentdirectory+"/packages/ply/")
sys.path.append(currentdirectory+"/packages/plyj/")
sys.path.append(currentdirectory+"/packages/pyparsing/")
sys.path.append(currentdirectory+"/packages/pycparser1/")
sys.path.append(currentdirectory+"/packages/pycparserext/")
sys.path.append(currentdirectory+"/packages/regex/")
sys.path.append(currentdirectory+"/packages/mpmath/")
sys.path.append(currentdirectory+"/packages/sympy/")
sys.path.append(currentdirectory+"/packages/z3/python/")


import xml.dom.minidom
import re
import random
#add by Pritom Rajkhowa
#import numpy as np
import resource
import hashlib
#import wolframalpha
#import sys
import itertools
import plyj.parser
import plyj.model as m
import subprocess
from sympy import *
import regex
#import os
import copy
import time
import datetime
import ConfigParser
import SyntaxFilter
import commandclass
import graphclass
#import solution_closed_form
#import FOL_translation
#import fun_utiles
from pyparsing import *
from sympy.core.relational import Relational
from pycparser1 import parse_file,c_parser, c_ast, c_generator
from pycparserext.ext_c_parser import GnuCParser
from pycparserext.ext_c_generator import GnuCGenerator
from itertools import permutations
ParserElement.enablePackrat()


#resource.setrlimit(resource.RLIMIT_STACK, [0x10000000, resource.RLIM_INFINITY])
#sys.setrecursionlimit(0x100000)

#resource.setrlimit(resource.RLIMIT_STACK, (2**29,-1))
#sys.setrecursionlimit(10**6)
#os.system('ulimit -s ulimited')

sys.setrecursionlimit(100000)

def is_empty(any_structure):
    if any_structure:
        return False
    else:
        return True




def is_number(s):
    if s=='j':
    	return False
    try:
        float(s) # for int, long and float
    except ValueError:
        try:
            complex(s) # for complex
        except ValueError:
            return False
    return True


def is_hex(input_string):
    flag=True
    if input_string is None:
        return None
    try:
        flag=int(input_string, 16)
    except ValueError:
        return None

    if flag:
       if '0x' in input_string:
    	   return str(int(input_string, 16))
       else:
    	   return None
    else:
       return None
config = ConfigParser.RawConfigParser()
config.read(currentdirectory+'/config.properties')
timeout=config.get('ConfigurationSection', 'timeout');
app_id=config.get('ConfigurationSection', 'app_id');



#Time Out 
if timeout.strip()!='' and timeout.strip()!='None' and is_number(timeout.strip())!=False:
	TIMEOUT=timeout.strip()
else:
	TIMEOUT=40000

if app_id.strip()!='' and app_id.strip()!='None':
	Mathematica_id=app_id.strip()
else:
	Mathematica_id=None


# base language (non dynamic, not changed by the program)
# do not use name with number in the end
# these names are not supposed to be used as prorgam variables

_base = ['=','==','!=','<','<=','>','>=','*','**','!','+','-','/', '%', 'ite', 'and', 'or', 'not', 'implies', 'all', 'some', 'null','>>','<<','&','|','^']
_infix_op = ['=','==','!=','<','<=','>','>=','*','**','+','-','/', '%', 'implies','<<','>>','&','|','^']
_relation_op = ['==','!=','<','<=','>','>=']

# variables introduced in the translation

def isvariable(x):
    if x.startswith('_x') or  x.startswith('_y') or  x.startswith('_n') or  x.startswith('_s'):
        return True
    else:
        return False



# program variables and temporary program variables and big N

def is_program_var(x,v):
    if x.startswith('_N'):
        return True
    for y in v:
        if x==y or x.startswith(y+OUT) or (x.startswith(y+TEMP) and 
                                           x[len(y+TEMP):].isdigit()) or x.startswith(y+LABEL):
            return True
    return False


current_milli_time = lambda: int(round(time.time() * 1000))



#
#Pre-Processig of Pre-Processor
#content='#include "assert.h #define LIMIT 1000000 #define LIMIT1 1000000'
#

def preProcessorHandling(content):
    
	new_content=content.replace(';',';\n').replace('}','}\n').replace('#','\n#').replace('int','\nint').replace('void','\nvoid').replace('void','\nvoid').replace('extern','\nextern ').replace('unsigned','\nunsigned').replace('Char','\nChar')   
	lines = new_content.splitlines()
	new_lines=[]
	defineMap={}
	for line in lines:
		definematch = regex.match("#define\\s+(\\w+)\\s+(.*)",line)
		if definematch:
			#deal with define statements by saving it in a dict
			#definedict[match.group(1)] = definedict[match.group(2)]
			defineMap[definematch.group(1)]=str(simplify(definematch.group(2)))
			new_lines.append(line)
	for line in new_lines:
		content=content.replace(line,'')
	return content,defineMap


#
#Utiles Functions Start
#
#expression='n+1'

def replaceAddOperator(expression):
	p = regex.compile(r'[A-Za-z|\d|\)|\]][+][A-Za-z|\d|\(|\]]')
	result=(p.sub(lambda m: m.group().replace("+", " + "), expression))
	result=replaceAddOperator1(result)
	return result

def replaceAddOperator1(expression):
	p = regex.compile(r'[A-Za-z|\d|\s][+][A-Za-z|\d]')
	result=(p.sub(lambda m: m.group().replace("+", "+ "), expression))
	return result

#
#Utiles Functions End
#

#
#Write Log Functions Start
#

"""
Reading the contain of the file 
"""
def readingFile( filename ):
    content=None
    with open(currentdirectory+"/"+filename) as f:
    	 content = f.readlines()
    return content
 
"""
Wrtitting the contain on file 
"""
def writtingFile( filename , content ):
	file = open(currentdirectory+"/"+filename, "w")
	file.write(str(content))
	file.close()
        #if '.graphml' in filename:
        #    st = os.stat(currentdirectory+"/"+filename)
        #    print st.st_size

"""
Appending the contain on file 
"""
def appendingFile( filename , content ):
	file = open(currentdirectory+"/"+filename, "a")
	file.write(str(content))
	file.close()

"""

write logs

"""

def writeLogFile(filename , content):
	if os.path.isfile(currentdirectory+"/"+filename):
    		appendingFile( filename , content )
	else:
    		writtingFile( filename , content )
                

#
#Write Log Functions Start
#


def getVersion():
    return "1.1.12(Date 28/11/2018)"



def prove_auto(file_name,property=None):

    if not(os.path.exists(file_name)): 
       print("File not exits")
       return
            
            
    start_time=current_milli_time()
    content=None
    #witness_path=None
    #global line_error_assert
    global new_variable
    global fail_count
    global error_count
    global assume_count
    global assert_count
    global defineMap
    global defineDetaillist
    global map___VERIFIER_nondet
    global new_variable_array
    global counter_variableMap
    global counter_variableMap_Conf
    global sub_vfact
    global external_var_map
    global external_pointer_map
    global fun_call_map
    global current_fun_call
    global fun_substitution_map
    global line_no_stmt_map
    global count_ast_line_no
    global main_count_ast_line_no
    global main_line_no_stmt_ast_map
        
    line_error_assert=None
    #getLineErrorAssert(file_name)
    struct_map={}
    fail_count=0
    error_count=0
    assume_count=0
    assert_count=0
    count_ast_line_no=0
    main_count_ast_line_no=0
    map___VERIFIER_nondet={}
    new_variable_array={}
    counter_variableMap={}
    counter_variableMap_Conf={}
    fun_call_map={}
    fun_substitution_map={}
    line_no_stmt_map={}
    function_vfacts=[]
    program_analysis=''
    program_analysis2=''
    program_analysis3=''
    program_analysis_decl=''
    program_analysis_var_decl=''
    current_fun_call=None
    struct_list=None
    type_struct_list=None
    line_no_stmt_map=None
    original_program=None
    new_program=None
    flag_terminate=False
    main_line_no_stmt_ast_map={}
        
    try:
       fd = open(file_name)
       text = "".join(fd.readlines())
       original_program=text
                
       #line_error_assert = getLineErrorAssert(file_name)
                
       defineMap={}
       content,defineMap=preProcessorHandling(text)
       text=replaceAddOperator(text)
       filtered_program = SyntaxFilter.SLexer(text)
       filtered_program.build()
                
       content,struct_list,type_struct_list=filtered_program.filterSyntax()

    except SyntaxFilter.SLexerError as e:
       print('Error(Find Error in Input File)')
       #print(e)
       return
    text = r""" """+content
    parser = GnuCParser()
    #ast = parse_file(file_name, use_cpp=True)
    try:
          try:
             new_program = text
             line_no_stmt_map = constructLineStmtmap(original_program,text)
          except Exception as e:
             line_no_stmt_map=None
            
          ast = parser.parse(text)
          for struct_str in struct_list:
                
              isCorrectSyn=False

              try:
                 ast_struct = parser.parse(struct_str)
                 isCorrectSyn=True
              except Exception as e:
                 isCorrectSyn=False
                
              if isCorrectSyn==True:
                
                 struct_name=ast_struct.ext[0].type.name
                
                 isPointer=False
                
                 isTypedef=False
                
                 defName=None
                
                 variable_map=getVariablesC(ast_struct.ext[0].type.decls)
                
                 structobject = structclass(struct_name, isTypedef,  variable_map , defName, isPointer)
                
                 struct_map[struct_name]=structobject
                
          for struct_str in type_struct_list:

              isCorrectSyn=False

              try:
                 ast_struct = parser.parse(struct_str)
                 isCorrectSyn=True
              except Exception as e:
                 isCorrectSyn=False
                
              if isCorrectSyn==True:
                
                 isPointer=False
                
                 isTypedef=False
                
                 struct_name = ast_struct.ext[0].name
                
                 if type(ast_struct.ext[0]) is c_ast.Typedef:
                    isTypedef=True
                    
                 if type(ast_struct.ext[0].type) is c_ast.PtrDecl:
                    isPointer=True

                 if isPointer==True:
                    struct_name = ast_struct.ext[0].type.type.type.name
                    defName = ast_struct.ext[0].type.type.declname
                    if struct_name is None and defName is not None:
                       struct_name=defName
                    variable_map=getVariablesC(ast_struct.ext[0].type.type.type.decls)
                    structobject = structclass(struct_name, isTypedef, variable_map , defName, isPointer)
                    struct_map[struct_name]=structobject
                 else:
                    struct_name = ast_struct.ext[0].type.declname
                    defName = ast_struct.ext[0].type.type.name
                    variable_map=getVariablesC(ast_struct.ext[0].type.type.decls)
                    structobject = structclass(struct_name, isTypedef, variable_map , defName, isPointer)
                    struct_map[struct_name]=structobject
                
    except Exception as e:
            #print 'Error(Find Error in Input File)'
            print('Unknown')
            writeLogFile( "j2llogs.logs" ,str(e))
            return
        #ast.show()
    generator = c_generator.CGenerator()
    writeLogFile( "j2llogs.logs" , getTimeStamp()+"\nCommand--Translate \n"+"\nParameters--\n File Name--"+file_name+"\n")
    if ast is None:
       print("Error present in code. Please verify you input file")
       return
    if len(ast.ext)==0:
       print("Error present in code. Please verify you input file")
       return
    externalvarmap={}
    externalarraymap={}
    functionvarmap={}
    memberfunctionmap={}
    axiomeMap={}
    addition_array_map={}
    function_vfact_map={}
    witnessXml_map={}
	
    counter=0 
        
    try:
       for e in ast.ext:
          if type(e) is c_ast.Decl:
             if type(e.type) is c_ast.FuncDecl:
                parametermap={}
                structType=None
                new_e,pointer_list,array_list=pointerHandlingParameter(e)
                if new_e is None:
                   function_decl=e
                else:
                   function_decl=new_e
                if function_decl.type.args is not None:
                   for param_decl in function_decl.type.args.params:
                       if param_decl.name is not None:
                          structType=None
                          if type(param_decl.type) is c_ast.ArrayDecl:
                             degree=0
                             dimensionmap={}
                             data_type,degree,structType=getArrayDetails(param_decl,degree,dimensionmap)
                             variable=variableclass(param_decl.name, data_type,None,dimensionmap,None,structType)
                          else:
                             try:

                                variable=variableclass(param_decl.name, param_decl.type.type.names[0],None,None,None,structType)

                             except Exception as e:
                                #print 'Error(Translation to Intermate Intermediate)'
                                print('Unknown')
                                writeLogFile( "j2llogs.logs" ,str(e))
                                #print str(e)
                                return
                          parametermap[param_decl.name]=variable  

                membermethod=membermethodclass(function_decl.name,function_decl.type.type.type.names[0],parametermap,None,None,0,0,None,None,None)
                functionvarmap[membermethod.getMethodname()]=membermethod

          elif type(e.type) is c_ast.TypeDecl:
                                    
                var_type=None
                initial_value=None
                structType=None
                e=change_var_name_decl(e)
                for child in e.children():
                    if type(child[1].type) is c_ast.IdentifierType:
                       var_type=child[1].type.names[0]
                    else:
                    				
                       initial_value=child[1].value
                       #variable=variableclass(e.name, var_type,None,None,initial_value,structType)
                       variable=variableclass(e.name, var_type,None,None,initial_value,structType)
                       program_analysis_var_decl=program_analysis_var_decl+str(generator.visit(e))+';\n'
                       externalvarmap[e.name]=variable
                       external_var_map[e.name]=e.name

          elif type(e.type) is c_ast.ArrayDecl:
               program_analysis_var_decl=program_analysis_var_decl+str(generator.visit(e))+';\n'
                                
               if type(e.type.type) is c_ast.PtrDecl:
                  array_name=getArrayNameDecl(e.type.type.type)
                  externalarraymap[array_name]=change_var_name_decl(e)
                  external_var_map[array_name]=e.name
                  external_pointer_map[array_name]=array_name
               else:
                  array_name=getArrayNameDecl(e.type)
                  externalarraymap[array_name]=change_var_name_decl(e)
                  external_var_map[array_name]=e.name
          else:
               if type(e) is c_ast.FuncDef:                          
                  parametermap={}
                  new_e,pointer_list,array_list=pointerHandlingParameter(e)
                  if new_e is None:
                     function_decl=e
                  else:
                     function_decl=new_e
    				
                  function_decl=e.decl
                                
                  function_body = e.body
                                
                  if function_body.block_items is not None:
                     #function_body=pointerHandlingDecl(function_body,pointer_list,array_list)
                     statements=function_body.block_items
                     statements=change_var_name(statements)
                     function_body= c_ast.Compound(block_items=statements)
                     localvarmap=getVariables(function_body)
                     counter=counter+1
                     if function_decl.type.args is not None:
                        for param_decl in function_decl.type.args.params:
                            new_param_decl=declarationModifying(param_decl)
                            if new_param_decl is not None:
                               param_decl=new_param_decl
                            param_decl=change_var_name_decl(param_decl)
                            if param_decl.name is not None:
                               structType=None
                               if type(param_decl.type) is c_ast.ArrayDecl:
                                  #print param_decl.show()
                                  degree=0
                                  dimensionmap={}
                                  data_type,degree,structType=getArrayDetails(param_decl,degree,dimensionmap)                                                             
                                  variable=variableclass(param_decl.name, data_type,None,dimensionmap,None,structType)
                               elif type(param_decl.type) is c_ast.PtrDecl:
                                    stmt=pointerToArray(param_decl)
                                    #print stmt.show()
                                    if stmt is not None and type(stmt.type) is c_ast.ArrayDecl:
                                       degree=0
                                       dimensionmap={}
                                    data_type,degree,structType=getArrayDetails(param_decl,degree,dimensionmap)
                                    variable=variableclass(stmt.name, data_type,None,dimensionmap,None,structType)
                                else:				
                                    try:
                                        variable=variableclass(param_decl.name, param_decl.type.type.names[0],None,None,None,structType)
                                    except Exception as e:
                                        print('Error(Translation to Intermate Intermediate)'
                                        writeLogFile( "j2llogs.logs" ,str(e))
                                        #print str(e)
                                        return
                                                                parametermap[param_decl.name]=variable
                                    if function_decl.name in functionvarmap.keys():
                                            if function_decl.name!='__VERIFIER_assert':
                                                membermethod=membermethodclass(function_decl.name,function_decl.type.type.type.names[0],parametermap,localvarmap,function_body,0,counter,None,None,function_decl)
                                                functionvarmap[function_decl.name]=membermethod
                                    else:
                                            if function_decl.type.args is not None:
                                                    for param_decl in function_decl.type.args.params:
                                                            new_param_decl=declarationModifying(param_decl)
                                                            if new_param_decl is not None:
                                                                param_decl=new_param_decl
                                                                param_decl=change_var_name_decl(param_decl)
                                                            if param_decl.name is not None:
                                                                    structType=None
                                                                    if type(param_decl.type) is c_ast.ArrayDecl:
                                                                            degree=0
                                                                            dimensionmap={}
                                                                            data_type,degree,structType=getArrayDetails(param_decl,degree,dimensionmap)
                                                                            variable=variableclass(param_decl.name, data_type,None,dimensionmap,None,structType)
                                                                    elif type(param_decl.type) is c_ast.PtrDecl:
                                                                            stmt=pointerToArray(param_decl)
                                                                            if stmt is not None and type(stmt.type) is c_ast.ArrayDecl:
                                                                                    degree=0
                                                                                    dimensionmap={}
                                                                                    data_type,degree,structType=getArrayDetails(param_decl,degree,dimensionmap={})
                                                                                    variable=variableclass(stmt.name, data_type,None,dimensionmap,None,structType)
								
                                                                    else:	
                                                                            try:
                                                                                variable=variableclass(param_decl.name, param_decl.type.type.names[0],None,None,None,structType)
                                                                            except Exception as e:
                                                                                print 'Error(Translation to Intermate Intermediate)'
                                                                                writeLogFile( "j2llogs.logs" ,str(e))
                                                                                #print str(e)
                                                                                return
                                                                    parametermap[param_decl.name]=variable
                                            if function_decl.name!='__VERIFIER_assert' and function_decl.name!='exit':
                                                membermethod=membermethodclass(function_decl.name,function_decl.type.type.type.names[0],parametermap,localvarmap,function_body,0,counter,None,copy.deepcopy(function_body),function_decl)
                                                functionvarmap[membermethod.getMethodname()]=membermethod
        except Exception as e:
            print 'Unknown'
            writeLogFile( "j2llogs.logs" ,str(e))
            #print str(e)
            return
        
    	for medthod in functionvarmap.keys():
                membermethod=functionvarmap[medthod]
    		body=membermethod.getBody()
    		if body is not None:
                    if body.block_items is not None: 
                        
                        try:

                            statements,pa_statements=programTransformation(body,functionvarmap,medthod)
                            
                            
                        
                            statements = updatePointerStruct(statements,struct_map)
                            
                        
                        
                            pa_statements = updatePointerStruct(pa_statements,struct_map)
                            
                            
                            statements = organizeMallocFunctionBlock(statements)
                            
                            
                            #pa_statements = organizeInnerDeclartionMain(pa_statements)
                            
                        
                        except Exception as e:
                            #print 'Error(Translation to Intermate Intermediate)'
                            print 'Unknown'
                            writeLogFile( "j2llogs.logs" ,str(e))
                            print str(e)
                            return
                        
                        for temp_method in externalarraymap.keys():
                            if isVarPresnt(statements,temp_method)==True:
                                new_statements=[]
                                new_statements.append(externalarraymap[temp_method])
                                statements=construct_program(new_statements+statements)
                        body_comp = c_ast.Compound(block_items=statements)
                        localvarmap=getVariables(body_comp)
                        statements,localvarmap=addAllExtVariables(statements,externalvarmap,localvarmap)
                        statements = translateStruct(statements,localvarmap,struct_map)
                        
                        
                        
                        duplicate_dec_map={}
                        generator = c_generator.CGenerator()
                        update_pa_statements=[]
                        for s in pa_statements:
                            if type(s) is c_ast.Decl:
                                key = generator.visit(s)
                                if key not in duplicate_dec_map:
                                    duplicate_dec_map[key]=key
                                    update_pa_statements.append(s)
                                else:
                                    if s.init is not None:
                                        update_pa_statements.append(c_ast.Assignment(op='=',lvalue=c_ast.ID(name=s.name),rvalue=s.init))
                            else:
                                update_pa_statements.append(s)

                        pa_statements=update_pa_statements
                        
                        line_count_ast_Block(pa_statements)
                        #statements=pointerHandling(statements,pointer_list,array_list)
                        
                        #print pa_statements
                        
                        pa_statements = updateDeclartionFromWhile(pa_statements)
                        
                        #print pa_statements
                        
                        if medthod=='main':
                            
                            pa_statements = updateAddInitArray(pa_statements)
                            
                            #print pa_statements
                        
                        #print '$$$$$$$$$$$$$$$$$$$$$$$$$$$'
                        #generator = c_generator.CGenerator()
                        #print(generator.visit(c_ast.Compound(block_items=pa_statements)))
                        #print '$$$$$$$$$$$$$$$$$$$$$$$$$$$'

                        
                        body_comp = c_ast.Compound(block_items=statements)
                        membermethod.setBody(body_comp)
                        membermethod.setLocalvar(localvarmap)
                        membermethod.setAnalysis_module(c_ast.Compound(block_items=pa_statements))
                    else:
                        membermethod.setBody(None)
                        membermethod.setLocalvar(None)
    		else:
		    membermethod.setBody(None)
    		    membermethod.setLocalvar(None)
    
    	temp_functionvarmap={}
        
        
    	
    	for medthod in functionvarmap.keys():
                membermethod=functionvarmap[medthod]
                in_var_map=membermethod.getInputvar()
                if len(in_var_map)>0:
                    for x in in_var_map:
                        variable=in_var_map[x]
                        if variable.getDimensions() is not None and len(variable.getDimensions())>0:
                            temp_functionvarmap[medthod]=functionvarmap[medthod]
                elif medthod=='main':
                        temp_functionvarmap[medthod]=functionvarmap[medthod]
                
    	
    	for medthod in functionvarmap.keys():
                membermethod=functionvarmap[medthod]
    		body=membermethod.getBody()
    		if body is not None:
                    if medthod=='main':
                        
                        statements=body.block_items
                        
                        statements = substituteFunBlock(statements,temp_functionvarmap,medthod,externalvarmap)
            
                        duplicate_dec_map={}
                        
                        generator = c_generator.CGenerator()
                        
                        update_statements=[]

                        for s in statements:
                            if type(s) is c_ast.Decl:
                                key = generator.visit(s)
                                if key not in duplicate_dec_map:
                                    duplicate_dec_map[key]=key
                                    update_statements.append(s)
                            else:
                                update_statements.append(s)
                                                            
                        body_comp = c_ast.Compound(block_items=update_statements)
                        
                        membermethod.setBody(body_comp)
    
                        #print '!!!!!!!!!!!!!!!!!!!!!'
                        #body_comp = c_ast.Compound(block_items=update_statements)
                        #generator = c_generator.CGenerator()
                        #print(generator.visit(body_comp))
                        #print '!!!!!!!!!!!!!!!!!!!!!'
                        #if len(temp_functionvarmap)>0:
                        #    ret_body_comp,temp_status1,temp_status2 = reduceArraySize1("int main()"+generator.visit(body_comp))
                        #
                        #    if ret_body_comp is not None and temp_status1==True and temp_status2:
                        #        body_comp = ret_body_comp.body
                        #        membermethod.setBody(body_comp)
                        

    
    	
    	
    
    	#program in intermediate form
    	programeIF=[]

    	programeIF.append('-1')
    			
    	programeIF.append('prog')

    	programe_array=[]

    	variables_list_map={}
        
    	for medthod in functionvarmap.keys():
                f_vfact=[]
                f_vfact_para=[]
    		membermethod=functionvarmap[medthod]
                if membermethod.getreturnType() is not 'void':
                    f_vfact.append(medthod)
                    f_vfact_para.append(membermethod.getreturnType())
                    for iv in membermethod.getInputvar():
                        i_var=membermethod.getInputvar()[iv]
                        f_vfact_para.append(i_var.getVariableType())
                    f_vfact.append(len(f_vfact_para)-1)
                    f_vfact.append(f_vfact_para)
                    function_vfacts.append(f_vfact)

                
    		body=membermethod.getBody()
                
    		if body is not None:
    			new_variable={}
    			update_statements=[]
    			   		
	    		body_comp=body
	    		
	    		membermethod.setTempoary(body_comp)
	    		
	    		statements=body.block_items
	    		
	    		new_variable.clear()

	    		update_statements=[]
			
			for var in new_variable.keys():
				if isBoolVariable( var )==True:
			    	    	#temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['_Bool'])), init=c_ast.Constant(type='_Bool', value=None), bitsize=None)
                                        temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
			    		update_statements.append(temp)
			    	else:
			    		if type(new_variable[var]) is tuple:
                                            type_stmt,t_degree=new_variable[var]
                                            program_temp=type_stmt+' '+var
                                            for x in range(0,t_degree):
                                                program_temp+='[]'
                                            program_temp+=';'
                                            temp_ast = parser.parse(program_temp)
                                            update_statements.append(temp_ast.ext[0])
                                        else:
                                            if var in new_variable_array.keys():
                                                type_stmt='int'
                                                t_degree=new_variable_array[var]
                                                program_temp=type_stmt+' '+var
                                                for x in range(0,t_degree):
                                                    program_temp+='[]'
                                                program_temp+=';'
                                                temp_ast = parser.parse(program_temp)
                                                update_statements.append(temp_ast.ext[0])
                                            else:
                                                temp=c_ast.Decl(name=var, quals=[], storage=[], funcspec=[], type=c_ast.TypeDecl(declname=var, quals=[], type=c_ast.IdentifierType(names=['int'])), init=c_ast.Constant(type='int', value='0'), bitsize=None)
                                                update_statements.append(temp)
			        	
			for statement in statements:
    				update_statements.append(statement)
                        
                        body_comp=c_ast.Compound(block_items=update_statements)
	    		
    			membermethod.setBody(body_comp)
   
    			
    			localvarmap=getVariables(body_comp)
    			
    			for var in externalvarmap.keys():
				variable=externalvarmap[var]
				localvarmap[var]=variable
    			
    			membermethod.setLocalvar(localvarmap)
    			membermethod=functionvarmap[medthod]
    			    			
    			function=[]
    			
    			function.append('-1')
    			
    			function.append('fun')    			
    			
    			functionName=[]
    			
    			allvariable={}
    			
    			for x in membermethod.getInputvar():
				allvariable[x]=membermethod.getInputvar()[x]
			for x in membermethod.getLocalvar():
        			allvariable[x]=membermethod.getLocalvar()[x]
    			if validationOfInput(allvariable)==True:
				print 'Unknown'
				#print "Please Rename variable Name {S,Q,N,in,is} to other Name"
          			return
    			

    			try:
                            
                             
                            
                            program,variablesarray,fname,iputmap,opvariablesarray,module_analysis,module_analysis2=translate2IntForm(membermethod.getMethodname(),membermethod.getreturnType(),membermethod.getBody(),membermethod.getInputvar(),membermethod.getTempoary(),membermethod.getAnalysis_module(),struct_map)

                            
                        except Exception as e:
                            #print 'Error(error occurred during translation intermediate format)'
                            print 'Unknown'
                            writeLogFile( "j2llogs.logs" ,str(e))
                        #    print str(e)
                            return
		

			functionName.append(fname)

                        
                        if len(iputmap.keys())>0:
                            for x_i in range(0,len(iputmap.keys())):
                                    functionName.append(iputmap.keys()[len(iputmap.keys())-1-x_i])
                                    #functionName.append(iputmap.keys()[x_i])


			function.append(functionName)
                                                
			
			function.append(program)
                        

			programe_array.append(function)
		
			variables_list_map[fname]=variablesarray
			
			addition_array=[]
			
			addition_array.append(iputmap)
			
			addition_array.append(allvariable)
			
			addition_array.append(opvariablesarray)
			
			addition_array_map[fname]=addition_array
			
			memberfunctionmap[fname]=membermethod
                        
                        
			
			function_vfact_list=[]
			function_vfact=[]
			function_vfact.append(fname)
			function_vfact.append(len(iputmap))
			parameters_type=[]
			parameters_type.append(membermethod.getreturnType())
			for x in defineDetaillist:
				function_vfact_list.append(x)
					
			
			defineDetaillist=[]
			for element in iputmap.keys():
				variable=iputmap[element]
				if variable is not None:
					parameters_type.append(variable.getVariableType())
			function_vfact.append(parameters_type)
			function_vfact_list.append(function_vfact)
			function_vfact_map[fname]=function_vfact_list	
                        
                        resultfunction='__VERIFIER_nondet_int'
                        
                        filename=file_name
                        functionname=functionName
                        
                        witnessXml=getWitness(filename,fname,resultfunction)
                        witnessXml_map[fname]= witnessXml
                        if program_analysis is not None:
                            #print '###########################3'
                            #print membermethod.getFun_decl().show()
                            #print '###########################3'
                            program_decl=programPrint(membermethod.getFun_decl())
                            #print '^^^^^^^^^^^^^^^^^^^'
                            #print membermethod.getMethodname()
                            #print membermethod.getreturnType()
                            #print program_decl
                            #print '^^^^^^^^^^^^^^^^^^^'
                            #print module_analysis2
                            #print '^^^^^^^^^^^^^^^^^^^'
                            if 'main' not in program_decl:
                                program_analysis_decl+=programPrint(membermethod.getFun_decl())+';\n'
                            module_analysis_t1,module_analysis_t2=module_analysis2
                            program_analysis2=program_decl+programPrint(module_analysis_t1)+program_analysis2
                            program_analysis3=program_decl+programPrint(module_analysis_t2)+program_analysis3
                            program_analysis=program_decl+programPrint(module_analysis)+program_analysis
                            
                            #print '%%%%%%%%%%%%%%%%%%!'
                            #print program_analysis
                            #print programPrint(module_analysis_t1)
                            #print '%%%%%%%%%%%%%%%%%%@'
                            #print program_analysis2
                            #print '%%%%%%%%%%%%%%%%%%@'
                            #print program_analysis3
                            #print '%%%%%%%%%%%%%%%%%%#'
                            
        
        
        #program_analysis=program_analysis_var_decl+program_analysis
        #program_analysis2=program_analysis_var_decl+program_analysis2
        #program_analysis3=program_analysis_var_decl+program_analysis3
        program_analysis_decl=program_analysis_var_decl+program_analysis_decl
        
        programeIF.append(programe_array)
        #print '$$$$$$$$$$$$$$$$$$$'
        #print program_analysis
        #print program_analysis_var_decl
        #print program_analysis_decl
        #print '$$$$$$$$$$$$$$$$$$$'
        #print '--------------------------------'
        #print programeIF
        #print '--------------------------------'
        #print variables_list_map
        #print '--------------------------------'
        #return
        
        try:
            f_map,o_map,a_map,cm_map,assert_map,assume_map,assert_key_map=translate1(programeIF,variables_list_map,1)
            
        except Exception as e:
            print 'Error(Translation Failed)'
            writeLogFile( "j2llogs.logs" ,str(e))
            #print str(e)
            return

        #Comment me to use Z3
        #return
        f_list=f_map.keys()
        cycle_list=[]
        programgraph_map=construct_graph(f_map,o_map,a_map,f_list)
        programgraph = graphclass.Graph(programgraph_map)
        

        
        if programgraph.cyclic():
            cycle_list=list(itertools.chain.from_iterable(programgraph.getAllNodesInCycle()))
            

        f_list=removeCycles(f_list,cycle_list)
        

        
        for f_x in cycle_list:
            for x in o_map[f_x]:
                if o_map[f_x][x][0]=='e':
                    o_map[f_x][x][2] = reconstructRecurences(o_map[f_x][x][2],cycle_list)

                    
        for f_x in cycle_list:
            if f_x in fun_call_map.keys() and fun_call_map[f_x]==1:
                for x in o_map['main']:
                    if o_map['main'][x][0]=='e':
                        o_map['main'][x][2] = reconstructRecurences(o_map['main'][x][2],cycle_list)
        


        function_substitution_test('main',programgraph_map,f_map,o_map,a_map,assert_map,assume_map,cycle_list)
        
        
           
        #print '$$$$$$$$$$$$$$$$$$$$'
        
        #print cycle_list
        
        #print '$$$$$$$$$$$$$$$$$$$$'
        
        
        
        
        #for x in f_map.keys():
        #    f=f_map[x]
        #    o=o_map[x]
        #    a=a_map[x]
        #    f,o,a=updateAxoimsRecurrences(f,o,a,cycle_list)
        #    f_map[x]=f
        #    o_map[x]=o
        #    a_map[x]=a
        
        if type(f_map) is dict and type(o_map) is dict and type(a_map) is dict and type(cm_map) is dict and type(assert_key_map) is dict:
                for key in f_map.keys():
                        membermethod=functionvarmap[key]                        
                        #print membermethod.getreturnType()
        		f=f_map[key]
        		o=o_map[key]
        		a=a_map[key]
        		cm=cm_map[key]
                        
        		assert_list=assert_map[key]
        		assume_list=assume_map[key]
                        
                        assert_list=function_substitution_main_Assert(assert_list,f_map,o_map,a_map,cycle_list)
                        
                        
        		addition_array=addition_array_map[key]
        		
        		vfacts,constraints=getVariFunDetails(f,o,a,addition_array[1],addition_array[2])
                        
                        #for x in vfacts:
                        #    print x

        		
        		vfacts2=getVariFunDetails2(f,o,a,addition_array[1],constraints,assert_list,assume_list)
                    
                        for x in a:
                            equ=getConstraints_Eq(x,addition_array[1],constraints)
                            if equ is not None:
                                constraints.append(equ)
        		vfacts=[]
        		for vfact in vfacts2:
        			vfacts.append(vfacts2[vfact])
                        
                        for x in function_vfacts:
                             vfacts.append(x)
                    
                        #print '--------------'
                        #for x in vfacts2:
                        #    print vfacts2[x]
                            
        		#for element in function_vfact_map.keys():
        		#	function_vfact_list=function_vfact_map[element]
        		#	for x in function_vfact_list:
                        #                if x[0] not in vfacts2.keys():
                        #                    vfacts.append(x)
                        f,o,a,cm,assert_list = rec_solver_tactic8(f,o,a,assert_list)
        		f,o,a,vfacts=organizeAxioms(f,o,a,vfacts)
                                                
                        
                        #output_axioms_fn(f,o,a)
        		axiom=axiomclass(f,o,a,membermethod.getInputvar(), vfacts, constraints,cm,assert_list,assume_list,addition_array[1])
        		axiomeMap[key]=axiom

                #print '#######'
                #print external_var_map
                #print program_analysis
                #print '#######'
                end_time=current_milli_time()
                #print "Translation Time--"
		#print end_time-start_time
                #AssetionAnalysis2(program_analysis2,program_analysis_decl)
                #
                #return
                #print '!!!!!!!!!!!!!'
                #print program_analysis
                #print program_analysis_decl
                #print '!!!!!!!!!!!!!'
                if programgraph.cyclic():
                    
                    axiommain=axiomeMap['main']
                    
                    program_analysis_list,concret_value_map_list = getRangeValues(axiommain.getOutput_equations(),program_analysis)
                    
                    #print '%%%%%%%%%%%%%%'
                    #print concret_value_map_list
                    #print '%%%%%%%%%%%%%%'
                    #print program_analysis
                    #print '%%%%%%%%%%%%%%'
                                        
                    isRunAgain=False
                    conrt_count=0
                    for program_analysis in program_analysis_list:
                        
                        if isRunAgain==False:
                            
                            results=AssetionAnalysis8(program_analysis,program_analysis_decl)
                            
                            #print '-----------'
                            #print program_analysis
                            #print main_count_ast_line_no

                            #print '-----------------'
                            #print main_line_no_stmt_ast_map
                            #if len(concret_value_map_list)>0:
                            #    print concret_value_map_list[conrt_count]
                            #print '-----------'
                            
                            if results is None and type(results) is not str:
                                
                                isRunAgain=True
                            else:
                                if len(concret_value_map_list)>0:
                                    program_analysis3 = AssetionAnalysis3_8(program_analysis3,concret_value_map_list[conrt_count])
                                
                            conrt_count=conrt_count+1
                        
                        
                    #print '%%%%%%%%%-------------'
                    #print results
                    #print '%%%%%%%%%-------------'
                    if type(results) is str and  'Termination Failed' in results:
                        print 'Termination Failed'
                        flag_terminate=True
                        #return
                    
                else:
                    
                    results=AssetionAnalysis(program_analysis,program_analysis_decl)
                    
                    #results={}
                    #print '%%%%%%%%%-------------'
                    #print program_analysis
                    #print '#####################'
                    #return
                    #parser = GnuCParser()
                    #generator = c_generator.CGenerator()
                    #ast = parser.parse(program_analysis)
                    #for e in ast.ext:
                    #    if type(e) is c_ast.FuncDef and e.decl.name=='main':
                    #        function_body = e.body
                    #        if function_body.block_items is not None:
                    #            statements=function_body.block_items
                    #            function_body= c_ast.Compound(block_items=updateAddInitArray(statements)) 
                    #            print(generator.visit(function_body))
                    if type(results) is str and  'Termination Failed' in results:
                        print 'Termination Failed'
                        return
                    elif type(results) is str and 'Segmentation fault (core dumped)' in results:
                        update_program,is_runable=reduceArraySize(program_analysis)
                        if is_runable==True:
                            results=AssetionAnalysis7(update_program,program_analysis_decl)
                        else:
                            update_program,is_runable=reduceArraySizeNonDet(program_analysis)
                            if is_runable==True:
                                results=AssetionAnalysis7(update_program,program_analysis_decl)
                    else:
                        if (type(results) is not dict and len(results)==0) or (type(results) is dict and len(results)==0):
                            new_program_analysis = AssetionAnalysis9(program_analysis)
                            if new_program_analysis is not None:
                                results=AssetionAnalysis(new_program_analysis,program_analysis_decl)
                                if results is not None and type(results) is not str and len(results) :
                                    program_analysis=new_program_analysis
                                
                                
                                

                #print '$$$$$$$$$$$$$$$$$'
                #print results
                #print '$$$$$$$$$$$$$$$$$'
                #results={}
                #include <stdlib.h>
                
                if results is None:
                    #print 'Result--'
                    #print 'Program Terminates Failed'
                    #return
                    results={}
                for fun in assert_key_map.keys():
                    assert_key_list = assert_key_map[fun]
                    assert_list=axiomeMap[fun].getAsserts()
                    new_assert_key_list=[]
                    for result in results:
                        new_assert_list=[]
                        for key in assert_key_list:
                            if key in result:
                                assertion=assert_key_list[key]
                                if '_FAILED' not in key:
                                    #print 'Assertion :'+wff2z3_update_postCond(assertion)
                                    #print 'False'
                                    #violation_status=violationWitness(filename)
                                    #if violation_status is not None and 'False' in violation_status:
                                    print 'VIAP_STANDARD_OUTPUT_False'
                                    
                                    #print '!!!!!!!!!!!!!@@@@@@@@ram'
                                    #print program_analysis3
                                    #print program_analysis_decl
                                    #print '!!!!!!!!!!!!!@@@@@@@@ram'
                                    
                                    program_analysis3_new = reduceLoopSize(program_analysis3)
                                    
                                    if program_analysis3_new is not None:
                                        
                                        #print assert_key_list
                                        
                                        #print '-------------------@@@@@@@@@@@@@@@@'
                                        
                                        program_analysis3 = program_analysis3_new

                                    
                                    result=AssetionAnalysis3(program_analysis3,program_analysis_decl,file_name,property)
                                    
                           
                                    
                                    if result is not None:
                                            writtingFile( "errorWitness.graphml" , result )
                                            writeLogFile( "j2llogs.logs" , "\nViolation \n"+str(result)+"\n" )
                                    else:
                                            
                                            line_no,stmt2 = getLineNumber_terminate('__VERIFIER_error()','__VERIFIER_assert')
                                            if property is None:
                                                    property="CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )"
                                            else:
                                                    if '=' in property:
                                                        value_names=property.split('=')
                                                        fd = open(value_names[1])
                                                        property = "".join(fd.readlines())
                                                    else:
                                                        property="CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )"
            
                                            hashcode=sha1(file_name)
                                            
                                            violation_witness2=''
                                            violation_witness2+="<node id=\"N0\"><data key=\"entry\">true</data></node>\n"
                                            violation_witness2+="<node id=\"N"+str(1)+"\">"+"\n<data key=\"violation\">true</data>\n<data key=\"violatedProperty\">__VERIFIER_error(); called in line "+str(line_no)+"</data>\n"+"</node>\n"
                                            violation_witness2+="<edge source=\"N"+str(0)+"\" target=\"N"+str(1)+"\">\n"
                                            violation_witness2+="<data key=\"sourcecode\">__VERIFIER_error();</data>\n"
                                            violation_witness2+="<data key=\"startline\">"+str(line_no)+"</data>\n"
                                            violation_witness2+="<data key=\"endline\">"+str(line_no)+"</data>\n"
                                            violation_witness2+="</edge>\n"
                                            
                                            violation_witness1="<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n"+"<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">\n"+"<key attr.name=\"originFileName\" attr.type=\"string\" for=\"edge\" id=\"originfile\">\n"+"<default>"+filename+"</default>\n"+"</key>\n"+"<key attr.name=\"invariant\" attr.type=\"string\" for=\"node\" id=\"invariant\"/>\n"+"<key attr.name=\"invariant.scope\" attr.type=\"string\" for=\"node\" id=\"invariant.scope\"/>\n"+"<key attr.name=\"namedValue\" attr.type=\"string\" for=\"node\" id=\"named\"/>\n"+"<key attr.name=\"nodeType\" attr.type=\"string\" for=\"node\" id=\"nodetype\">\n"+"<default>path</default>\n"+"</key>"+"<key attr.name=\"isFrontierNode\" attr.type=\"boolean\" for=\"node\" id=\"frontier\">"+"<default>false</default>"+"</key>\n"+"<key attr.name=\"isViolationNode\" attr.type=\"boolean\" for=\"node\" id=\"violation\">\n"+"<default>false</default>\n"+"</key>\n"+"<key attr.name=\"isEntryNode\" attr.type=\"boolean\" for=\"node\" id=\"entry\">\n"+"<default>false</default>\n"+"</key>\n"+"<key attr.name=\"isSinkNode\" attr.type=\"boolean\" for=\"node\" id=\"sink\">\n"+"<default>false</default>"+"</key>"+"<key attr.name=\"isLoopHead\" attr.type=\"boolean\" for=\"node\" id=\"loopHead\">\n"+"<default>false</default>"+"</key>"+"<key attr.name=\"violatedProperty\" attr.type=\"string\" for=\"node\" id=\"violatedProperty\"/>\n"+"<key attr.name=\"threadId\" attr.type=\"string\" for=\"edge\" id=\"threadId\"/>\n"+"<key attr.name=\"sourcecodeLanguage\" attr.type=\"string\" for=\"graph\" id=\"sourcecodelang\"/>\n"+"<key attr.name=\"programFile\" attr.type=\"string\" for=\"graph\" id=\"programfile\"/>\n"+"<key attr.name=\"programHash\" attr.type=\"string\" for=\"graph\" id=\"programhash\"/>\n"+"<key attr.name=\"specification\" attr.type=\"string\" for=\"graph\" id=\"specification\"/>\n"+"<key attr.name=\"memoryModel\" attr.type=\"string\" for=\"graph\" id=\"memorymodel\"/>\n"+"<key attr.name=\"architecture\" attr.type=\"string\" for=\"graph\" id=\"architecture\"/>\n"+"<key attr.name=\"producer\" attr.type=\"string\" for=\"graph\" id=\"producer\"/>\n"+"<key attr.name=\"sourcecode\" attr.type=\"string\" for=\"edge\" id=\"sourcecode\"/>\n"+"<key attr.name=\"startline\" attr.type=\"int\" for=\"edge\" id=\"startline\"/>\n"+"<key attr.name=\"endline\" attr.type=\"int\" for=\"edge\" id=\"endline\"/>\n"+"<key attr.name=\"lineColSet\" attr.type=\"string\" for=\"edge\" id=\"lineCols\"/>\n"+"<key attr.name=\"control\" attr.type=\"string\" for=\"edge\" id=\"control\"/>\n"+"<key attr.name=\"assumption\" attr.type=\"string\" for=\"edge\" id=\"assumption\"/>\n"+"<key attr.name=\"assumption.scope\" attr.type=\"string\" for=\"edge\" id=\"assumption.scope\"/>\n"+"<key attr.name=\"enterFunction\" attr.type=\"string\" for=\"edge\" id=\"enterFunction\"/>\n"+"<key attr.name=\"returnFromFunction\" attr.type=\"string\" for=\"edge\" id=\"returnFrom\"/>"+"<key attr.name=\"predecessor\" attr.type=\"string\" for=\"edge\" id=\"predecessor\"/>\n"+"<key attr.name=\"successor\" attr.type=\"string\" for=\"edge\" id=\"successor\"/>\n"+"<key attr.name=\"witness-type\" attr.type=\"string\" for=\"graph\" id=\"witness-type\"/>\n"+"<graph edgedefault=\"directed\">\n"+"<data key=\"witness-type\">violation_witness</data>\n"+"<data key=\"sourcecodelang\">C</data>"+"<data key=\"producer\">VIAP</data>"+"<data key=\"specification\">"+property+"</data>"+"<data key=\"programfile\">"+filename+"</data>\n"+"<data key=\"programhash\">"+hashcode+"</data>\n"+"<data key=\"memorymodel\">precise</data>\n"+"<data key=\"architecture\">32bit</data>\n"+"\n<node id=\"sink\"><data key=\"sink\">true</data></node>\n"
                                            writtingFile( "errorWitness.graphml" , str(violation_witness1+violation_witness2+"\n</graph>\n</graphml>\n"))
                                            writeLogFile( "j2llogs.logs" , "\nViolation \n"+str(violation_witness1+violation_witness2+"\n</graph>\n</graphml>\n")+"\n" )
                                    
                                    test_int_mid=None
                                    test_uint_mid=None
                                    test_char_mid=None
                                    int_mid_count=0
                                    uint_mid_count=0
                                    char_mid_count=0
                                    #print results[result]
                                    return
                                            
                                    if assertion in assert_list:
                                        assert_list.remove(assertion)
                                else:
                                    for x in assert_list:
                                        if x[0]=='c1':
                                            if key in x[1][1][0]:
                                                #print 'Assertion :'+wff2z3_update_postCond(x)
                                                assert_list.remove(x)
                                    #print 'False'
                                    #violation_status=violationWitness(filename)
                                    #if violation_status is not None and 'False' in violation_status:
                                    print 'VIAP_STANDARD_OUTPUT_False'
                                    test_int_mid=None
                                    test_uint_mid=None
                                    test_char_mid=None
                                    int_mid_count=0
                                    uint_mid_count=0
                                    char_mid_count=0
                                    
                                    #print '!!!!!!!!!!!!!@@@@@@@@ram'
                                    #print result
                                    #print program_analysis3
                                    #AssetionAnalysis10(program_analysis3)
                                    #print program_analysis_decl
                                    
                                    #stmt,line_no = AssetionAnalysis11(program_analysis3)
                                    
                                    #print stmt
                                    
                                    #result,new_result = AssetionAnalysis10(program_analysis3,program_analysis_decl,file_name,property)
                                    
                                    #print new_result
                                    
                                    #print '!!!!!!!!!!!!!@@@@@@@@ram'
                                    
                                    result=AssetionAnalysis3(program_analysis3,program_analysis_decl,file_name,property)
                                    
                                    if result is not None:
                                            #print "Error Witness Generated"
                                            writtingFile( "errorWitness.graphml" , result )
                                            writeLogFile( "j2llogs.logs" , "\nViolation \n"+str(result)+"\n" )
                                    else:
                                            
                                            line_no,stmt2 = getLineNumber_terminate('__VERIFIER_error();','main')
                                            
                                            if property is None:
                                                    property="CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )"
                                            else:
                                                    if '=' in property:
                                                        value_names=property.split('=')
                                                        fd = open(value_names[1])
                                                        property = "".join(fd.readlines())
                                                    else:
                                                        property="CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )"
            
                                            
                                            violation_witness2=''
                                            violation_witness2+="<node id=\"N0\"><data key=\"entry\">true</data></node>\n"
                                            violation_witness2+="<node id=\"N"+str(1)+"\">"+"\n<data key=\"violation\">true</data>\n<data key=\"violatedProperty\">__VERIFIER_error(); called in line "+str(line_no)+"</data>\n"+"</node>\n"
                                            violation_witness2+="<edge source=\"N"+str(0)+"\" target=\"N"+str(1)+"\">\n"
                                            violation_witness2+="<data key=\"sourcecode\">__VERIFIER_error();</data>\n"
                                            violation_witness2+="<data key=\"startline\">"+str(line_no)+"</data>\n"
                                            violation_witness2+="<data key=\"endline\">"+str(line_no)+"</data>\n"
                                            violation_witness2+="</edge>\n"
                                            
                                            hashcode=sha1(file_name)
                                            violation_witness1="<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n"+"<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">\n"+"<key attr.name=\"originFileName\" attr.type=\"string\" for=\"edge\" id=\"originfile\">\n"+"<default>"+filename+"</default>\n"+"</key>\n"+"<key attr.name=\"invariant\" attr.type=\"string\" for=\"node\" id=\"invariant\"/>\n"+"<key attr.name=\"invariant.scope\" attr.type=\"string\" for=\"node\" id=\"invariant.scope\"/>\n"+"<key attr.name=\"namedValue\" attr.type=\"string\" for=\"node\" id=\"named\"/>\n"+"<key attr.name=\"nodeType\" attr.type=\"string\" for=\"node\" id=\"nodetype\">\n"+"<default>path</default>\n"+"</key>"+"<key attr.name=\"isFrontierNode\" attr.type=\"boolean\" for=\"node\" id=\"frontier\">"+"<default>false</default>"+"</key>\n"+"<key attr.name=\"isViolationNode\" attr.type=\"boolean\" for=\"node\" id=\"violation\">\n"+"<default>false</default>\n"+"</key>\n"+"<key attr.name=\"isEntryNode\" attr.type=\"boolean\" for=\"node\" id=\"entry\">\n"+"<default>false</default>\n"+"</key>\n"+"<key attr.name=\"isSinkNode\" attr.type=\"boolean\" for=\"node\" id=\"sink\">\n"+"<default>false</default>"+"</key>"+"<key attr.name=\"isLoopHead\" attr.type=\"boolean\" for=\"node\" id=\"loopHead\">\n"+"<default>false</default>"+"</key>"+"<key attr.name=\"violatedProperty\" attr.type=\"string\" for=\"node\" id=\"violatedProperty\"/>\n"+"<key attr.name=\"threadId\" attr.type=\"string\" for=\"edge\" id=\"threadId\"/>\n"+"<key attr.name=\"sourcecodeLanguage\" attr.type=\"string\" for=\"graph\" id=\"sourcecodelang\"/>\n"+"<key attr.name=\"programFile\" attr.type=\"string\" for=\"graph\" id=\"programfile\"/>\n"+"<key attr.name=\"programHash\" attr.type=\"string\" for=\"graph\" id=\"programhash\"/>\n"+"<key attr.name=\"specification\" attr.type=\"string\" for=\"graph\" id=\"specification\"/>\n"+"<key attr.name=\"memoryModel\" attr.type=\"string\" for=\"graph\" id=\"memorymodel\"/>\n"+"<key attr.name=\"architecture\" attr.type=\"string\" for=\"graph\" id=\"architecture\"/>\n"+"<key attr.name=\"producer\" attr.type=\"string\" for=\"graph\" id=\"producer\"/>\n"+"<key attr.name=\"sourcecode\" attr.type=\"string\" for=\"edge\" id=\"sourcecode\"/>\n"+"<key attr.name=\"startline\" attr.type=\"int\" for=\"edge\" id=\"startline\"/>\n"+"<key attr.name=\"endline\" attr.type=\"int\" for=\"edge\" id=\"endline\"/>\n"+"<key attr.name=\"lineColSet\" attr.type=\"string\" for=\"edge\" id=\"lineCols\"/>\n"+"<key attr.name=\"control\" attr.type=\"string\" for=\"edge\" id=\"control\"/>\n"+"<key attr.name=\"assumption\" attr.type=\"string\" for=\"edge\" id=\"assumption\"/>\n"+"<key attr.name=\"assumption.scope\" attr.type=\"string\" for=\"edge\" id=\"assumption.scope\"/>\n"+"<key attr.name=\"enterFunction\" attr.type=\"string\" for=\"edge\" id=\"enterFunction\"/>\n"+"<key attr.name=\"returnFromFunction\" attr.type=\"string\" for=\"edge\" id=\"returnFrom\"/>"+"<key attr.name=\"predecessor\" attr.type=\"string\" for=\"edge\" id=\"predecessor\"/>\n"+"<key attr.name=\"successor\" attr.type=\"string\" for=\"edge\" id=\"successor\"/>\n"+"<key attr.name=\"witness-type\" attr.type=\"string\" for=\"graph\" id=\"witness-type\"/>\n"+"<graph edgedefault=\"directed\">\n"+"<data key=\"witness-type\">violation_witness</data>\n"+"<data key=\"sourcecodelang\">C</data>"+"<data key=\"producer\">VIAP</data>"+"<data key=\"specification\">"+property+"</data>"+"<data key=\"programfile\">"+filename+"</data>\n"+"<data key=\"programhash\">"+hashcode+"</data>\n"+"<data key=\"memorymodel\">precise</data>\n"+"<data key=\"architecture\">32bit</data>\n"+"\n<node id=\"sink\"><data key=\"sink\">true</data></node>\n"
                                            writtingFile( "errorWitness.graphml" , str(violation_witness1+violation_witness2+"\n</graph>\n</graphml>\n"))
                                            writeLogFile( "j2llogs.logs" , "\nViolation \n"+str(violation_witness1+violation_witness2+"\n</graph>\n</graphml>\n")+"\n" )                                    #print results[result]
                                    return
                
                if len(f_list)==1 and 'main' in f_list:
                    axiommain=axiomeMap['main']
                    vfactsmain=axiommain.getVfact()
                    
                    a=axiommain.getOther_axioms()
                    assert_list_main=axiommain.getAsserts()
                    re_equations=[]
                    for fun in cycle_list:
                        axiom=axiomeMap[fun]
                        if axiom is not None:
                            equations=[]
                            list_exps={}
                            f=axiom.getFrame_axioms()
                            o=axiom.getOutput_equations()
                            witnessXml= witnessXml_map[fun]
                            assert_list=axiom.getAsserts()
                            vfacts=axiom.getVfact()
                            inputvar=axiom.getInputvariable()
                            
                            for x in o:
                                equation=[]
                                equation.append('R')
                                equation.append(inputvar.keys())
                                equation.append(o[x][1])
                                equation.append(o[x][2])
                                a.append(equation)
                                equations.append(copy.deepcopy(equation))
                                re_equations.append(copy.deepcopy(equation))
                            #print '========================='
                            #print axiommain.getOutput_equations()
                            #print '========================='
                            for x in axiommain.getOutput_equations():
                                e=axiommain.getOutput_equations()[x]
                                if '_FAILED' in x and e[0]=='e':
                                    getRecuresiveFunDef(e[2],cycle_list,list_exps)
                                    temp_condition_map={}
                                    getAllCondtion_tactic8(e,temp_condition_map)
                                    list_ConcreteValue = getConcreteValue(temp_condition_map)
                                    #program_analysis,concret_value_map = getRangeValues(axiommain.getOutput_equations(),program_analysis)
                                    
                                    program_analysis_list,concret_value_map_list = getRangeValues(axiommain.getOutput_equations(),program_analysis)
                                    
                                    
                                    if len(list_ConcreteValue)==1:
                                        results=AssetionAnalysis5(program_analysis,program_analysis_decl,list_ConcreteValue[0])
                                        if type(results) is str and  'Termination Failed' in results:
                                            print 'Termination Failed'
                                            return
                                        if results is not None and len(results.keys())>0:
                                            print 'VIAP_STANDARD_OUTPUT_False'
                                            #print 'XXXXX-YYYYY'
                                            #result=AssetionAnalysis3(program_analysis3,program_analysis_decl,file_name,property)
                                            result= AssetionAnalysis3_5(program_analysis3,program_analysis_decl,file_name,property,list_ConcreteValue[0])
                                            if result is not None:
                                                #print "Error Witness Generated"
                                                writtingFile( "errorWitness.graphml" , result )
                                                writeLogFile( "j2llogs.logs" , "\nViolation \n"+str(result)+"\n" )
                                                return
                                            else:
                                                line_no,stmt2 = getLineNumber_terminate('__VERIFIER_error()','main')
                                            
                                                if property is None:
                                                    property="CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )"
                                                else:
                                                    if '=' in property:
                                                        value_names=property.split('=')
                                                        fd = open(value_names[1])
                                                        property = "".join(fd.readlines())
                                                    else:
                                                        property="CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )"
            
                                            
                                                violation_witness2=''
                                                violation_witness2+="<node id=\"N0\"><data key=\"entry\">true</data></node>\n"
                                                violation_witness2+="<node id=\"N"+str(1)+"\">"+"\n<data key=\"violation\">true</data>\n<data key=\"violatedProperty\">__VERIFIER_error(); called in line "+str(line_no)+"</data>\n"+"</node>\n"
                                                violation_witness2+="<edge source=\"N"+str(0)+"\" target=\"N"+str(1)+"\">\n"
                                                violation_witness2+="<data key=\"sourcecode\">__VERIFIER_error();</data>\n"
                                                violation_witness2+="<data key=\"startline\">"+str(line_no)+"</data>\n"
                                                violation_witness2+="<data key=\"endline\">"+str(line_no)+"</data>\n"
                                                violation_witness2+="</edge>\n"
                                            
                                                hashcode=sha1(file_name)
                                                violation_witness1="<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n"+"<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">\n"+"<key attr.name=\"originFileName\" attr.type=\"string\" for=\"edge\" id=\"originfile\">\n"+"<default>"+filename+"</default>\n"+"</key>\n"+"<key attr.name=\"invariant\" attr.type=\"string\" for=\"node\" id=\"invariant\"/>\n"+"<key attr.name=\"invariant.scope\" attr.type=\"string\" for=\"node\" id=\"invariant.scope\"/>\n"+"<key attr.name=\"namedValue\" attr.type=\"string\" for=\"node\" id=\"named\"/>\n"+"<key attr.name=\"nodeType\" attr.type=\"string\" for=\"node\" id=\"nodetype\">\n"+"<default>path</default>\n"+"</key>"+"<key attr.name=\"isFrontierNode\" attr.type=\"boolean\" for=\"node\" id=\"frontier\">"+"<default>false</default>"+"</key>\n"+"<key attr.name=\"isViolationNode\" attr.type=\"boolean\" for=\"node\" id=\"violation\">\n"+"<default>false</default>\n"+"</key>\n"+"<key attr.name=\"isEntryNode\" attr.type=\"boolean\" for=\"node\" id=\"entry\">\n"+"<default>false</default>\n"+"</key>\n"+"<key attr.name=\"isSinkNode\" attr.type=\"boolean\" for=\"node\" id=\"sink\">\n"+"<default>false</default>"+"</key>"+"<key attr.name=\"isLoopHead\" attr.type=\"boolean\" for=\"node\" id=\"loopHead\">\n"+"<default>false</default>"+"</key>"+"<key attr.name=\"violatedProperty\" attr.type=\"string\" for=\"node\" id=\"violatedProperty\"/>\n"+"<key attr.name=\"threadId\" attr.type=\"string\" for=\"edge\" id=\"threadId\"/>\n"+"<key attr.name=\"sourcecodeLanguage\" attr.type=\"string\" for=\"graph\" id=\"sourcecodelang\"/>\n"+"<key attr.name=\"programFile\" attr.type=\"string\" for=\"graph\" id=\"programfile\"/>\n"+"<key attr.name=\"programHash\" attr.type=\"string\" for=\"graph\" id=\"programhash\"/>\n"+"<key attr.name=\"specification\" attr.type=\"string\" for=\"graph\" id=\"specification\"/>\n"+"<key attr.name=\"memoryModel\" attr.type=\"string\" for=\"graph\" id=\"memorymodel\"/>\n"+"<key attr.name=\"architecture\" attr.type=\"string\" for=\"graph\" id=\"architecture\"/>\n"+"<key attr.name=\"producer\" attr.type=\"string\" for=\"graph\" id=\"producer\"/>\n"+"<key attr.name=\"sourcecode\" attr.type=\"string\" for=\"edge\" id=\"sourcecode\"/>\n"+"<key attr.name=\"startline\" attr.type=\"int\" for=\"edge\" id=\"startline\"/>\n"+"<key attr.name=\"endline\" attr.type=\"int\" for=\"edge\" id=\"endline\"/>\n"+"<key attr.name=\"lineColSet\" attr.type=\"string\" for=\"edge\" id=\"lineCols\"/>\n"+"<key attr.name=\"control\" attr.type=\"string\" for=\"edge\" id=\"control\"/>\n"+"<key attr.name=\"assumption\" attr.type=\"string\" for=\"edge\" id=\"assumption\"/>\n"+"<key attr.name=\"assumption.scope\" attr.type=\"string\" for=\"edge\" id=\"assumption.scope\"/>\n"+"<key attr.name=\"enterFunction\" attr.type=\"string\" for=\"edge\" id=\"enterFunction\"/>\n"+"<key attr.name=\"returnFromFunction\" attr.type=\"string\" for=\"edge\" id=\"returnFrom\"/>"+"<key attr.name=\"predecessor\" attr.type=\"string\" for=\"edge\" id=\"predecessor\"/>\n"+"<key attr.name=\"successor\" attr.type=\"string\" for=\"edge\" id=\"successor\"/>\n"+"<key attr.name=\"witness-type\" attr.type=\"string\" for=\"graph\" id=\"witness-type\"/>\n"+"<graph edgedefault=\"directed\">\n"+"<data key=\"witness-type\">violation_witness</data>\n"+"<data key=\"sourcecodelang\">C</data>"+"<data key=\"producer\">VIAP</data>"+"<data key=\"specification\">"+property+"</data>"+"<data key=\"programfile\">"+filename+"</data>\n"+"<data key=\"programhash\">"+hashcode+"</data>\n"+"<data key=\"memorymodel\">precise</data>\n"+"<data key=\"architecture\">32bit</data>\n"+"\n<node id=\"sink\"><data key=\"sink\">true</data></node>\n"
                                                writtingFile( "errorWitness.graphml" , str(violation_witness1+violation_witness2+"\n</graph>\n</graphml>\n"))
                                                writeLogFile( "j2llogs.logs" , "\nViolation \n"+str(violation_witness1+violation_witness2+"\n</graph>\n</graphml>\n")+"\n" )                     
                                                return
                    
                                    elif len(concret_value_map_list)>0 and flag_terminate==False:
                                        list_ConcreteValue.append('0')
                                        
                                        isRunAgain=False
                                        
                                        results=None
                                        
                                        
                                        for program_analysis in program_analysis_list:
                                            
                                            if isRunAgain==False:
                                                
                                                #print '~~~~~~~~~~~~~~~~'
                                                #print program_analysis
                                                #print '~~~~~~~~~~~~~~~~'
                                        
                                                results=AssetionAnalysis5(program_analysis,program_analysis_decl,list_ConcreteValue[0])
                                                
                                                if results is None and type(results) is not str:
                                                    
                                                    isRunAgain=True
                                            
                                            
                                        if type(results) is str and  'Termination Failed' in results:
                                            print 'Termination Failed'
                                            #return
                                        if results is not None and type(results) is not str and len(results.keys())>0:
                                            print 'VIAP_STANDARD_OUTPUT_False'
                                            
                                            #print '~~~~~~~~~~~~~~~~'
                                            #print program_analysis3
                                            #print '~~~~~~~~~~~~~~~~'
            
                                            result=AssetionAnalysis3(program_analysis3,program_analysis_decl,file_name,property)
                                            if result is not None:
                                                #print "Error Witness Generated"
                                                writtingFile( "errorWitness.graphml" , result )
                                                writeLogFile( "j2llogs.logs" , "\nViolation \n"+str(result)+"\n" )
                                                return
                                            else:
                                                line_no,stmt2 = getLineNumber_terminate('__VERIFIER_error()','main')
                                            
                                                if property is None:
                                                    property="CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )"
                                                else:
                                                    if '=' in property:
                                                        value_names=property.split('=')
                                                        fd = open(value_names[1])
                                                        property = "".join(fd.readlines())
                                                    else:
                                                        property="CHECK( init(main()), LTL(G ! call(__VERIFIER_error())) )"
            
                                            
                                                violation_witness2=''
                                                violation_witness2+="<node id=\"N0\"><data key=\"entry\">true</data></node>\n"
                                                violation_witness2+="<node id=\"N"+str(1)+"\">"+"\n<data key=\"violation\">true</data>\n<data key=\"violatedProperty\">__VERIFIER_error(); called in line "+str(line_no)+"</data>\n"+"</node>\n"
                                                violation_witness2+="<edge source=\"N"+str(0)+"\" target=\"N"+str(1)+"\">\n"
                                                violation_witness2+="<data key=\"sourcecode\">__VERIFIER_error();</data>\n"
                                                violation_witness2+="<data key=\"startline\">"+str(line_no)+"</data>\n"
                                                violation_witness2+="<data key=\"endline\">"+str(line_no)+"</data>\n"
                                                violation_witness2+="</edge>\n"
                                            
                                                hashcode=sha1(file_name)
                                                violation_witness1="<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n"+"<graphml xmlns=\"http://graphml.graphdrawing.org/xmlns\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\">\n"+"<key attr.name=\"originFileName\" attr.type=\"string\" for=\"edge\" id=\"originfile\">\n"+"<default>"+filename+"</default>\n"+"</key>\n"+"<key attr.name=\"invariant\" attr.type=\"string\" for=\"node\" id=\"invariant\"/>\n"+"<key attr.name=\"invariant.scope\" attr.type=\"string\" for=\"node\" id=\"invariant.scope\"/>\n"+"<key attr.name=\"namedValue\" attr.type=\"string\" for=\"node\" id=\"named\"/>\n"+"<key attr.name=\"nodeType\" attr.type=\"string\" for=\"node\" id=\"nodetype\">\n"+"<default>path</default>\n"+"</key>"+"<key attr.name=\"isFrontierNode\" attr.type=\"boolean\" for=\"node\" id=\"frontier\">"+"<default>false</default>"+"</key>\n"+"<key attr.name=\"isViolationNode\" attr.type=\"boolean\" for=\"node\" id=\"violation\">\n"+"<default>false</default>\n"+"</key>\n"+"<key attr.name=\"isEntryNode\" attr.type=\"boolean\" for=\"node\" id=\"entry\">\n"+"<default>false</default>\n"+"</key>\n"+"<key attr.name=\"isSinkNode\" attr.type=\"boolean\" for=\"node\" id=\"sink\">\n"+"<default>false</default>"+"</key>"+"<key attr.name=\"isLoopHead\" attr.type=\"boolean\" for=\"node\" id=\"loopHead\">\n"+"<default>false</default>"+"</key>"+"<key attr.name=\"violatedProperty\" attr.type=\"string\" for=\"node\" id=\"violatedProperty\"/>\n"+"<key attr.name=\"threadId\" attr.type=\"string\" for=\"edge\" id=\"threadId\"/>\n"+"<key attr.name=\"sourcecodeLanguage\" attr.type=\"string\" for=\"graph\" id=\"sourcecodelang\"/>\n"+"<key attr.name=\"programFile\" attr.type=\"string\" for=\"graph\" id=\"programfile\"/>\n"+"<key attr.name=\"programHash\" attr.type=\"string\" for=\"graph\" id=\"programhash\"/>\n"+"<key attr.name=\"specification\" attr.type=\"string\" for=\"graph\" id=\"specification\"/>\n"+"<key attr.name=\"memoryModel\" attr.type=\"string\" for=\"graph\" id=\"memorymodel\"/>\n"+"<key attr.name=\"architecture\" attr.type=\"string\" for=\"graph\" id=\"architecture\"/>\n"+"<key attr.name=\"producer\" attr.type=\"string\" for=\"graph\" id=\"producer\"/>\n"+"<key attr.name=\"sourcecode\" attr.type=\"string\" for=\"edge\" id=\"sourcecode\"/>\n"+"<key attr.name=\"startline\" attr.type=\"int\" for=\"edge\" id=\"startline\"/>\n"+"<key attr.name=\"endline\" attr.type=\"int\" for=\"edge\" id=\"endline\"/>\n"+"<key attr.name=\"lineColSet\" attr.type=\"string\" for=\"edge\" id=\"lineCols\"/>\n"+"<key attr.name=\"control\" attr.type=\"string\" for=\"edge\" id=\"control\"/>\n"+"<key attr.name=\"assumption\" attr.type=\"string\" for=\"edge\" id=\"assumption\"/>\n"+"<key attr.name=\"assumption.scope\" attr.type=\"string\" for=\"edge\" id=\"assumption.scope\"/>\n"+"<key attr.name=\"enterFunction\" attr.type=\"string\" for=\"edge\" id=\"enterFunction\"/>\n"+"<key attr.name=\"returnFromFunction\" attr.type=\"string\" for=\"edge\" id=\"returnFrom\"/>"+"<key attr.name=\"predecessor\" attr.type=\"string\" for=\"edge\" id=\"predecessor\"/>\n"+"<key attr.name=\"successor\" attr.type=\"string\" for=\"edge\" id=\"successor\"/>\n"+"<key attr.name=\"witness-type\" attr.type=\"string\" for=\"graph\" id=\"witness-type\"/>\n"+"<graph edgedefault=\"directed\">\n"+"<data key=\"witness-type\">violation_witness</data>\n"+"<data key=\"sourcecodelang\">C</data>"+"<data key=\"producer\">VIAP</data>"+"<data key=\"specification\">"+property+"</data>"+"<data key=\"programfile\">"+filename+"</data>\n"+"<data key=\"programhash\">"+hashcode+"</data>\n"+"<data key=\"memorymodel\">precise</data>\n"+"<data key=\"architecture\">32bit</data>\n"+"\n<node id=\"sink\"><data key=\"sink\">true</data></node>\n"
                                                writtingFile( "errorWitness.graphml" , str(violation_witness1+violation_witness2+"\n</graph>\n</graphml>\n"))
                                                writeLogFile( "j2llogs.logs" , "\nViolation \n"+str(violation_witness1+violation_witness2+"\n</graph>\n</graphml>\n")+"\n" )                     
                                                return


                                        
                                        
                                        
                            for vfact in vfacts:
                                #if vfact[0][-1]!='1' and vfact[0]!=fun:
                                if vfact[0][0:len(vfact[0])-1] not in inputvar and vfact[0]!=fun:
                                    vfactsmain.append(vfact)
                                if vfact[0][-1]=='1' and '_FAILED1' in vfact[0]:
                                    vfactsmain.append(vfact)
                            for list_exp in list_exps:
                                status=prove_assert_tactic6(equations,list_exps[list_exp],cycle_list,vfactsmain,witnessXml)
                                if status is not None:
                                    a.append(status)
                            for tassert in assert_list:
                                assert_list_main.append(tassert)
                    
                    #print '--------------------'
                    #print re_equations
                    vfactsmain=axiommain.getVfact()
                    a=axiommain.getOther_axioms()
                    for x in axiommain.getOutput_equations():
                        if '_FAILED' in x:
                            #e=axiommain.getOutput_equations()[x][2]
                            #print e
                            #print wff2string1(axiommain.getOutput_equations()[x])
                            e=copy.deepcopy(axiommain.getOutput_equations()[x][2])
                            addition_equs = prove_assert_tactic7(e,re_equations,cycle_list,vfactsmain,witnessXml)
                            for addition_equ in addition_equs:
                                a.append(addition_equ)
                            #print wff2string1(axiommain.getOutput_equations()[x])
                    axiommain.setOther_axioms(a)
                    axiomeMap['main']=axiommain
                    #print '--------------------'
                program=programclass(file_name, memberfunctionmap , externalvarmap, axiomeMap, witnessXml_map) 
                #print '@@@@@@------'
                prove_auto_process(program,property,program_analysis3,program_analysis_decl)
                #return program
        else:
        	print 'Error in  Translation'



