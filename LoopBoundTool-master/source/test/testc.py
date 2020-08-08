def getVariablesC(statements):
    localvarmap={}
    if statements is None:
        return localvarmap
    for decl in statements:
        if type(decl) is c_ast.Decl:
            var_type=None
            initial_value=None
            structType=None
            if type(decl.type) is c_ast.ArrayDecl:
                #if checkingArrayName(decl.type)==True:
                if is_number(decl.name[-1])==True:
                    decl=c_ast.Decl(name=decl.name+'_var', quals=decl.quals, storage=decl.storage, funcspec=decl.funcspec,   type=renameArrayName(decl.type), init=decl.init, bitsize=decl.bitsize)
                elif decl.name in ['S','Q','N','in','is']:
                    decl=c_ast.Decl(name=decl.name+'_var', quals=decl.quals, storage=decl.storage, funcspec=decl.funcspec, type=renameArrayName(decl.type), init=decl.init, bitsize=decl.bitsize)
            elif type(decl.type) is c_ast.PtrDecl:
                if type(decl.type.type) is c_ast.TypeDecl:
                    if is_number(decl.type.type.declname[-1])==True:
                        decl.type.type=c_ast.TypeDecl(decl.type.type.declname+'_var', quals=decl.type.type.quals, type=decl.type.type.type)
                    elif decl.name in ['S','Q','N','in','is']:
                        decl.type.type=c_ast.TypeDecl(decl.type.type.declname+'_var', quals=decl.type.type.quals, type=decl.type.type.type)
            else:
                if is_number(decl.type.declname[-1])==True :
                    decl=c_ast.Decl(name=decl.name+'_var', quals=decl.quals, storage=decl.storage, funcspec=decl.funcspec, type=c_ast.TypeDecl(declname=decl.type.declname+'_var', quals=decl.type.quals, type=decl.type.type), init=decl.init, bitsize=decl.bitsize)


            if type(decl.type) is c_ast.ArrayDecl:
                degree=0
                dimensionmap={}
                var_type,degree,structType=getArrayDetails(decl,degree,dimensionmap)
                variable=variableclass(decl.name, var_type,None,dimensionmap,initial_value,structType)
            elif type(decl.type) is c_ast.PtrDecl:
                degree=0
                dimensionmap={}
                var_type,degree,structType=getArrayDetails(decl,degree,dimensionmap)
                variable=variableclass(decl.name, var_type,'Pointer',dimensionmap,initial_value,structType)
            else:
            	for child in decl.children():
                    if type(child[1]) is c_ast.TypeDecl:
                        if type(child[1].type) is c_ast.IdentifierType:
                            var_type=child[1].type.names[0]
                        else:
                            if type(child[1].type) is c_ast.Struct:
                                structType=child[1].type.name
                                var_type=child[1].type.name
                            else:
                                initial_value=child[1].value
                    else:
                    		if type(child[1]) is c_ast.FuncCall:
                                        parameter=''
                                        if child[1].args is not None:
                                                for param in child[1].args.exprs:
                                                       if type(param) is c_ast.ID:
                                                               if parameter=='':
                                                                        parameter = "expres('"+param.name+"')"
                                                               else:
                                                                        parameter += ",expres('"+param.name+"')"
                                                       elif type(param) is c_ast.Constant:
                                                                if parameter=='':
                                                                        parameter = "expres('"+param.value+"')"
								else:
                                                                        parameter += ",expres('"+param.value+"')"
                                                       else:
                                                                if type(statement) is c_ast.ArrayRef:
									degree=0
									stmt,degree=createArrayList_C(statement,degree)
								    	if parameter=='':
										parameter = "expres('d"+str(degree)+'array'+"',["+stmt+"])"
									else:
		        							parameter += ","+"expres('d"+str(degree)+'array'+"',["+stmt+"])"
						#initial_value="['"+child[1].name.name+"',"+parameter+"]"
						initial_value="['"+child[1].name.name+"',"+parameter+"]"
					else:
						#initial_value="expres('"+child[1].name.name+"'"+")"
						initial_value=child[1].name.name
				else:
					if type(child[1]) is c_ast.Constant:
						initial_value=child[1].value
                                        elif type(child[1]) is c_ast.ID:
						initial_value=child[1].name
					else:
                                                #print expressionCreator_C(child[1])
						initial_value=child[1]
            	variable=variableclass(decl.name, var_type,None,None,initial_value,structType)
            localvarmap[decl.name]=variable
        elif type(decl) is c_ast.While:
        	localvarmap_temp=getVariablesC(decl.stmt.block_items)
        	for var in localvarmap_temp.keys():
        		localvarmap[var]=localvarmap_temp[var]
        elif type(decl) is c_ast.If:
        	localvarmap_temp=getVariablesC_If(decl)
        	for var in localvarmap_temp.keys():
        		localvarmap[var]=localvarmap_temp[var]
    return localvarmap
