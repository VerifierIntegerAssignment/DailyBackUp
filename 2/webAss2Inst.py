#import commandclass
import subprocess, threading
import sys
import os
import wadze
import all_classes as allclass
import FOLTranslation as folTras
currentdirectory = os.path.dirname(os.path.realpath(__file__))






    



def displayOutput(insts_list):

    for inst in insts_list:

        if isinstance(inst, list):

 
           displayOutput(inst)

        else:
    
           print(inst)














def translation(file_name,property=None):

    if not(os.path.exists(file_name)): 
       print("File not exits")
       return

    #command1 = currentdirectory+'/wasi-sdk-11.0/bin/clang'+' '+str(file_name)+'  '+'--target=wasm32-unknown-unknown-wasm -nostartfiles -nostdlib -Wl,--no-entry -Wl,--export-all -o test.wasm'
    #command1 = currentdirectory+'/wasi-sdk-11.0/bin/clang'+' '+str(file_name)+'  '+'--target=wasm32-unknown-unknown-wasm -nostartfiles --include-directory=/home/pritom/web_app/MainDevelopment/2/wasi-sdk-11.0/lib/clang/10.0.0/include  -Wl,--no-entry -Wl,--export-all -o test.wasm'
    command1 = currentdirectory+'/wasi-sdk-11.0/bin/clang'+' '+str(file_name)+'  '+'--target=wasm32-unknown-unknown-wasm -nostartfiles -I'+currentdirectory+"/wasi-sdk-11.0/share/wasi-sysroot/include -L"+currentdirectory+'/wasi-sdk-11.0/share/wasi-sysroot/lib/wasm32-wasi -Wl,--no-entry -Wl,--export-all -o test.wasm'
    print(command1)

    try :
       proc = subprocess.Popen(command1, stdout=subprocess.PIPE,shell=True)
       output = proc.stdout.read()
       status=output
    except OSError  as err:
           print('Error Ocurred While executing command')

    if (os.path.exists(currentdirectory+'/test.wasm')): 
       with open('test.wasm', 'rb') as file:
            data = file.read()
       module = wadze.parse_module(data)

       # If you also want function code decoded into instructions, do this
       module['code'] = [ wadze.parse_code(c) for c in module['code']]

       global_stack = [] 

       list_fun_para =[]

       list_fun_ret = []

       list_fun_obj = []

       list_table_obj = []

       list_global_obj = []

       list_memory_obj = []

       export_map_memory = {}

       export_map_function = {}

       export_map_global = {}



       for x in module['type']:
                  
           list_fun_para.append(x[0])

           list_fun_ret.append(x[1])

       for x in module['func']:

           funcObj = allclass.functionclass(x, list_fun_para[x], list_fun_ret[x])

           list_fun_obj.append(funcObj)

       for x in module['table']:

           tableObj = allclass.tableclass(x[0],x[1])

           list_table_obj.append(tableObj)


       global_counter=0

       for x in module['global']:

           
           globalObj = allclass.globalclass('v'+str(global_counter)+'g', x[0][0], x[0][1], x[1])

           global_counter = global_counter+1

           list_global_obj.append(globalObj)


       list_memory_obj = module['memory']

       for x in module['export']:

           if isinstance(x, wadze.ExportGlobal):

              export_map_global[x[1]] = x[0]


           if isinstance(x, wadze.ExportFunction):

              export_map_function[x[1]] = x[0]
       

           if isinstance(x, wadze.ExportMemory):

              export_map_memory[x[1]] = x[0]


       exportMapObj = allclass.exportMapclass(export_map_memory, export_map_function, export_map_global)


       fun_list = []       

       vfact_map = {}
       
       
       for exp in module['code']:

           local_stack = []

           insts_list = []

           varcount = 1 #Counter for variables 

           var_list = [] #List of all local variable

           for x in exp.locals:
             
               varcount = varcount+1


               varObj = allclass.variableclass('v'+str(varcount)+'l',x)

               var_list.append(varObj)




           for inst in exp.instructions:

               print(inst)

           print('``````````````````````````````')

           #for x in insts_list:

           #    print(x)

           #print(insts_list)

           #print('``````````````````````````````')

           #displayOutput(insts_list)




#file_name='test2.c'
#file_name='test/afnp2014_true-unreach-call-i.c'
#file_name='test/bhmr2007_true-unreach-call-i1.c'
file_name='test/ddlm2013_true-unreach-call-i.c'
#file_name='test/test3.c'

translation(file_name)



#test=['-1', 'prog', [['-1', 'fun', ['main'], ['-1', 'seq', ['-1', '=', ['RET'], ['0']], ['-1', 'seq', ['-1', '=', ['x'], ['1']], ['-1', 'seq', ['-1', '=', ['y'], ['0']], ['-1', 'seq', ['-1', 'while', ['<', ['y'], ['1000']], ['-1', 'seq', ['-1', '=', ['x'], ['+', ['x'], ['y']]], ['-1', '=', ['y'], ['+', ['y'], ['1']]]]], ['-1', '=', ['RET'], ['0']]]]]]]]]

#vtest={'main': {'y': ['_y1', 'int'], 'x': ['_y2', 'int'], 'RET': ['_y3', 'int']}}

#folTras.translate1(test,vtest,1)
