#import commandclass
import subprocess, threading
import sys
import os
import wadze
import all_classes as allclass
import FOLTranslation as folTras
currentdirectory = os.path.dirname(os.path.realpath(__file__))

def ifConstruct(insts_list):

    inst_bef_list=[]

    inst_aft_list=[]

    cond_found = False

    cond_expr = None

    for inst in insts_list:

        if isinstance(inst, list):

              if cond_found == False:

                 inst_bef_list.append(inst)

              else:

                 inst_aft_list.append(inst)

        else:

           if("['-1','if1'," in inst):

              cond_found = True

              cond_expr = eval(inst)

           elif cond_found == False:

              inst_bef_list.append(inst)

           else:

              inst_aft_list.append(inst)

    #print('%%%%%%%%%%%%%%%%%%%%')
    #print(inst_aft_list)
    #print('%%%%%%%%%%%%%%%%%%%%')
    #print(inst_bef_list)
    #print('%%%%%%%%%%%%%%%%%%%%')

    seri_inst = postProcessHandleOutPut(inst_bef_list)

    #print('%%%%%%%%%%%%%%%%%%%%')
    #print(inst_aft_list)
    #print('%%%%%%%%%%%%%%%%%%%%')
    #print(inst_bef_list)
    #print('%%%%%%%%%%%%%%%%%%%%')
    #print(seri_inst)
    #print('%%%%%%%%%%%%%%%%%%%%')

    comb_both = inst_aft_list + inst_bef_list

    loop_inst = postProcessHandleOutPut(comb_both)

    

    cond_expr.append(loop_inst)
 
    return seri_inst, cond_expr




def loopConstruct(insts_list):

    inst_bef_list=[]

    inst_aft_list=[]

    cond_found = False

    cond_expr = None

    for inst in insts_list:

        if isinstance(inst, list):


           if cond_found == False:

              inst_bef_list.append(inst)

           else:

              inst_aft_list.append(inst)

        else:

           if("['-1','while'," in inst):

              cond_found = True

              cond_expr = eval(inst)

           elif cond_found == False:

              inst_bef_list.append(inst)

           else:

              inst_aft_list.append(inst)

    seri_inst = postProcessHandleOutPut(inst_bef_list)

    comb_both = inst_aft_list + inst_bef_list

    loop_inst = postProcessHandleOutPut(comb_both)

    cond_expr.append(loop_inst)
 
    return seri_inst, cond_expr
    



def displayOutput(insts_list):

    for inst in insts_list:

        if isinstance(inst, list):

 
           displayOutput(inst)

        else:
    
           print(inst)




def postProcessHandleOutPut(insts_list):

    inst_stack =[]

    for inst in insts_list:

        #print(inst)
        
        inst_stack.append(inst)

    #print('********************')

    program = None

    while inst_stack:

        inst = inst_stack.pop()

        if program is None:

           if isinstance(inst, list):

               print('============================@@@@@@@@@@@@@@@@@@@@@')
               print(inst)
               print('============================@@@@@@@@@@@@@@@@@@@@@')

               if inst[0]=='loop':

                  seri_inst, cond_expr = loopConstruct(inst[1:])

                  temp_program = eval("['-1', 'seq']")

                  temp_program.append(seri_inst)

                  temp_program.append(cond_expr)

                  program = temp_program

               elif inst[0]=='blockIfElse':


                  temp_program = eval(inst[1])

                  ifCase = postProcessHandleOutPut(inst[2])

                  temp_program.append(ifCase)

                  elseCase = postProcessHandleOutPut(inst[3])

                  temp_program.append(elseCase)

                  program = temp_program


               else:

                  seri_inst, cond_expr = ifConstruct(inst[1:])

                  if seri_inst is not None:

                     temp_program = eval("['-1', 'seq']")

                     temp_program.append(seri_inst)

                     temp_program.append(cond_expr)

                     program = temp_program

                  else:

                     program = cond_expr


           else:

               program = eval(inst)

        else:

           if isinstance(inst, list):

               if inst[0]=='loop':

                  seri_inst, cond_expr = loopConstruct(inst[1:])

                  temp_program = eval("['-1', 'seq']")

                  temp_program.append(seri_inst)

                  temp_program.append(cond_expr)

                  temp_program2 = eval("['-1', 'seq']")

                  temp_program2.append(temp_program)

                  temp_program2.append(program)

                  program = temp_program2


               elif inst[0]=='blockIfElse':


                  temp_program = eval(inst[1])

                  ifCase = postProcessHandleOutPut(inst[2])

                  temp_program.append(ifCase)

                  elseCase = postProcessHandleOutPut(inst[3])

                  temp_program.append(elseCase)

                  temp_program2 = eval("['-1', 'seq']")

                  temp_program2.append(temp_program)

                  temp_program2.append(program)

                  program = temp_program2


               else:


                seri_inst, cond_expr = ifConstruct(inst[1:])


                if seri_inst is not None:

                    temp_program = eval("['-1', 'seq']")

                    temp_program.append(seri_inst)

                    temp_program.append(cond_expr)

                    temp_program2 = eval("['-1', 'seq']")

                    temp_program2.append(temp_program)

                    temp_program2.append(program)

                    program = temp_program2

                else:

                     temp_program2 = eval("['-1', 'seq']")

                     temp_program2.append(cond_expr)

                     temp_program2.append(program)

                     program = temp_program2


           else:

               temp_program = eval("['-1', 'seq',"+inst+"]")

               temp_program.append(program)

               program = temp_program

    return program









def blockHandler(codelist, global_stack,local_stack):

    insts_list = []

    for inst in codelist:

        print(inst)

        print('=============1')

        if len(inst)==1:

           if inst[0] =='i32.sub':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['-',"+temp2+","+temp1+"]")

           elif inst[0] =='i32.add':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['+',"+temp2+","+temp1+"]")

           elif inst[0] =='i32.mul':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['*',"+temp2+","+temp1+"]")

           elif inst[0] =='i32.and':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['&',"+temp2+","+temp1+"]")

           elif inst[0] =='i32.or':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['|',"+temp2+","+temp1+"]")

           elif inst[0] =='i32.div_s':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['/',['"+temp2+"'],['"+temp1+"']]")

           elif inst[0] =='i32.div_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['/',"+temp2+","+temp1+"]")

           elif inst[0] == 'i32.gt_s':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['>',"+temp2+","+temp1+"]")

           elif inst[0] == 'i32.lt_s' or inst[0] == 'i32.lt_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['<',"+temp2+","+temp1+"]")


           elif inst[0] == 'i32.ge_s' or inst[0] == 'i32.ge_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['>=',"+temp2+","+temp1+"]")

           elif inst[0] == 'i32.le_s' or inst[0] == 'i32.le_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['<=',"+temp2+","+temp1+"]")


           elif inst[0] =='i64.sub' :

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['-',"+temp2+","+temp1+"]")

           elif inst[0] =='i64.add':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['+',"+temp2+","+temp1+"]")

           elif inst[0] =='i64.mul':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['*',"+temp2+","+temp1+"]")

           elif inst[0] =='i64.and':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['&',"+temp2+","+temp1+"]")

           elif inst[0] =='i64.or':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['|',"+temp2+","+temp1+"]")

           elif inst[0] =='i64.div_s':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['/',"+temp2+","+temp1+"]")

           elif inst[0] =='i64.div_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['/',"+temp2+","+temp1+"]")

           elif inst[0] == 'i64.gt_s' or inst[0] == 'i64.gt_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['>',"+temp2+","+temp1+"]")

           elif inst[0] == 'i64.lt_s' or inst[0] == 'i64.lt_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['<',"+temp2+","+temp1+"]")


           elif inst[0] == 'i64.ge_s' or inst[0] == 'i64.ge_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['>=',"+temp2+","+temp1+"]")

           elif inst[0] == 'i64.le_s' or inst[0] == 'i64.le_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['<=',"+temp2+","+temp1+"]")


           elif inst[0] =='i64.extend_i32_s':

              temp = local_stack.pop()

              local_stack.append("['extend32to64fun',"+temp+"]")

           elif inst[0] == 'f64.convert_i64_s':

              temp = local_stack.pop()

              local_stack.append("['converti64tof64fun',"+str(temp)+"]")

           elif inst[0] == 'return':

              
              if len(local_stack)>0:

                 temp = local_stack.pop()

                 insts_list.append("['-1','=',['ret'],"+str(temp)+"]")


           elif inst[0] == 'i32.eqz':
       
             temp = local_stack.pop()

             local_stack.append("['==',"+temp+",['0']]")


        elif len(inst)==2:

          inst_type, inst_operant = inst

          if inst_type=='call':

             if inst_operant==4:

                var_name = '__VERIFIER_nondet_int'
                
                local_stack.append("['"+var_name+"']")

             elif inst_operant==2:

                temp = local_stack.pop()

                insts_list.append("['-1','=',['assume'],"+temp+"]")


             elif inst_operant==3:

                temp = local_stack.pop()

                insts_list.append("['-1','=',['assert'],"+temp+"]")

          elif inst_type=='br_if':

             temp = local_stack.pop()

             insts_list.append("['-1','while',['=',"+temp+",['0']]]")

          elif inst_type=='global.get':

             var_name='v'+str(inst_operant)+'g'

             local_stack.append("['"+var_name+"']")

          elif inst_type=='global.set':

             temp = local_stack.pop()

             var_name='v'+str(inst_operant)+'g'

             insts_list.append("['-1','=',['"+var_name+"'],"+temp+"]")

          elif inst_type=='local.get':

             var_name='v'+str(inst_operant)+'l'

             local_stack.append("['"+var_name+"']")

          elif inst_type=='local.set':

             temp = local_stack.pop()

             var_name='v'+str(inst_operant)+'l'

             insts_list.append("['-1','=',['"+var_name+"'],"+temp+"]")

          elif inst_type=='i32.const':

              local_stack.append("['"+str(inst_operant)+"']")

          elif inst_type=='i64.const':

              local_stack.append("['"+str(inst_operant)+"']")



        elif len(inst)==3:

          inst_type, inst_operant1, inst_operant2 = inst

          if inst_type =='block':


              if len(inst_operant2)==1:

                  t_inst_type, t_inst_operant1, t_inst_operant2 = inst_operant2[0]

                  if t_inst_type=='loop':

                    #print('BBBBB')
                  
                    local_insts_list = blockHandler(t_inst_operant2, global_stack, local_stack)

                  else:

                    #print('AAAA')
                        
                    local_insts_list = blockHandlerIf(t_inst_operant2, global_stack, local_stack)

                  insts_list.append([t_inst_type]+local_insts_list)

              else:
                  #print('CCCCC')

                  local_insts_list = blockHandlerIf(inst_operant2, global_stack, local_stack)


                  if len(local_insts_list)>0 and local_insts_list[0][0]=='block':

                     if1_2_if2 = eval(local_insts_list[0][1])

                     if1_2_if2[1] = 'if2'

                     new_local_insts_list=['blockIfElse']+[str(if1_2_if2)]+[local_insts_list[0][2:]]+[local_insts_list[1:]]

                     insts_list.append(new_local_insts_list)

                     #print('=====================================xx')
                  
                  else:

                     insts_list.append(['block']+local_insts_list)

                     #print('=====================================xxxx')
                  

          elif inst_type =='loop':

              local_insts_list = blockHandler(inst_operant2, global_stack, local_stack)

              if len(local_insts_list)>0:
              
                 insts_list.append('loop')

                 insts_list.append(local_insts_list)

              #insts_list.append('end')

          elif inst_type =='i32.store':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              #insts_list.append('memory'+str(inst_operant1)+'off32['+str(temp2)+' + '+str(inst_operant2)+'] = '+str(temp1)+";")

              insts_list.append("['-1','=',['memory"+str(inst_operant1)+"op32off',['+',"+str(temp2)+",['"+str(inst_operant2)+"']]],"+str(temp1)+"]")



          elif inst_type =='i64.store':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              #insts_list.append('memory'+str(inst_operant1)+'off64['+str(temp2)+' + '+str(inst_operant2)+'] = '+str(temp1)+";")

              insts_list.append("['-1','=',['memory"+str(inst_operant1)+"op64off',['+',"+str(temp2)+",['"+str(inst_operant2)+"']]],"+str(temp1)+"]")


          elif inst_type =='i32.load':


              temp = local_stack.pop()

              
              local_stack.append("['memory"+str(inst_operant1)+"op32off',['+',"+str(temp)+",['"+str(inst_operant2)+"']]]")


          elif inst[0] =='i64.load':


              temp = local_stack.pop()
              

              local_stack.append("['memory"+str(inst_operant1)+"op32off',['+',"+str(temp)+",['"+str(inst_operant2)+"']]]")


          else:

              print('========================')

              print(inst_type)

              print(inst_operant1)

              print(inst_operant2)

              print('========================')

        else:

          inst_type = inst           
          print('========================')
          print(inst_type)
          print('========================')


    return insts_list




def blockHandlerIf(codelist, global_stack,local_stack):

    insts_list = []

    for inst in codelist:

        #print(inst)
        #print('=============2')

        if len(inst)==1:

           if inst[0] =='i32.sub':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['-',"+temp2+","+temp1+"]")

           elif inst[0] =='i32.add':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['+',"+temp2+","+temp1+"]")

           elif inst[0] =='i32.mul':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['*',"+temp2+","+temp1+"]")

           elif inst[0] =='i32.and':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['&',"+temp2+","+temp1+"]")

           elif inst[0] =='i32.or':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['|',"+temp2+","+temp1+"]")

           elif inst[0] =='i32.div_s':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['/',['"+temp2+"'],['"+temp1+"']]")

           elif inst[0] =='i32.div_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['/',"+temp2+","+temp1+"]")

           elif inst[0] == 'i32.gt_s':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['>',"+temp2+","+temp1+"]")

           elif inst[0] == 'i32.lt_s' or inst[0] == 'i32.lt_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['<',"+temp2+","+temp1+"]")


           elif inst[0] == 'i32.ge_s' or inst[0] == 'i32.ge_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['>=',"+temp2+","+temp1+"]")

           elif inst[0] == 'i32.le_s' or inst[0] == 'i32.le_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['<=',"+temp2+","+temp1+"]")


           elif inst[0] =='i64.sub' :

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['-',"+temp2+","+temp1+"]")

           elif inst[0] =='i64.add':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['+',"+temp2+","+temp1+"]")

           elif inst[0] =='i64.mul':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['*',"+temp2+","+temp1+"]")

           elif inst[0] =='i64.and':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['&',"+temp2+","+temp1+"]")

           elif inst[0] =='i64.or':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['|',"+temp2+","+temp1+"]")

           elif inst[0] =='i64.div_s':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['/',"+temp2+","+temp1+"]")

           elif inst[0] =='i64.div_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['/',"+temp2+","+temp1+"]")

           elif inst[0] == 'i64.gt_s' or inst[0] == 'i64.gt_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['>',"+temp2+","+temp1+"]")

           elif inst[0] == 'i64.lt_s' or inst[0] == 'i64.lt_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['<',"+temp2+","+temp1+"]")


           elif inst[0] == 'i64.ge_s' or inst[0] == 'i64.ge_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['>=',"+temp2+","+temp1+"]")

           elif inst[0] == 'i64.le_s' or inst[0] == 'i64.le_u':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              local_stack.append("['<=',"+temp2+","+temp1+"]")


           elif inst[0] =='i64.extend_i32_s':

              temp = local_stack.pop()

              local_stack.append("['extend32to64fun',"+temp+"]")

           elif inst[0] == 'f64.convert_i64_s':

              temp = local_stack.pop()

              local_stack.append("['converti64tof64fun',"+str(temp)+"]")

           elif inst[0] == 'return':

              if len(local_stack)>0:

                 temp = local_stack.pop()

                 insts_list.append("['-1','=',['ret'],"+str(temp)+"]")

           elif inst[0] == 'i32.eqz':
       
             temp = local_stack.pop()

             local_stack.append("['==',"+temp+",['0']]")


        elif len(inst)==2:

          inst_type, inst_operant = inst

          if inst_type=='call':

             if inst_operant==4:

                var_name = '__VERIFIER_nondet_int'
                
                local_stack.append("['"+var_name+"']")

             elif inst_operant==2:

                temp = local_stack.pop()

                insts_list.append("['-1','=',['assume'],"+temp+"]")


             elif inst_operant==3:

                temp = local_stack.pop()

                insts_list.append("['-1','=',['assert'],"+temp+"]")


          elif inst_type=='br_if':

             temp = local_stack.pop()

             insts_list.append("['-1','if1',['=',"+temp+",['0']]]")

          elif inst_type=='global.get':

             var_name='v'+str(inst_operant)+'g'

             local_stack.append("['"+var_name+"']")

          elif inst_type=='global.set':

             temp = local_stack.pop()

             var_name='v'+str(inst_operant)+'g'

             insts_list.append("['-1','=',['"+var_name+"'],"+temp+"]")

          elif inst_type=='local.get':

             var_name='v'+str(inst_operant)+'l'

             local_stack.append("['"+var_name+"']")

          elif inst_type=='local.set':

             temp = local_stack.pop()

             var_name='v'+str(inst_operant)+'l'

             insts_list.append("['-1','=',['"+var_name+"'],"+temp+"]")

          elif inst_type=='i32.const':

              local_stack.append("['"+str(inst_operant)+"']")

          elif inst_type=='i64.const':

              local_stack.append("['"+str(inst_operant)+"']")



        elif len(inst)==3:

          inst_type, inst_operant1, inst_operant2 = inst

          if inst_type =='block':


              if len(inst_operant2)==1:

                  t_inst_type, t_inst_operant1, t_inst_operant2 = inst_operant2[0]

                  if t_inst_type=='loop':
                    print('aaaaa')
                  
                    local_insts_list = blockHandler(t_inst_operant2, global_stack, local_stack)

                  else:

                    print('bbbbb')

                    local_insts_list = blockHandlerIf(t_inst_operant2, global_stack, local_stack)

                  insts_list.append([t_inst_type]+local_insts_list)

              else:

                  print('cccccc')
                  
                  local_insts_list = blockHandlerIf(inst_operant2, global_stack, local_stack)

                  if len(local_insts_list)>0 and local_insts_list[0][0]=='block':

                     if1_2_if2 = eval(local_insts_list[0][1])

                     if1_2_if2[1] = 'if2'

                     new_local_insts_list=['blockIfElse']+[str(if1_2_if2)]+[local_insts_list[0][2:]]+[local_insts_list[1:]]

                     insts_list.append(new_local_insts_list)

                     print('=====================================xx')
                  
                  else:

                     insts_list.append(['block']+local_insts_list)

                     print('=====================================xxxx')


          elif inst_type =='loop':

              local_insts_list = blockHandler(inst_operant2, global_stack, local_stack)

              if len(local_insts_list)>0:              

                 insts_list.append('loop')

                 insts_list.append(local_insts_list)

              #insts_list.append('end')

          elif inst_type =='i32.store':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              #insts_list.append('memory'+str(inst_operant1)+'off32['+str(temp2)+' + '+str(inst_operant2)+'] = '+str(temp1)+";")

              insts_list.append("['-1','=',['memory"+str(inst_operant1)+"op32off',['+',"+str(temp2)+",['"+str(inst_operant2)+"']]],"+str(temp1)+"]")



          elif inst_type =='i64.store':

              temp1 = local_stack.pop()

              temp2 = local_stack.pop()

              #insts_list.append('memory'+str(inst_operant1)+'off64['+str(temp2)+' + '+str(inst_operant2)+'] = '+str(temp1)+";")

              insts_list.append("['-1','=',['memory"+str(inst_operant1)+"op64off',['+',"+str(temp2)+",['"+str(inst_operant2)+"']]],"+str(temp1)+"]")


          elif inst_type =='i32.load':


              temp = local_stack.pop()

              
              local_stack.append("['memory"+str(inst_operant1)+"op32off',['+',"+str(temp)+",['"+str(inst_operant2)+"']]]")


          elif inst[0] =='i64.load':


              temp = local_stack.pop()
              

              local_stack.append("['memory"+str(inst_operant1)+"op32off',['+',"+str(temp)+",['"+str(inst_operant2)+"']]]")


          else:

              print('========================')

              print(inst_type)

              print(inst_operant1)

              print(inst_operant2)

              print('========================')

        else:

          inst_type = inst           
          print('========================')
          print(inst_type)
          print('========================')


    return insts_list





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

       fun_count = 0
       
       
       for exp in module['code']:

           fun_count = fun_count + 1

           if(fun_count==len(list_fun_obj)-1):

    
                local_stack = []

                insts_list = []

                varcount = 1 #Counter for variables 

                var_list = [] #List of all local variable

                for x in exp.locals:
             
                   varcount = varcount+1

                   varObj = allclass.variableclass('v'+str(varcount)+'l',x)

                   var_list.append(varObj)


                insts_list = blockHandler(exp.instructions, global_stack, local_stack)

                #print('``````````````````````````````')

                #for x in insts_list:

                #    print(x)

                #print(insts_list)

                #print('``````````````````````````````')

                #displayOutput(insts_list)

                program = postProcessHandleOutPut(insts_list)

                if program is not None:

              

                   program_fun=[]

                   program_fun.append('-1')

                   program_fun.append('fun')

                   program_fun.append(['function'+str(fun_count)])

                   program_fun.append(program)

                   fun_list.append(program_fun)

                   vfact={}

                   vfactCount = 0

                   for varObj in var_list:

                       vfactCount = vfactCount+1

                       keyvalue = varObj.getVariablename()

                       temp_list = []

                       temp_list.append('_x'+str(vfactCount))

                       temp_list.append('int')

                       vfact[keyvalue] = temp_list


                   for varObj in list_global_obj:

                       vfactCount = vfactCount+1

                       keyvalue = varObj.getGlobalname()

                       temp_list = []

                       temp_list.append('_x'+str(vfactCount))

                       temp_list.append('int')

                       vfact[keyvalue] = temp_list


                   temp_list1 = []

                   vfactCount = vfactCount+1

                   temp_list1.append('_x'+str(vfactCount))

                   temp_list1.append('int')

                   temp_list1.append('int')

                   vfact['memory2op32off'] = temp_list1

                   temp_list2 = []

                   vfactCount = vfactCount+1

                   temp_list2.append('_x'+str(vfactCount))

                   temp_list2.append('int')

                   temp_list2.append('int')

                   vfact['memory3op64off'] = temp_list2


                   temp_list3 = []

                   vfactCount = vfactCount+1

                   temp_list3.append('_x'+str(vfactCount))

                   temp_list3.append('int')

                   vfact['ret'] = temp_list3

                   temp_list4 = []

                   vfactCount = vfactCount+1

                   temp_list4.append('_x'+str(vfactCount))

                   temp_list4.append('int')

                   vfact['assert'] = temp_list4

                   temp_list5 = []

                   vfactCount = vfactCount+1

                   temp_list5.append('_x'+str(vfactCount))

                   temp_list5.append('int')

                   vfact['assume'] = temp_list5


                   vfact_map['function'+str(fun_count)] = vfact


       main_program = []

       main_program.append('-1')

       main_program.append('prog')

       main_program.append(fun_list)

       print(main_program)

       print(vfact_map)

       #print(vfact)

       folTras.translate1(main_program,vfact_map,1)

       #print(local_stack)


#file_name='test2.c'
#file_name='test/afnp2014_true-unreach-call-i1.c'
#file_name='test/bhmr2007_true-unreach-call-i1.c'
file_name='test/ddlm2013_true-unreach-call-i.c'
#file_name='test/test3.c'

translation(file_name)



#test=['-1', 'prog', [['-1', 'fun', ['main'], ['-1', 'seq', ['-1', '=', ['RET'], ['0']], ['-1', 'seq', ['-1', '=', ['x'], ['1']], ['-1', 'seq', ['-1', '=', ['y'], ['0']], ['-1', 'seq', ['-1', 'while', ['<', ['y'], ['1000']], ['-1', 'seq', ['-1', '=', ['x'], ['+', ['x'], ['y']]], ['-1', '=', ['y'], ['+', ['y'], ['1']]]]], ['-1', '=', ['RET'], ['0']]]]]]]]]

#vtest={'main': {'y': ['_y1', 'int'], 'x': ['_y2', 'int'], 'RET': ['_y3', 'int']}}

#folTras.translate1(test,vtest,1)
