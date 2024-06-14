
.data
    n: .word 10
    
.text
.globl __start


FUNCTION:
    # Todo: Define your own function in HW1
    # You should store the output into x10
  
    addi a2, x0, 4 # a2 = 4
    add a1, x10, x0
    # jal x1, funct_T
    # beq x0, x0, end
  
funct_T:
  # store into mem
    addi sp, sp, -8
    sw x1, 4(sp)
    sw a1, 0(sp) # old n
     
  # n = 1, 2, 3
    bge a1, a2, fourup
    addi a1, x0, 3 # 3 stored in a1
    addi sp, sp, 8
    jalr x0, 0(x1) # return
  
  # n > 3
fourup:

  # call T(n/4
    srai a1, a1, 2 # a1 = n/4
    jal x1, funct_T 

  # restore sp
    addi t1, a1, 0 # return value T(n/4)
    lw a1, 0(sp) # old n (back here!)
    lw x1, 4(sp) 
    addi sp, sp, 8

  # )*3 +10n +3
    slli t2, t1, 1
    add t1, t1, t2 # T(n/4)
    slli t2, a1, 1
    add t1, t1, t2
    slli t2, t2, 2
    add t1, t1, t2
    addi a1, t1, 3 # return value stored in a1
    jalr x0, 0(x1) # return 
    
  
# end:
    addi a2, x0, 0 # reset a2
    add x10, x0, a1
  

  
# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1,FUNCTION
    la   t0, n
    sw   x10, 4(t0)
    addi a0,x0,10
    ecall