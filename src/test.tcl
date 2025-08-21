clear -all

# Analyze your RTL and testbench
analyze -sv09 formal_tb.sv femtorv32.sv      rv32i_alu.v      rv32i_fetch.v         rv32i_soc.v  rv32i_basereg.v  rv32i_forwarding.v    rv32i_writeback.v rv32i_core.v     rv32i_header.vh      fwb_master.v  rv32i_csr.v      rv32i_memoryaccess.v   rv32i_decoder.v 

elaborate -top formal_tb  

# Set clock and reset
clock clk
reset ~resetn

# Instruction memory setup for ft and pc memory
#assume {rst -> u_mem.u_ram.ram[0] == 32'h02800093}
#assume -reset {ft_mem_wmask == 4'h 0}
# assume -reset {ft_memory[0] == 32'h 02800093}
# assume -reset {ft_memory[1] == 32'h 0000a023}
# assume -reset {ft_memory[2] == 32'h 0000a103}
# assume -reset {ft_memory[3] == 32'h 00110113}
# assume -reset {ft_memory[4] == 32'h 0020a023}
# assume -reset {ft_memory[5] == 32'h ff5ff06f}

# assume -reset {u_mem.u_ram.ram[0] == 32'h02800093}
# assume -reset {u_mem.u_ram.ram[1] == 32'h0000a023}
# assume -reset {u_mem.u_ram.ram[2] == 32'h0000a103}
# assume -reset {u_mem.u_ram.ram[3] == 32'h00110113}
# assume -reset {u_mem.u_ram.ram[4] == 32'h0020a023}
# assume -reset {u_mem.u_ram.ram[5] == 32'hff5ff06f}

# set MEMSIZE 32
# # Zero out the rest
# for {set i 6} {$i < $MEMSIZE} {incr i} {
#     assume -reset [format {ft_memory[%d] == 32'h11111111} $i]
#     assume -reset [format {uut.m1.memory_regfile[%d] == 32'h11111111} $i]
# }

# set MEMSIZE 32
# for {set i 0} {$i < $MEMSIZE} {incr i} {
#     assume -reset [format {
#         (
#             ((uut.m1.memory_regfile[%d] & 32'hfe00707f) == 32'h00000033)


#         )
#     } $i $i $i $i $i]
# }

#             # ((uut.m1.memory_regfile[%d] & 32'hfe00707f) == 32'h40000033) |  
#             # ((uut.m1.memory_regfile[%d] & 32'hfe00707f) == 32'h00004033) |  
#             # ((uut.m1.memory_regfile[%d] & 32'hfe00707f) == 32'h00006033) |  
#             # ((uut.m1.memory_regfile[%d] & 32'hfe00707f) == 32'h00007033)    


#             # ((ft_memory[%d] & 32'hfe00707f) == 32'h40000033) | 
#             # ((ft_memory[%d] & 32'hfe00707f) == 32'h00004033) | 
#             # ((ft_memory[%d] & 32'hfe00707f) == 32'h00006033) |  
#             # ((ft_memory[%d] & 32'hfe00707f) == 32'h00007033)    


# for {set i 0} {$i < $MEMSIZE} {incr i} {
#     assume -reset [format {
#         (
#             ((ft_memory[%d] & 32'hfe00707f) == 32'h00000033) 

#         )
#     } $i $i $i $i $i]
# }




# set regfile_size 32
# for {set i 0} {$i < $regfile_size} {incr i} {
#     assume -reset [format {ft_CPU.RegisterBank[%d] == 32'h00000000} $i]
# }

# for {set i 1} {$i < $regfile_size} {incr i} {
#     assume -reset [format {uut.m0.m0.base_regfile[%d] == 32'h00000000} $i]
# }

prove -all
