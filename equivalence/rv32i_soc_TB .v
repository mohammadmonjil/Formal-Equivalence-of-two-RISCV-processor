`timescale 1ns / 1ns
`include "rv32i_header.vh"

module rv32i_soc_TB;
    parameter MEMORY="memory.mem";
    parameter ZICSR_EXTENSION = 1;
    /******************************* MODIFY ****************************************/
    localparam MEMORY_DEPTH = 81920, //number of memory bytes
               DATA_START_ADDR = 32'h1004; //starting address of data memory to be displayed
    /*******************************************************************************/
   
    reg clk,rst_n;
    reg temp;
    integer i,j;          
    
    
    rv32i_soc #(.PC_RESET(32'h00_00_00_00), .MEMORY_DEPTH(MEMORY_DEPTH), .CLK_FREQ_MHZ(100), .TRAP_ADDRESS(32'h00000004), .ZICSR_EXTENSION(ZICSR_EXTENSION)) uut (
        .i_clk(clk),
        .i_rst(!rst_n)
        );
    
    always #5 clk=!clk; //100MHz clock
    
    initial begin //2nd reset to test resetting while core is executing instruction
        clk = 0;
        #200;
        rst_n = 0;
        #500;
        rst_n = 1;
    end  
        
	initial begin
		#100_000; //simulation time limit
		`ifdef LONGER_SIM_LIMIT
		#25_000_000;
		`endif
		$stop;
	end
endmodule
