// Core plus memory

`timescale 1ns / 1ps

//complete package containing the rv32i_core, RAM, and IO peripherals (I2C and UART)
module rv32i_soc #(parameter CLK_FREQ_MHZ=12, PC_RESET=32'h00_00_00_00, TRAP_ADDRESS=32'h00_00_00_00, ZICSR_EXTENSION=1, MEMORY_DEPTH=81920, GPIO_COUNT = 12) ( 
    input wire i_clk,
    input wire i_rst
    //UART
    //GPIO
    );

    
    //Instruction Memory Interface
    wire[31:0] inst; 
    wire[31:0] iaddr;  
    wire i_stb_inst;
    wire o_ack_inst;
    
    //Data Memory Interface
    wire[31:0] i_wb_data_data; //data retrieved from memory
    wire[31:0] o_wb_data_data; //data to be stored to memory
    wire[31:0] wb_addr_data; //address of data memory for store/load
    wire[3:0] wb_sel_data; //byte strobe for write (1 = write the byte) {byte3,byte2,byte1,byte0}
    wire wb_we_data; //write-enable (1 = write, 0 = read) 
    wire wb_stb_data; //request for read/write access to data memory
    wire wb_ack_data; //ack by data memory (high when data to be read is ready or when write data is already written
    wire wb_cyc_data; //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
    wire wb_stall_data; //stall by data memory
    
    //Interrupts
    wire i_external_interrupt = 0; //interrupt from external source
    wire o_timer_interrupt = 0; //interrupt from CLINT
    wire o_software_interrupt = 0; //interrupt from CLINT
    
    wire pc_inst_start;
    wire [31:0] pc_pc;
    wire [31:0] pc_inst;

    wire [31:0] rs1_alu;
    wire [31:0] rs2_alu;
    wire [4:0] rs1_addr_alu;
    wire [4:0] rs2_addr_alu;

    rv32i_core #(.PC_RESET(PC_RESET), .TRAP_ADDRESS(TRAP_ADDRESS), .ZICSR_EXTENSION(ZICSR_EXTENSION)) m0( //main RV32I core
        .i_clk(i_clk),
        .i_rst_n(!i_rst),
        //Instruction Memory Interface
        .i_inst(inst), //32-bit instruction
        .o_iaddr(iaddr), //address of instruction 
        .o_stb_inst(i_stb_inst), //request for read access to instruction memory
        .i_ack_inst(o_ack_inst),  //ack (high if new instruction is ready)
        //Data Memory Interface
        .o_wb_cyc_data(wb_cyc_data), //bus cycle active (1 = normal operation, 0 = all ongoing transaction are to be cancelled)
        .o_wb_stb_data(wb_stb_data), //request for read/write access to data memory
        .o_wb_we_data(wb_we_data), //write-enable (1 = write, 0 = read)
        .o_wb_addr_data(wb_addr_data), //address of data memory for store/load
        .o_wb_data_data(o_wb_data_data), //data to be stored to memory
        .o_wb_sel_data(wb_sel_data), //byte strobe for write (1 = write the byte) {byte3,byte2,byte1,byte0}
        .i_wb_ack_data(wb_ack_data), //ack by data memory (high when read data is ready or when write data is already written)
        .i_wb_stall_data(wb_stall_data), //stall by data memory
        .i_wb_data_data(i_wb_data_data), //data retrieved from memory
        //Interrupts
        .i_external_interrupt(i_external_interrupt), //interrupt from external source
        .i_software_interrupt(o_software_interrupt), //interrupt from software (inter-processor interrupt)
        .i_timer_interrupt(o_timer_interrupt) //interrupt from timer
        
        `ifdef FORMAL
            ,.Current_PC(pc_pc)
            ,.Current_inst(pc_inst)
            ,.inst_start(pc_inst_start)
            ,.rs1_alu(rs1_alu)
            ,.rs2_alu(rs2_alu)
            ,.rs1_addr_alu(rs1_addr_alu)
            ,.rs2_addr_alu(rs2_addr_alu)
        `endif
     );
        

    // DEVICE 0
     main_memory #(.MEMORY_DEPTH(MEMORY_DEPTH)) m1( //Instruction and Data memory (combined memory) 
        .i_clk(i_clk),
        // Instruction Memory
        .i_inst_addr(iaddr[$clog2(MEMORY_DEPTH)-1:0]),
        .o_inst_out(inst),
        .i_stb_inst(i_stb_inst), 
        .o_ack_inst(o_ack_inst), 
        // Data Memory
        .i_wb_cyc(wb_cyc_data),
        .i_wb_stb(wb_stb_data),
        .i_wb_we(wb_we_data),
        .i_wb_addr(wb_addr_data[$clog2(MEMORY_DEPTH)-1:0]),
        .i_wb_data(o_wb_data_data),
        .i_wb_sel(wb_sel_data),
        .o_wb_ack(wb_ack_data),
        .o_wb_stall(wb_stall_data),
        .o_wb_data(i_wb_data_data)
    );


endmodule


module main_memory #(parameter MEMORY_DEPTH=1024) ( //Instruction and Data memory (combined memory)
    input wire i_clk,
    // Instruction Memory
    input wire[$clog2(MEMORY_DEPTH)-1:0] i_inst_addr,
    output reg[31:0] o_inst_out,
    input wire i_stb_inst, // request for instruction
    output reg o_ack_inst, //ack (high if new instruction is now on the bus)
    // Data Memory
    input wire i_wb_cyc,
    input wire i_wb_stb,
    input wire i_wb_we,
    input wire[$clog2(MEMORY_DEPTH)-1:0] i_wb_addr,
    input wire[31:0] i_wb_data,
    input wire[3:0] i_wb_sel,
    output reg o_wb_ack,
    output wire o_wb_stall,
    output reg[31:0] o_wb_data
);
    reg[31:0] memory_regfile[MEMORY_DEPTH/4 - 1:0];

    assign o_wb_stall = 0; // never stall

    initial begin //initialize memory to zero
        o_ack_inst <= 0;
        o_wb_ack <= 0;
        o_inst_out <= 0;
    end
	
	integer i;
	initial begin


	    // Clear memory

	    for (i = 0; i < MEMORY_DEPTH/4 - 1; i = i + 1)
		memory_regfile[i] = 32'h00000000;

	    // Load custom instructions
	    memory_regfile[0] = 32'h00208263; // li     x1,1020
	    memory_regfile[1] = 32'h0000a023; // sw     x0,0(x1)
	    memory_regfile[2] = 32'h0000a103; // lw     x2,0(x1)
	    memory_regfile[3] = 32'h00110113; // addi   x2,x2,1
	    memory_regfile[4] = 32'h0020a023; // sw     x2,0(x1)
	    memory_regfile[5] = 32'hff5ff06f; // ebreak (or end of program)
	end
    
    //reading must be registered to be inferred as block ram
    always @(posedge i_clk) begin 
        o_ack_inst <= i_stb_inst; //go high next cycle after receiving request (data o_inst_out is also sent at next cycle)
        o_wb_ack <= i_wb_stb && i_wb_cyc;
        o_inst_out <= memory_regfile[{i_inst_addr>>2}]; //read instruction 
        // o_wb_data <= memory_regfile[i_wb_addr[$clog2(MEMORY_DEPTH)-1:2]]; //read data    
        o_wb_data <= memory_regfile[i_wb_addr[6:2]]; //read data  
    end

    // write data
    always @(posedge i_clk) begin
        if(i_wb_we && i_wb_stb && i_wb_cyc) begin
            if(i_wb_sel[0]) memory_regfile[i_wb_addr[$clog2(MEMORY_DEPTH)-1:2]][7:0] <= i_wb_data[7:0]; 
            if(i_wb_sel[1]) memory_regfile[i_wb_addr[$clog2(MEMORY_DEPTH)-1:2]][15:8] <= i_wb_data[15:8];
            if(i_wb_sel[2]) memory_regfile[i_wb_addr[$clog2(MEMORY_DEPTH)-1:2]][23:16] <= i_wb_data[23:16];
            if(i_wb_sel[3]) memory_regfile[i_wb_addr[$clog2(MEMORY_DEPTH)-1:2]][31:24] <= i_wb_data[31:24];
        end      
        
    end
    
endmodule


