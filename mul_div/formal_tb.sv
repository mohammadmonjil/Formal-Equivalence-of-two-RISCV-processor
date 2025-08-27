
`define FORMAL

module formal_tb(
    input clk,
    input resetn
    );
    
    localparam MEMSIZE = 32;
    
    //femto

	wire rst;	
	assign rst = !resetn;
	

	   

//-------------------------------------------------------------------------------------//
   wire          mem_i_rd_w;
   wire          mem_i_flush_w;
   wire          mem_i_invalidate_w;
   wire [ 31:0]  mem_i_pc_w;
   wire [ 31:0]  mem_d_addr_w;
   wire [ 31:0]  mem_d_data_wr_w;
   wire          mem_d_rd_w;
   wire [  3:0]  mem_d_wr_w;
   wire          mem_d_cacheable_w;
   wire [ 10:0]  mem_d_req_tag_w;
   wire          mem_d_invalidate_w;
   wire          mem_d_writeback_w;
   wire          mem_d_flush_w;
   wire          mem_i_accept_w;
   wire          mem_i_valid_w;
   wire          mem_i_error_w;
   wire [ 31:0]  mem_i_inst_w;
   wire [ 31:0]  mem_d_data_rd_w;
   wire          mem_d_accept_w;
   wire          mem_d_ack_w;
   wire          mem_d_error_w;
   wire [ 10:0]  mem_d_resp_tag_w;
   
   
   wire          pc_inst_done;
   wire          pc_inst_start;
   wire [ 31:0]  pc_pc;
   riscv_core
   pc_CPU
   //-----------------------------------------------------------------
   // Ports
   //-----------------------------------------------------------------
   (
       // Inputs
        .clk_i(clk)
       ,.rst_i(rst)
       ,.mem_d_data_rd_i(mem_d_data_rd_w)
       ,.mem_d_accept_i(mem_d_accept_w)
       ,.mem_d_ack_i(mem_d_ack_w)
       ,.mem_d_error_i(mem_d_error_w)
       ,.mem_d_resp_tag_i(mem_d_resp_tag_w)
       ,.mem_i_accept_i(mem_i_accept_w)
       ,.mem_i_valid_i(mem_i_valid_w)
       ,.mem_i_error_i(mem_i_error_w)
       ,.mem_i_inst_i(mem_i_inst_w)
    //    ,.mem_i_inst_i(32'h02c5d533)
       
       ,.intr_i(1'b0)
       ,.reset_vector_i(32'h00000000)
       ,.cpu_id_i('b0)
   
       // Outputs
       ,.mem_d_addr_o(mem_d_addr_w)
       ,.mem_d_data_wr_o(mem_d_data_wr_w)
       ,.mem_d_rd_o(mem_d_rd_w)
       ,.mem_d_wr_o(mem_d_wr_w)
       ,.mem_d_cacheable_o(mem_d_cacheable_w)
       ,.mem_d_req_tag_o(mem_d_req_tag_w)
       ,.mem_d_invalidate_o(mem_d_invalidate_w)
       ,.mem_d_writeback_o(mem_d_writeback_w)
       ,.mem_d_flush_o(mem_d_flush_w)
       ,.mem_i_rd_o(mem_i_rd_w)
       ,.mem_i_flush_o(mem_i_flush_w)
       ,.mem_i_invalidate_o(mem_i_invalidate_w)
       ,.mem_i_pc_o(mem_i_pc_w)
       `ifdef FORMAL

       ,.inst_start(pc_inst_start)
       `endif
   );
    
    tcm_mem
    u_mem
    (
        // Inputs
         .clk_i(clk)
        ,.rst_i(rst)
        ,.mem_i_rd_i(mem_i_rd_w)
        ,.mem_i_flush_i(mem_i_flush_w)
        ,.mem_i_invalidate_i(mem_i_invalidate_w)
        ,.mem_i_pc_i(mem_i_pc_w)
        ,.mem_d_addr_i(mem_d_addr_w)
        ,.mem_d_data_wr_i(mem_d_data_wr_w)
        ,.mem_d_rd_i(mem_d_rd_w)
        ,.mem_d_wr_i(mem_d_wr_w)
        ,.mem_d_cacheable_i(mem_d_cacheable_w)
        ,.mem_d_req_tag_i(mem_d_req_tag_w)
        ,.mem_d_invalidate_i(mem_d_invalidate_w)
        ,.mem_d_writeback_i(mem_d_writeback_w)
        ,.mem_d_flush_i(mem_d_flush_w)
    
        // Outputs
        ,.mem_i_accept_o(mem_i_accept_w)
        ,.mem_i_valid_o(mem_i_valid_w)
        ,.mem_i_error_o(mem_i_error_w)
        ,.mem_i_inst_o(mem_i_inst_w)
        ,.mem_d_data_rd_o(mem_d_data_rd_w)
        ,.mem_d_accept_o(mem_d_accept_w)
        ,.mem_d_ack_o(mem_d_ack_w)
        ,.mem_d_error_o(mem_d_error_w)
        ,.mem_d_resp_tag_o(mem_d_resp_tag_w)
    );
    
    
    reg [retire_width-1:0] pc_retired;
    
    always @(posedge clk or posedge rst)
    if (rst)
        pc_retired <= 0;
    else if (pc_inst_done)
        pc_retired <= pc_retired + 1;
    
    reg [31:0] pc_reg[32];

    genvar j;
    generate

        for (j = 0; j<32; j = j +1) begin
            
            if (j == 0) assign pc_reg[j] = 32'd0;
            else assign pc_reg[j] = pc_CPU.reg_file[j];
        end
    endgenerate
    
//aux code

    localparam int retire_width = 64;
    
    monitor #(.MEMSIZE(MEMSIZE)) u_monitor (
         .clk(clk)
        ,.rst(rst)
        ,.pc_reg(pc_reg)
        ,.pc_mem(u_mem.u_ram.ram)
        ,.pc_pc(pc_pc)
        ,.pc_inst_start(pc_inst_start)
        ,.inst(pc_CPU.opcode_w)
        ,.mul_div_ready_o(pc_CPU.muldiv_ready_w)
        ,.mul_div_valid_i(pc_CPU.opcode_valid_w)
        ,.mul_div_operand_ra_i(pc_CPU.rs1_val_w)
        ,.mul_div_operand_rb_i(pc_CPU.rs2_val_w)
        ,.mul_div_result_o(pc_CPU.muldiv_result_w)
    );

endmodule

module monitor #(
    parameter MEMSIZE = 32
)(
    input  logic        clk,
    input  logic        rst,
    input  logic [31:0] pc_reg[0:31],
    input  logic [31:0] pc_mem[0:MEMSIZE-1],
    input  logic [31:0] pc_pc,
    input  logic        pc_inst_start,
    input  logic [31:0] inst,
    input  logic        mul_div_ready_o,
    input  logic        mul_div_valid_i,
    input  logic [31:0] mul_div_operand_ra_i,
    input  logic [31:0] mul_div_operand_rb_i,
    input  logic [31:0] mul_div_result_o
);
    
    function automatic int clog2(input int value);
        int res = 0;
        for (int v = value - 1; v > 0; v >>= 1) res++;
        return res;
    endfunction

    localparam ADDR_WIDTH = clog2(MEMSIZE);
    localparam logic [31:0] INT_MIN = 32'h8000_0000;
    localparam logic [31:0] ALL1    = 32'hFFFF_FFFF;

    logic [ADDR_WIDTH-1:0] pc_word_addr;
    logic                  pc_bounds;
    logic [31:0]           pc_instr;

    assign pc_word_addr = pc_pc[ADDR_WIDTH+1:2]; // divide by 4 (drop 2 LSBs)
    assign pc_in_bounds = (pc_pc[31:ADDR_WIDTH+2] == 0); // upper bits must be 0
    // assign pc_instr = pc_in_bounds ? pc_mem[pc_word_addr] : 32'hDEADBEEF;
    assign pc_instr = inst;

    function automatic logic is_muldivrem(input logic [31:0] instr);
        logic [6:0]  opcode;
        logic [6:0]  funct7;

        opcode = instr[6:0];
        funct7 = instr[31:25];

        // RV32M extension instructions are R-type with opcode = 0110011 and funct7 = 0000001
        if ((opcode == 7'b0110011) && (funct7 == 7'b0000001))
            is_muldivrem = 1'b1;
        else
            is_muldivrem = 1'b0;
    endfunction

    function automatic logic [4:0] get_rs1(input logic [31:0] instr);
        return instr[19:15];
    endfunction

    // Extract rs2 field (bits 24:20)
    function automatic logic [4:0] get_rs2(input logic [31:0] instr);
        return instr[24:20];
    endfunction

    // Extract rd field (bits 11:7)
    function automatic logic [4:0] get_rd(input logic [31:0] instr);
        return instr[11:7];
    endfunction


    // rs1, rs2 gets to the operand of the multiplier block if the instruction is mul/div/rem
   
    property source_reg_values_reach_mul_div_inputs;
        logic [31:0] rs1_val, rs2_val;

        @(posedge clk) disable iff (rst)
            (pc_inst_start && is_muldivrem(pc_instr),
                rs1_val = pc_reg[get_rs1(pc_instr)], rs2_val = pc_reg[get_rs2(pc_instr)])
            |-> mul_div_valid_i && (mul_div_operand_ra_i== rs1_val) && (mul_div_operand_rb_i == rs2_val) ;
    endproperty

    assert property (source_reg_values_reach_mul_div_inputs);

    property result_of_mul_div_gets_written_to_destination_reg;
        logic [5:0] rd_addr;
        logic [31:0] mul_div_result;

        @(posedge clk) disable iff (rst)
            (pc_inst_start && is_muldivrem(pc_instr), rd_addr = get_rd(pc_instr))
            ##1 !mul_div_ready_o[*1:$]##1 (mul_div_ready_o, mul_div_result = mul_div_result_o) 
            ##1 !pc_inst_start[*1:$]##1 pc_inst_start
            |-> ( (rd_addr == 5'd0) ? (pc_reg[rd_addr] == 32'd0) : pc_reg[rd_addr] == mul_div_result) ;
    endproperty

    assert property (result_of_mul_div_gets_written_to_destination_reg);

endmodule
