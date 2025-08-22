
module tcm_mem
(
    // Inputs
     input           clk_i
    ,input           rst_i
    ,input           mem_i_rd_i
    ,input           mem_i_flush_i
    ,input           mem_i_invalidate_i
    ,input  [ 31:0]  mem_i_pc_i
    ,input  [ 31:0]  mem_d_addr_i
    ,input  [ 31:0]  mem_d_data_wr_i
    ,input           mem_d_rd_i
    ,input  [  3:0]  mem_d_wr_i
    ,input           mem_d_cacheable_i
    ,input  [ 10:0]  mem_d_req_tag_i
    ,input           mem_d_invalidate_i
    ,input           mem_d_writeback_i
    ,input           mem_d_flush_i

    // Outputs
    ,output          mem_i_accept_o
    ,output          mem_i_valid_o
    ,output          mem_i_error_o
    ,output [ 31:0]  mem_i_inst_o
    ,output [ 31:0]  mem_d_data_rd_o
    ,output          mem_d_accept_o
    ,output          mem_d_ack_o
    ,output          mem_d_error_o
    ,output [ 10:0]  mem_d_resp_tag_o
);

//-------------------------------------------------------------
// Dual Port RAM
//-------------------------------------------------------------
wire [31:0] data_r_w;



//-------------------------------------------------------------
// Instruction Fetch
//-------------------------------------------------------------
reg        mem_i_valid_q;

always @ (posedge clk_i )
if (rst_i)
    mem_i_valid_q <= 1'b0;
else
    mem_i_valid_q <= mem_i_rd_i;

assign mem_i_accept_o  = 1'b1;
assign mem_i_valid_o   = mem_i_valid_q;
assign mem_i_error_o   = 1'b0;

//-------------------------------------------------------------
// Data Access / Incoming external access
//-------------------------------------------------------------
reg        mem_d_accept_q;
reg        mem_d_ack_q;
reg [10:0] mem_d_tag_q;

always @ (posedge clk_i )
if (rst_i)
begin
    mem_d_ack_q    <= 1'b0;
    mem_d_tag_q    <= 11'b0;
end
else if ((mem_d_rd_i || mem_d_wr_i != 4'b0 || mem_d_flush_i || mem_d_invalidate_i || mem_d_writeback_i) && mem_d_accept_o)
begin
    mem_d_ack_q    <= 1'b1;
    mem_d_tag_q    <= mem_d_req_tag_i;
end
else
    mem_d_ack_q    <= 1'b0;

assign mem_d_ack_o          = mem_d_ack_q;
assign mem_d_resp_tag_o     = mem_d_tag_q;
assign mem_d_data_rd_o      = data_r_w;
assign mem_d_error_o        = 1'b0;

assign mem_d_accept_o       = 1'b1;

//-------------------------------------------------------------
// write: Write byte into memory
//-------------------------------------------------------------

tcm_mem_ram
u_ram
(
    // Instruction fetch
     .clk0_i(clk_i)
    ,.rst0_i(rst_i)
    ,.addr0_i(mem_i_pc_i[15:2])
    ,.data0_i(32'b0)
    ,.wr0_i(4'b0)

    // External access / Data access
    ,.clk1_i(clk_i)
    ,.rst1_i(rst_i)
    ,.addr1_i(mem_d_addr_i[15:2])
    ,.data1_i(mem_d_data_wr_i)
    ,.wr1_i(mem_d_wr_i)

    // Outputs
    ,.data0_o(mem_i_inst_o)
    ,.data1_o(data_r_w)
);

// wire           clk0_i;
// wire           rst0_i;
// wire  [ 13:0]  addr0_i;
// wire  [ 31:0]  data0_i;
// wire  [  3:0]  wr0_i;
// wire           clk1_i;
// wire           rst1_i;
// wire  [ 13:0]  addr1_i;
// wire  [ 31:0]  data1_i;
// wire  [  3:0]  wr1_i;

// // Outputs
// wire [ 31:0]  data0_o;
// wire [ 31:0]  data1_o;


// assign           clk0_i = clk_i;
// assign           rst0_i = rst_i;
// assign           addr0_i = mem_i_pc_i[15:2];
// assign           data0_i = 32'b0;
// assign           wr0_i = 4'b0;
// assign           clk1_i  = clk_i;
// assign           rst1_i= rst_i;
// assign           addr1_i = mem_d_addr_i[15:2];
// assign    data1_i = mem_d_data_wr_i;
// assign    wr1_i = mem_d_wr_i;

// // Outputs
// assign   data0_o = mem_i_inst_o;
// assign   data1_o = data_r_w;

// localparam MEMSIZE = 32;
// reg [31:0]   ram [MEMSIZE-1:0] /*verilator public*/;
// /* verilator lint_on MULTIDRIVEN */

// reg [31:0] ram_read0_q;
// reg [31:0] ram_read1_q;

// // Synchronous write
// always @ (posedge clk0_i)
// begin
//     // if (rst0_i) ;
//     // else begin
//     ram_read0_q <= ram[addr0_i];
//     if (wr0_i[0])
//         ram[addr0_i][7:0] <= data0_i[7:0];
//     if (wr0_i[1])
//         ram[addr0_i][15:8] <= data0_i[15:8];
//     if (wr0_i[2])
//         ram[addr0_i][23:16] <= data0_i[23:16];
//     if (wr0_i[3])
//         ram[addr0_i][31:24] <= data0_i[31:24];
//     // end
// end

// always @ (posedge clk1_i)
// begin
//     // if (rst1_i) ;
//     // else begin
//     ram_read1_q <= ram[addr1_i];
//     if (wr1_i[0])
//         ram[addr1_i][7:0] <= data1_i[7:0];
//     if (wr1_i[1])
//         ram[addr1_i][15:8] <= data1_i[15:8];
//     if (wr1_i[2])
//         ram[addr1_i][23:16] <= data1_i[23:16];
//     if (wr1_i[3])
//         ram[addr1_i][31:24] <= data1_i[31:24];

//     // end
// end

// assign data0_o = ram_read0_q;
// assign data1_o = ram_read1_q;



endmodule
