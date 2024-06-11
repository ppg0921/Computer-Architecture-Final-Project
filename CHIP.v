//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//
module CHIP #(                                                                                  //
    parameter BIT_W = 32                                                                        //
)(                                                                                              //
    // clock                                                                                    //
        input               i_clk,                                                              //
        input               i_rst_n,                                                            //
    // instruction memory                                                                       //
        input  [BIT_W-1:0]  i_IMEM_data,                                                        //
        output [BIT_W-1:0]  o_IMEM_addr,                                                        //
        output              o_IMEM_cen,                                                         //
    // data memory                                                                              //
        input               i_DMEM_stall,                                                       //
        input  [BIT_W-1:0]  i_DMEM_rdata,                                                       //
        output              o_DMEM_cen,                                                         //
        output              o_DMEM_wen,                                                         //
        output [BIT_W-1:0]  o_DMEM_addr,                                                        //
        output [BIT_W-1:0]  o_DMEM_wdata,                                                       //
    // finnish procedure                                                                        //
        output              o_finish,                                                           //
    // cache                                                                                    //
        input               i_cache_finish,                                                     //
        output              o_proc_finish                                                       //
);                                                                                              //
//----------------------------- DO NOT MODIFY THE I/O INTERFACE!! ------------------------------//

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any declaration
    // FSM parameters:
    parameter S_IFID               = 2'd0;
    parameter S_MULTI_CYCLE_OP     = 2'd1;
    parameter S_ONE_CYCLE_OP       = 2'd2;
    parameter S_FINISH             = 2'd3;

    // ALU instruction parameter
    parameter INST_AND = 4'b0000; // and
    parameter INST_OR  = 4'b0001; // or
    parameter INST_ADD = 4'b0010; // add, lw, sw, 
    parameter INST_SUB = 4'b0110; // sub, beq
    parameter INST_SLT = 4'b0111; // 
    parameter INST_SLL = 4'b1000; 

    parameter INST_SRA = 4'b1001;
    parameter INST_XOR = 4'b1010;
    parameter INST_SLT_N = 4'b1011;
    parameter INST_SUB_N = 4'b1100;
    parameter INST_MUL = 4'b1101;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
        reg [BIT_W-1:0] PC, next_PC;
        wire mem_cen, mem_wen;
        wire [BIT_W-1:0] mem_addr, mem_wdata, mem_rdata;
        wire mem_stall;

        // FSM states
        reg [1:0] state, state_nxt; 

        // Control Signals
        reg Branch, MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite;
        reg [1:0] ALUOp;

        reg [63:0] ImmGen;
        reg [3:0] ALUctrl;

        // Other signals
        reg [BIT_W-1:0] reg_rdata1, reg_rdata2;
        
        reg ALU_zero;
        reg [BIT_W-1:0]ALU_result_one, ALU_result_multi;
        reg mul_valid, mul_valid_nxt;
        reg mul_done;

        // load input
        // reg cache_finish, cache_finish_nxt;
        // reg [BIT_W-1:0] IMEM_data, IMEM_data_nxt;
        // reg DMEM_stall, DMEM_stall_nxt;
        // reg [BIT_W-1:0] DMEM_rdata, DMEM_rdata_nxt;


// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment
    assign o_DMEM_wdata = reg_rdata2;
    assign o_DMEM_addr = (ALUctrl == INST_MUL) ? ALU_result_multi : ALU_result_one 

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: Reg_file wire connection
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (RegWrite),
        .rs1    (i_IMEM_data[19:15]),                
        .rs2    (i_IMEM_data[24:20]),                
        .rd     (i_IMEM_data[11:7]),                 
        .wdata  (i_IMEM_data[6:0] == 7'b1101111 || i_IMEM_data[6:0] == 7'b1100111? PC + 4 :(MemtoReg ? i_DMEM_rdata : ALU_result)),             
        .rdata1 (reg_rdata1),           
        .rdata2 (reg_rdata2)
    );

    MULDIV_unit ALU0(
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n), 
        .i_valid(mul_valid_nxt),
        .i_A    (reg_rdata1),
        .i_B    (ALUSrc ? ImmGen : reg_rdata2), 
        .o_data (ALU_result_multi), 
        .o_done (mul_done)
    );


// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // Todo: any combinational/sequential circuit
    always @(*) begin
        if(i_IMEM_data[6:0] === 7'b1100111)
            next_PC = ALU_result_one;
        else
            next_PC = (Branch === 1)? PC+(ImmGen<<1) : PC+4;
    end

    // FSM
    always @(*) begin
        case(state)
        S_IFID:           state_nxt = ( i_IMEM_data[6:0] == 7'b1110011 ) ? S_FINISH : ( (i_IMEM_data[6:0] == 7'b1110011 && i_IMEM_data[25] == 1'b0) ? S_MULTI_CYCLE_OP : S_ONE_CYCLE_OP);
        S_MULTI_CYCLE_OP: state_nxt = mul_done ? S_IFID : state_nxt;
        S_ONE_CYCLE_OP:   state_nxt = i_DMEM_stall   ? S_IFID : state_nxt;
        S_FINISH: state_nxt = state;
        default : state_nxt = state;
        endcase
    end
    

    // Control Signals
    always @(*) begin
        Branch = (i_IMEM_data[6] === 1 && (ALU_zero || i_IMEM_data[2] === 1))? 1:0;
        MemRead = (i_IMEM_data[6:4] === 3'b0)? 1:0;
        MemtoReg = (i_IMEM_data[6:4] === 3'b0)? 1:0;
        MemWrite = (i_IMEM_data[6:4] === 3'b010)? 1:0;
        ALUSrc = (i_IMEM_data[6:5] === 2'b00 || i_IMEM_data[6:4] === 3'b010)? 1:0;
        RegWrite = (i_IMEM_data[5] === 0 || (i_IMEM_data[2] === 1 && (i_IMEM_data[4] & i_IMEM_data[3] === 0)) || ((i_IMEM_data[6] & i_IMEM_data[2] === 0) && (i_IMEM_data[4] | i_IMEM_data[3] === 1)))? 1:0;
        if(i_IMEM_data[6] === 0 && i_IMEM_data[4:2] === 3'b0)  
            ALUOp = 2'b00;
        else if(i_IMEM_data[6:2] === 5'b11000)
            ALUOp = 2'b01;
        else
            ALUOp = 2'b10;
    end

    // ALU control
    always @(*) begin
        case(ALUOp)
            2'b00: ALUctrl = INST_ADD;
            2'b01: case(i_IMEM_data[14:12])
                3'b000: ALUctrl = INST_SUB;
                3'b101: ALUctrl = INST_SLT_N;
                3'b100: ALUctrl = INST_SLT;
                3'b001: ALUctrl = INST_SUB_N;
                default: ALUctrl = INST_ADD;
            endcase
            2'b10: case(i_IMEM_data[6:0])
                7'b0110011: case(i_IMEM_data[14:12])
                    3'b000: ALUctrl = i_IMEM_data[30] ? INST_SUB : (i_IMEM_data[25] ? INST_MUL : INST_ADD) ;
                    3'b111: ALUctrl = INST_AND;
                    3'b111: ALUctrl = INST_XOR;
                    default: ALUctrl = INST_ADD;
                endcase
                7'b0010011: case(i_IMEM_data[14:12])
                    3'b000: ALUctrl = INST_ADD;
                    3'b001: ALUctrl = INST_SLL;
                    3'b010: ALUctrl = INST_SLT;
                    3'b101: ALUctrl = INST_SRA;
                    default: ALUctrl = INST_ADD;
                endcase
                7'b0010111: ALUctrl = INST_ADD; // auipc, TBD
                7'b1101111: ALUctrl = INST_ADD; // jal, TBD
                7'b1100111: ALUctrl = INST_ADD; // jalr, TBD
                default: ALUctrl = INST_ADD;
            endcase
            default: ALUctrl = INST_ADD;
        endcase
    end


    // ALU
    always @(*) begin
        ALU_zero = 1'b0;
        case(ALUctrl)
            INST_ADD: begin
                shreg_tmp = i_A + i_B;
                if(i_A[31] == 0 && i_B[31] == 0 && shreg_tmp[31] == 1) ALU_shreg = 64'h000000007fffffff;
                else if(i_A[31] == 1 && i_B[31] == 1 && shreg_tmp[31] == 0) ALU_shreg = 64'h0000000080000000;
                else ALU_shreg = {32'd0, shreg_tmp};
            end
            INST_SUB: begin
                shreg_tmp = i_A - i_B;
                if(i_A[31] == 0 && i_B[31] == 1 && shreg_tmp[31] == 1) ALU_shreg = 64'h000000007fffffff;
                else if(i_A[31] == 1 && i_B[31] == 0 && shreg_tmp[31] == 0) ALU_shreg = 64'h0000000080000000;
                else ALU_shreg = {32'd0, shreg_tmp};
                if(ALU_shreg == 64'd0) o_zero = 1'b1;
            end
            INST_SUB_N: begin
                shreg_tmp = i_A - i_B;
                if(i_A[31] == 0 && i_B[31] == 1 && shreg_tmp[31] == 1) ALU_shreg = 64'h000000007fffffff;
                else if(i_A[31] == 1 && i_B[31] == 0 && shreg_tmp[31] == 0) ALU_shreg = 64'h0000000080000000;
                else ALU_shreg = {32'd0, shreg_tmp};
                if(ALU_shreg != 64'd0) o_zero = 1'b1;
            end
            INST_AND: ALU_shreg = {32'd0, i_A & i_B};
            INST_OR:  ALU_shreg = {32'd0, i_A | i_B};
            INST_XOR: ALU_shreg = {32'd0, i_A ^ i_B};
            INST_SLT: begin
                if(i_A[31] == 0 && i_B[31] == 1) ALU_shreg = 64'd0;
                else if(i_A[31] == 1 && i_B[31] == 0) ALU_shreg = {63'd0, 1'd1};
                else begin
                    shreg_tmp = i_A - i_B;
                    if( shreg_tmp[31] == 1 ) ALU_shreg = {63'd0, 1'd1};
                    else ALU_shreg = 64'd0;
                end
                o_zero = ALU_shreg[0];
            end
            INST_SLT_N: begin
                if(i_A[31] == 0 && i_B[31] == 1) ALU_shreg = 64'd0;
                else if(i_A[31] == 1 && i_B[31] == 0) ALU_shreg = {63'd0, 1'd1};
                else begin
                    shreg_tmp = i_A - i_B;
                    if( shreg_tmp[31] == 1 ) ALU_shreg = {63'd0, 1'd1};
                    else ALU_shreg = 64'd0;
                end
                o_zero = !ALU_shreg[0];
            end
            INST_SLL: begin
                shreg_tmp = i_A << i_B;
                ALU_shreg = {32'd0, shreg_tmp};
            end
            INST_SRA: begin
                shreg_tmp = i_A >> i_B;
                ALU_shreg = {32'd0, shreg_tmp};
            end
            INST_MUL: begin
                mul_valid_nxt = 1'b1;
            end
            // mul: done in the MULDIV unit.
            
            default: begin
                ALU_shreg = 64'd0; 
                shreg_tmp = 32'd0;
                mul_valid_nxt = 1'b0;
            end
        endcase
    end

    // Imm Gen


    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            cnt <= 5'd0;
            mul_valid <= 1'b0;
        end
        else begin
            PC <= next_PC;
            cnt <= cnt_nxt;
            mul_valid <= mul_valid_nxt;
        end
    end
endmodule

// DO NOT MODIFY REGISTER FILE
module Reg_file(i_clk, i_rst_n, wen, rs1, rs2, rd, wdata, rdata1, rdata2);
   
    parameter BITS = 32;
    parameter word_depth = 32;
    parameter addr_width = 5; // 2^addr_width >= word_depth
    
    input i_clk, i_rst_n, wen; // wen: 0:read | 1:write
    input [BITS-1:0] wdata;
    input [addr_width-1:0] rs1, rs2, rd;

    output [BITS-1:0] rdata1, rdata2;

    reg [BITS-1:0] mem [0:word_depth-1];
    reg [BITS-1:0] mem_nxt [0:word_depth-1];

    integer i;

    assign rdata1 = mem[rs1];
    assign rdata2 = mem[rs2];

    always @(*) begin
        for (i=0; i<word_depth; i=i+1)
            mem_nxt[i] = (wen && (rd == i)) ? wdata : mem[i];
    end

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1) begin
                case(i)
                    32'd2: mem[i] <= 32'hbffffff0;
                    32'd3: mem[i] <= 32'h10008000;
                    default: mem[i] <= 32'h0;
                endcase
            end
        end
        else begin
            mem[0] <= 0;
            for (i=1; i<word_depth; i=i+1)
                mem[i] <= mem_nxt[i];
        end       
    end
endmodule

module MULDIV_unit(i_clk, i_valid, i_rst_n, i_A, i_B, o_data, o_done);
    // Todo: HW2

    // parameter
    parameter DATA_W = 32;
    parameter S_WORK = 1'b1;
    parameter S_IDLE = 1'b0;

    // input and output
    input                       i_clk;   // clock
    input                       i_valid;
    input                       i_rst_n; // reset

    input [DATA_W - 1 : 0]      i_A;     // input operand A
    input [DATA_W - 1 : 0]      i_B;     // input operand B

    output [2*DATA_W - 1 : 0]   o_data;  // output value
    output                     o_done;

    // Regs
    reg  [ 2*DATA_W-1: 0] shreg, shreg_nxt;
    reg  [   DATA_W-1: 0] shreg_tmp;
    reg [4:0] cnt, cnt_nxt;
    reg state, state_nxt;
    reg  [   DATA_W-1: 0] operand_a, operand_a_nxt;
    reg  [   DATA_W-1: 0] operand_b, operand_b_nxt;

    // Always Combination

    // load input
     always @(*) begin
        if (i_valid) begin
            operand_a_nxt = i_A;
            operand_b_nxt = i_B;
            // inst_nxt      = i_inst;
        end
        else begin
            operand_a_nxt = operand_a;
            operand_b_nxt = operand_b;
            // inst_nxt      = inst;
        end
    end

    // FSM
    always @(*) begin
        case(state)
            S_IDLE: state_nxt = i_valid ? S_WORK : state;
            S_WORK: state_nxt = (cnt == 5'd31) ? S_OUT : state;
        endcase
    end

    // Counter
    always @(posedge i_clk) begin
        cnt_nxt = cnt + 5'd1;
        else cnt_nxt = 5'd0;
    end

    // Output
    always @(*) begin
        if(state == S_IDLE) shreg_nxt = 64'b0;
        else if (cnt == 0)begin 
            if(operand_a[0] == 1) shreg_nxt = {1'b0, operand_b[31:0], operand_a[31:1]};
            else shreg_nxt = {33'b0, operand_a[31:1]};
        end
        else if(shreg[0] == 1) shreg_nxt = {1'b0, shreg[63:1]} + {1'b0, operand_b, 31'b0};
        else shreg_nxt = shreg >> 1;
    end

    // Sequential always block
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            state       <= S_IDLE;
            operand_a   <= 0;
            operand_b   <= 0;
            // inst        <= 0;
            shreg       <= 0;
            done        <= 0;
            cnt         <= 0;
        end
        else begin
            state       <= state_nxt;
            operand_a   <= operand_a_nxt;
            operand_b   <= operand_b_nxt;
            // inst        <= inst_nxt;
            shreg       <= shreg_nxt; // wired to o_data.
            cnt         <= cnt_nxt;
            done        <= (state == S_WORK && state_nxt == S_IDLE);
        end
    end
endmodule

module Cache#(
        parameter BIT_W = 32,
        parameter ADDR_W = 32
    )(
        input i_clk,
        input i_rst_n,
        // processor interface
            input i_proc_cen,
            input i_proc_wen,
            input [ADDR_W-1:0] i_proc_addr,
            input [BIT_W-1:0]  i_proc_wdata,
            output [BIT_W-1:0] o_proc_rdata,
            output o_proc_stall,
            input i_proc_finish,
            output o_cache_finish,
        // memory interface
            output o_mem_cen,
            output o_mem_wen,
            output [ADDR_W-1:0] o_mem_addr,
            output [BIT_W*4-1:0]  o_mem_wdata,
            input [BIT_W*4-1:0] i_mem_rdata,
            input i_mem_stall,
            output o_cache_available,
        // others
        input  [ADDR_W-1: 0] i_offset
    );

    assign o_cache_available = 0; // change this value to 1 if the cache is implemented

    //------------------------------------------//
    //          default connection              //
    assign o_mem_cen = i_proc_cen;              //
    assign o_mem_wen = i_proc_wen;              //
    assign o_mem_addr = i_proc_addr;            //
    assign o_mem_wdata = i_proc_wdata;          //
    assign o_proc_rdata = i_mem_rdata[0+:BIT_W];//
    assign o_proc_stall = i_mem_stall;          //
    //------------------------------------------//

    // Todo: BONUS

endmodule