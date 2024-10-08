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
    parameter S_IDLE               = 2'd0;
    parameter S_MULTI_CYCLE_OP     = 2'd1;
    parameter S_ONE_CYCLE_OP       = 2'd2;
    parameter S_FINISH             = 2'd3;

    // ALU instruction parameter
    parameter INST_AND = 4'b0000; 
    parameter INST_OR  = 4'b0001; 
    parameter INST_ADD = 4'b0010; 
    parameter INST_SUB = 4'b0110; 
    parameter INST_SLT = 4'b0111;
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

        reg signed [63:0] ImmGen;
        reg [3:0] ALUctrl;

        // Other signals
        wire [BIT_W-1:0] reg_rdata1, reg_rdata2;
        
        reg ALU_zero;
        wire [BIT_W-1:0] ALU_result_one;
        wire [BIT_W-1:0] ALU_result_multi;
        reg mul_valid, mul_valid_nxt;
        wire mul_done;

        wire [BIT_W-1: 0]i_A, i_B;
        reg  [BIT_W-1: 0]shreg_tmp;
        reg  [2*BIT_W-1: 0] ALU_shreg;
        reg [BIT_W-1:0] reg_wdata;
        reg [BIT_W-1:0] instruction, instruction_nxt;
        reg newPC, newPC_nxt;
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
    assign o_DMEM_addr = (ALUctrl == INST_MUL) ? ALU_result_multi : ALU_result_one;
    assign i_B = (ALUSrc) ? ImmGen[BIT_W-1:0] : reg_rdata2;
    assign i_A = (instruction[6:0] === 7'b0010111) ? PC : reg_rdata1;
    assign o_finish = (state == S_FINISH);
    assign o_IMEM_addr = next_PC;
    assign o_IMEM_cen = (state != S_FINISH);
    assign o_DMEM_cen = (MemWrite | MemRead);
    assign o_DMEM_wen = MemWrite;
    assign ALU_result_one = ALU_shreg;
    assign o_proc_finish = (instruction[6:0] == 7'b1110011);
    

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: Reg_file wire connection
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (RegWrite),
        .rs1    (instruction[19:15]),                
        .rs2    (instruction[24:20]),                
        .rd     (instruction[11:7]),                 
        .wdata  (reg_wdata),             
        .rdata1 (reg_rdata1),           
        .rdata2 (reg_rdata2)
    );

    MULDIV_unit ALU0(
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n), 
        .i_valid(mul_valid_nxt && newPC),
        .i_A    (reg_rdata1),
        .i_B    ((ALUSrc) ? ImmGen[31:0] : reg_rdata2), 
        .o_data (ALU_result_multi), 
        .o_done (mul_done)
    );


// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // Todo: any combinational/sequential circuit

    // PC control
    always @(*) begin
        if(instruction == 64'b0)
            next_PC = 32'h00010000;
        else if (i_DMEM_stall || (state == S_MULTI_CYCLE_OP && !mul_done))
            next_PC = PC;
        else if(instruction[6:0] === 7'b1100111) begin  // jalr
            next_PC = ALU_result_one;
        end
        else
            next_PC = (Branch === 1)? PC+(ImmGen<<1) : PC+4;
        newPC_nxt = (next_PC != PC);
    end

    // IF (instruction fetch)
    always @(*) begin
        instruction_nxt = i_IMEM_data;
        if(instruction[6:0] === 7'b1110011)
            instruction_nxt = instruction;
    end

    // reg_wdata (write back of register file)
    always @(*) begin
        if(instruction[6:0] == 7'b1101111 || instruction[6:0] == 7'b1100111) begin  // jal, jalr
            reg_wdata = PC+4;
        end
        else begin
            if(MemtoReg)    reg_wdata = i_DMEM_rdata;
            else begin
                if(ALUctrl == INST_MUL)
                    reg_wdata = ALU_result_multi;
                else
                    reg_wdata = ALU_result_one;
            end
        end
    end

    // FSM
    // to determine state_nxt, need to use instruction_nxt/ i.e. i_IMEM_data
    always @(*) begin
        state_nxt = state;
        if(!i_DMEM_stall) begin
            if(instruction_nxt[6:0] == 7'b1110011 && i_cache_finish) state_nxt = S_FINISH;
            else if (!(state == S_MULTI_CYCLE_OP && !mul_done))
                state_nxt = (instruction_nxt[6:0] == 7'b0110011 && instruction_nxt[25] == 1'b1) ? S_MULTI_CYCLE_OP : S_ONE_CYCLE_OP;
        end
    end
    
    // ImmGen
    always @(*) begin
        case(instruction[6:0])
            7'b0110011: ImmGen = 64'b0;     // R type
            7'b0010011, 7'b1100111, 7'b0000011, 7'b1110011: begin       // I type
                if(instruction[14:12] == 3'b001 || instruction[14:12] == 3'b101)    // slli, srai
                    ImmGen = {{58{instruction[25]}}, instruction[25:20]};
                else
                    ImmGen = {{52{instruction[31]}}, instruction[31:20]};      
            end
            7'b0100011: ImmGen = {{52{instruction[31]}}, instruction[31:25], instruction[11:7]};       // S type
            7'b1100011: ImmGen = {{52{instruction[31]}}, instruction[31], instruction[7], instruction[30:25], instruction[11:8]};      // B type
            7'b0010111: ImmGen = {{32{instruction[31]}}, instruction[31:12], {12'b0}};     // U type
            7'b1101111: ImmGen = {{44{instruction[31]}}, instruction[31], instruction[19:12], instruction[20], instruction[30:21]};    // J type
            default: ImmGen = 64'b0;
        endcase
    end

    // Control Signals
    always @(*) begin
        Branch = (instruction[6] === 1 && (ALU_zero || instruction[2] === 1))? 1:0;
        MemRead = (instruction[6:4] === 3'b0 && instruction !== 64'b0)? 1:0;
        MemtoReg = (instruction[6:4] === 3'b0)? 1:0;
        MemWrite = (instruction[6:4] === 3'b010)? 1:0;
        ALUSrc = (instruction[6:5] === 2'b00 || instruction[6:4] === 3'b010 || instruction[6:0] === 7'b1100111)? 1:0;
        RegWrite = (instruction[6:0] === 7'b1101111 || instruction[6:0] === 7'b1100111 || instruction[6:0] === 7'b0010111 || instruction[6:0] === 7'b0110011 || instruction[6:0] === 7'b0010011 || instruction[6:0] === 7'b0000011 || instruction[6:0] === 7'b0100011 )? 1:0;
        if(instruction[6] === 0 && instruction[4:2] === 3'b0)  
            ALUOp = 2'b00;
        else if(instruction[6:2] === 5'b11000)
            ALUOp = 2'b01;
        else
            ALUOp = 2'b10;
    end

    // ALU control
    always @(*) begin
        case(ALUOp)
            2'b00: ALUctrl = INST_ADD;    // load, store
            2'b01: case(instruction[14:12])     // branch
                3'b000: ALUctrl = INST_SUB;     // beq
                3'b101: ALUctrl = INST_SLT_N;   // bge
                3'b100: ALUctrl = INST_SLT;     // blt
                3'b001: ALUctrl = INST_SUB_N;   // bne
                default: ALUctrl = INST_ADD;
            endcase
            2'b10: case(instruction[6:0])   // I type, R type
                7'b0110011: case(instruction[14:12])    // R type
                    3'b000: ALUctrl = instruction[30] ? INST_SUB : (instruction[25] ? INST_MUL : INST_ADD) ;    // sub, mul, add
                    3'b111: ALUctrl = INST_AND; // and
                    3'b100: ALUctrl = INST_XOR; // xor
                    default: ALUctrl = INST_ADD;
                endcase
                7'b0010011: case(instruction[14:12])    // I type
                    3'b000: ALUctrl = INST_ADD; // addi
                    3'b001: ALUctrl = INST_SLL; // slli
                    3'b010: ALUctrl = INST_SLT; // slti
                    3'b101: ALUctrl = INST_SRA; // srai
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
        mul_valid_nxt = 1'b0;
        ALU_shreg = 64'b0;
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
                if(ALU_shreg == 64'd0) ALU_zero = 1'b1;
            end
            INST_SUB_N: begin
                shreg_tmp = i_A - i_B;
                if(i_A[31] == 0 && i_B[31] == 1 && shreg_tmp[31] == 1) ALU_shreg = 64'h000000007fffffff;
                else if(i_A[31] == 1 && i_B[31] == 0 && shreg_tmp[31] == 0) ALU_shreg = 64'h0000000080000000;
                else ALU_shreg = {32'd0, shreg_tmp};
                if(ALU_shreg != 64'd0) ALU_zero = 1'b1;
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
                ALU_zero = ALU_shreg[0];
            end
            INST_SLT_N: begin
                if(i_A[31] == 0 && i_B[31] == 1) ALU_shreg = 64'd0;
                else if(i_A[31] == 1 && i_B[31] == 0) ALU_shreg = {63'd0, 1'd1};
                else begin
                    shreg_tmp = i_A - i_B;
                    if( shreg_tmp[31] == 1 ) ALU_shreg = {63'd0, 1'd1};
                    else ALU_shreg = 64'd0;
                end
                ALU_zero = !ALU_shreg[0];
            end
            INST_SLL: begin
                shreg_tmp = i_A << i_B;
                ALU_shreg = {32'd0, shreg_tmp};
            end
            INST_SRA: begin
                shreg_tmp = i_A >>> i_B;  //! signed or unsigned? (signed)
                if(i_A[BIT_W-1] == 1'b0)
                    ALU_shreg = {32'b0, shreg_tmp};
                else
                    ALU_shreg = {{32{1'b1}}, shreg_tmp};
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


    // Sequential always block
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
            mul_valid <= 1'b0;
            state <= S_IDLE;
            newPC <= 1'b1;
            instruction <= 64'b0;
        end
        else begin
            PC <= next_PC;
            mul_valid <= mul_valid_nxt;
            state <= state_nxt;
            newPC <= newPC_nxt;
            instruction <= instruction_nxt;
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

    input  [DATA_W-1: 0]     i_A;     // input operand A
    input  [DATA_W-1: 0]     i_B;     // input operand B

    output [DATA_W-1: 0]     o_data;  // output value
    output                      o_done;

    // Regs
    reg [2*DATA_W-1: 0] shreg, shreg_nxt;
    
    reg [4:0] cnt, cnt_nxt;
    reg state, state_nxt;
    reg [DATA_W-1: 0] operand_a, operand_a_nxt;
    reg [DATA_W-1: 0] operand_b, operand_b_nxt;
    reg done;

    // continuous assignment
    assign o_data = shreg[DATA_W-1:0];
    assign o_done = done;


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
            S_WORK: state_nxt = (cnt == 5'd31) ? S_IDLE : state;
        endcase
    end

    // Counter
    always @(posedge i_clk) begin
        if(state == S_WORK)
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

    assign o_cache_available = 1; // ! change this value to 1 if the cache is implemented

    // //------------------------------------------//
    // //          default connection              //
    // assign o_mem_cen = i_proc_cen;              //
    // assign o_mem_wen = i_proc_wen;              //
    // assign o_mem_addr = i_proc_addr;            //
    // assign o_mem_wdata = i_proc_wdata;          //
    // assign o_proc_rdata = i_mem_rdata[0+:BIT_W];//
    // assign o_proc_stall = i_mem_stall;          //
    // //------------------------------------------//

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Parameters
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    parameter S_IDLE           = 3'd0;
    parameter S_WRITE          = 3'd1;
    parameter S_WB             = 3'd2;
    parameter S_ALLO           = 3'd3;
    parameter S_READ           = 3'd4;
    parameter S_FINISH         = 3'd5;
    parameter CACHE_DATA_SIZE  = 128;   // 32*4 bits
    parameter BLOCK_NUMBER     = 16;
    parameter TAG_SIZE         = 24;
    parameter ADDR_SIZE        = 32;
    parameter INDEX_SIZE       = 4;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // registers
    reg [2:0] state, state_nxt;
    reg o_cwen_cnt, o_cwen_cnt_nxt;
    reg [CACHE_DATA_SIZE-1:0] cache_data[BLOCK_NUMBER-1:0];
    reg [TAG_SIZE-1:0] cache_tag[BLOCK_NUMBER-1:0];
    reg cache_valid[BLOCK_NUMBER-1:0];
    reg cache_dirty[BLOCK_NUMBER-1:0];
    reg [BIT_W-1:0] o_proc_data_reg, o_proc_data_nxt;
    reg [ADDR_SIZE-1:0]    addr;    // relative address

    reg [CACHE_DATA_SIZE-1:0] cache_data_nxt;
    reg [TAG_SIZE-1:0] cache_tag_nxt;
    reg cache_valid_nxt, cache_dirty_nxt;
    reg cache_wen;
    reg [INDEX_SIZE:0] block_cnt, block_cnt_nxt;

    // wires
    wire [INDEX_SIZE-1:0] addr_idx;
    wire [1:0] addr_blk_ofs;
    wire [ADDR_SIZE-1:0] relative_addr_to_mem;
    wire hit, dirty;

    

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------


    assign addr_idx = (i_proc_finish)? block_cnt[INDEX_SIZE-1:0] : addr[ADDR_SIZE-TAG_SIZE-1: ADDR_SIZE-TAG_SIZE-INDEX_SIZE];
    assign addr_blk_ofs = addr[3:2];
    assign relative_addr_to_mem = (state == S_WB)? ({{cache_tag[addr_idx]}, addr_idx, 4'b0}):({addr[ADDR_SIZE-1:ADDR_SIZE-TAG_SIZE-INDEX_SIZE], 4'b0});

    // assign addr_index = i_proc_addr[ADDR_SIZE-TAG_SIZE-1: ADDR_SIZE-TAG_SIZE-INDEX_SIZE];
    assign o_proc_stall = i_mem_stall | (state == S_IDLE && i_proc_cen == 1) | (state != S_IDLE && state != S_FINISH);
    assign o_cache_finish = (state == S_FINISH);
    assign o_mem_cen = (((state == S_WB) || (state == S_ALLO)) & o_cwen_cnt);
    assign o_mem_wen = ((state == S_WB) & o_cwen_cnt);
    assign o_proc_rdata = o_proc_data_reg;
    assign o_mem_addr = (o_mem_cen || i_proc_finish)? (relative_addr_to_mem + i_offset) : 32'b0;
    assign o_mem_wdata = (o_mem_cen || i_proc_finish)? {cache_data[addr_idx]} : 128'b0;
    
    

    // Todo: BONUS

    // FSM
    always @(*) begin
        case(state)
            S_IDLE: begin
                if(i_proc_cen) begin
                    if(i_proc_wen)  state_nxt = S_WRITE;
                    else  state_nxt = S_READ;  // i_proc_wen = 0
                end
                else if (i_proc_finish) state_nxt = S_WB;
                else    state_nxt = state;
            end
            S_WRITE: begin
                if(hit)     state_nxt = S_FINISH;
                else begin// hit = 0
                    if(!i_mem_stall) begin
                        // o_cwen_cnt_nxt = 1;
                        if(dirty)   state_nxt = S_WB;
                        else    state_nxt = S_ALLO;     // dirty = 0
                    end
                    else    state_nxt = state;
                end
            end
            S_WB: begin
                if(!i_mem_stall)    begin
                    if(i_proc_finish)   begin
                        if(block_cnt_nxt == BLOCK_NUMBER)   state_nxt = S_FINISH;
                        else    state_nxt = S_WB;
                    end
                    else state_nxt = S_ALLO;
                end
                else    state_nxt = state;
            end
            S_ALLO: begin
                if(!i_mem_stall) begin
                    if(cache_wen)  state_nxt = S_WRITE;
                    else    state_nxt = S_READ;
                end
                else    state_nxt = state;
            end
            S_READ: begin
                if(hit)
                    state_nxt = S_FINISH;
                else if(!i_mem_stall) begin
                    // o_cwen_cnt_nxt = 1;
                    if(dirty)   state_nxt = S_WB;
                    else    state_nxt = S_ALLO;    // dirty = 0 
                end
                else    state_nxt = state;
            end
            S_FINISH: state_nxt = S_IDLE;
            default : state_nxt = state;
        endcase
    end

    // make sure o_mem_cen and o_mem_wen only remain high for 1 cycle
    always @(*) begin
        case(state)
            S_IDLE: o_cwen_cnt_nxt = (state_nxt == S_WB)? 1:0;
            S_WRITE, S_READ: o_cwen_cnt_nxt = (state_nxt == S_ALLO || state_nxt == S_WB)? 1 : 0;
            S_WB: o_cwen_cnt_nxt = (state_nxt == S_ALLO || block_cnt_nxt != block_cnt)? 1 : 0;
            default: o_cwen_cnt_nxt = 0;
        endcase
    end

    // block write back counter
    integer j;
    always @(*) begin
        if(!i_mem_stall && i_proc_finish) begin
            block_cnt_nxt = BLOCK_NUMBER;
            for(j=0; j<block_cnt; j=j+1) begin       // biggest j s.t. cache_valid[j] && cache_dirty[j]
                if(cache_valid[j] && cache_dirty[j])
                    block_cnt_nxt = j;
            end
        end
        else
            block_cnt_nxt = block_cnt;
    end

    assign hit = (cache_valid[addr_idx] == 1) & (cache_tag[addr_idx] == addr[ADDR_SIZE-1: ADDR_SIZE-TAG_SIZE]);
    assign dirty = (!hit) & cache_dirty[addr_idx];
    // operation in each state
    always @(*) begin
        cache_data_nxt = cache_data[addr_idx];
        cache_dirty_nxt = cache_dirty[addr_idx];
        cache_valid_nxt = cache_valid[addr_idx];
        cache_tag_nxt = cache_tag[addr_idx];
        o_proc_data_nxt = 32'b0;
        case(state)
            S_READ: begin
                if (hit) begin
                    o_proc_data_nxt = cache_data[addr_idx][(addr_blk_ofs+1)*BIT_W-1 -: BIT_W];
                end
            end
            S_WRITE: begin
                if (hit) begin
                    cache_data_nxt[(addr_blk_ofs+1)*BIT_W-1 -: BIT_W] = i_proc_wdata;
                    cache_dirty_nxt = 1;
                end
            end
            S_ALLO: begin
                if(!i_mem_stall) begin
                    cache_tag_nxt = addr[ADDR_SIZE-1:ADDR_SIZE-TAG_SIZE];
                    cache_data_nxt = i_mem_rdata;
                    cache_valid_nxt = 1;
                    cache_dirty_nxt = 0;
                end
            end
            default: o_proc_data_nxt = 32'b0;
        endcase
    end

    // Sequential
    integer i;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            for (i=0; i<BLOCK_NUMBER; i=i+1) begin
                cache_data[i] <= 0;
                cache_tag[i] <= 0;
                cache_dirty[i] <= 0;
                cache_valid[i] <= 0;
            end
            state <= S_IDLE;
            o_proc_data_reg <= 32'b0;
            // hit <= 0;
            // dirty <= 0;
            o_cwen_cnt <= 0;
            addr <= 0;
            cache_wen <= 0;
            block_cnt <= BLOCK_NUMBER;
        end
        else begin
            state <= state_nxt;
            o_proc_data_reg <= o_proc_data_nxt;
            o_cwen_cnt <= o_cwen_cnt_nxt;
            if(state == S_IDLE && !i_proc_finish)begin
                addr <= i_proc_addr-i_offset;
                cache_wen <= i_proc_wen;
            end
            cache_data[addr_idx] <= cache_data_nxt;
            cache_dirty[addr_idx] <= cache_dirty_nxt;
            cache_tag[addr_idx] <= cache_tag_nxt;
            cache_valid[addr_idx] <= cache_valid_nxt;
            block_cnt <= block_cnt_nxt;
        end
    end

endmodule