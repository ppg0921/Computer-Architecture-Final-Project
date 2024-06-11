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

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Wires and Registers
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // TODO: any declaration
        reg [BIT_W-1:0] PC, next_PC;
        wire mem_cen, mem_wen;
        wire [BIT_W-1:0] mem_addr, mem_wdata, mem_rdata;
        wire mem_stall;
        // Control Signals
        reg Branch, MemRead, MemtoReg, MemWrite, ALUSrc, RegWrite;
        reg [1:0] ALUOp;

        reg [63:0] ImmGen;

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: any wire assignment

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Submoddules
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // TODO: Reg_file wire connection
    Reg_file reg0(               
        .i_clk  (i_clk),             
        .i_rst_n(i_rst_n),         
        .wen    (),          
        .rs1    (),                
        .rs2    (),                
        .rd     (),                 
        .wdata  (),             
        .rdata1 (),           
        .rdata2 ()
    );

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Always Blocks
// ------------------------------------------------------------------------------------------------------------------------------------------------------
    
    // Todo: any combinational/sequential circuit
    
    always @(*) begin
        next_PC = (Branch === 1)? PC+(ImmGen<<1) : PC+4;
    end

    // ImmGen
    always @(*) begin
        case(i_IMEM_data[6:0])
            7'b0110011: ImmGen = 64'b0;     // R type
            7'b0010011, 7'b1100111, 7'b0000011, 7'b1110011: ImmGen = {{52{i_IMEM_data[31]}}, i_IMEM_data[31:20]};      // I type
            7'b0100011: ImmGen = {{52{i_IMEM_data[31]}}, i_IMEM_data[31:25], i_IMEM_data[11:7]};       // S type
            7'b1100011: ImmGen = {{52{i_IMEM_data[31]}}, i_IMEM_data[31], i_IMEM_data[7], i_IMEM_data[30:25], i_IMEM_data[11:8]};      // B type
            7'b0010111: ImmGen = {{32{i_IMEM_data[31]}}, i_IMEM_data[31:12], {12'b0}};     // U type
            7'b1101111: ImmGen = {{44{i_IMEM_data[31]}}, i_IMEM_data[31], i_IMEM_data[19:12], i_IMEM_data[20], i_IMEM_data[30:21]};    // J type
            default: ImmGen = 64'b0;
        endcase
    end

    // Control Signals
    always @(*) begin
        Branch = (i_IMEM_data[6] === 1)? 1:0;
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

    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            PC <= 32'h00010000; // Do not modify this value!!!
        end
        else begin
            PC <= next_PC;
        end
    end
endmodule

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

module MULDIV_unit(
    // TODO: port declaration
    );
    // Todo: HW2
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
    reg [ADDR_SIZE-1:0]    addr;

    reg [CACHE_DATA_SIZE-1:0] cache_data_nxt;
    reg [TAG_SIZE-1:0] cache_tag_nxt;
    reg cache_valid_nxt, cache_dirty_nxt;

    // wires
    wire [INDEX_SIZE-1:0] addr_idx;
    wire [1:0] addr_blk_ofs;
    wire hit, dirty;

    

// ------------------------------------------------------------------------------------------------------------------------------------------------------
// Continuous Assignment
// ------------------------------------------------------------------------------------------------------------------------------------------------------

    // assign addr_index = i_proc_addr[ADDR_SIZE-TAG_SIZE-1: ADDR_SIZE-TAG_SIZE-INDEX_SIZE];
    // assign o_proc_stall = i_mem_stall | (state == S_IDLE && i_proc_cen == 1) | (state != S_IDLE && state != S_FINISH);
    // assign o_cache_finish = (state == S_FINISH);
    // assign o_mem_cen = ((state == S_WB) || (state == S_ALLO)) & o_cwen_cnt;
    // assign o_mem_wen = (state == S_WB) & o_cwen_cnt;
    // assign o_proc_rdata = o_proc_data_reg;
    // assign o_mem_addr = (i_proc_cen)? {cache_tag[i_proc_addr[ADDR_SIZE-TAG_SIZE-1: ADDR_SIZE-TAG_SIZE-INDEX_SIZE]], i_proc_addr[ADDR_SIZE-TAG_SIZE-1: ADDR_SIZE-TAG_SIZE-INDEX_SIZE], 4'b0} : 32'b0;
    // assign o_mem_wdata = (i_proc_cen)? {cache_data[i_proc_addr[ADDR_SIZE-TAG_SIZE-1: ADDR_SIZE-TAG_SIZE-INDEX_SIZE]]} : 128'b0;
    
    assign addr_idx = addr[ADDR_SIZE-TAG_SIZE-1: ADDR_SIZE-TAG_SIZE-INDEX_SIZE];
    assign addr_blk_ofs = addr[3:2];

    // Todo: BONUS

    // FSM
    always @(*) begin
        case(state)
            S_IDLE: begin
                if(i_proc_cen) begin
                    if(i_proc_wen)
                        state_nxt = S_WRITE;
                    else    // i_proc_wen = 0
                        state_nxt = S_READ;
                end
                else
                    state_nxt = state;
            end
            S_WRITE: begin
                if(hit)
                    state_nxt = S_FINISH;
                else begin// hit = 0
                    if(!i_mem_stall) begin
                        // o_cwen_cnt_nxt = 1;
                        if(dirty)
                            state_nxt = S_WB;
                        else    // dirty = 0
                            state_nxt = S_ALLO;
                    end
                    else
                        state_nxt = state;
                end
            end
            S_WB: begin
                if(!i_mem_stall)
                    state_nxt = S_ALLO;
                else
                    state_nxt = state;
            end
            S_ALLO: begin
                if(!i_mem_stall) begin
                    if(i_proc_wen)
                        state_nxt = S_WRITE;
                    else
                        state_nxt = S_READ;
                end
                else
                    state_nxt = state;
            end
            S_READ: begin
                if(hit)
                    state_nxt = S_FINISH;
                else if(!i_mem_stall) begin
                    // o_cwen_cnt_nxt = 1;
                    if(dirty)
                        state_nxt = S_WB;
                    else    // dirty = 0
                        state_nxt = S_ALLO;
                end
                else
                    state_nxt = state;
            end
            S_FINISH: state_nxt = S_IDLE;
            default : state_nxt = state;
        endcase
    end

    // make sure o_mem_cen and o_mem_wen only remain high for 1 cycle
    always @(*) begin
        case(state)
            S_WRITE, S_READ: o_cwen_cnt_nxt = (state_nxt == S_ALLO || state_nxt == S_WB)? 1 : 0;
            S_WB: o_cwen_cnt_nxt = (state_nxt == S_ALLO)? 1 : 0;
            default: o_cwen_cnt_nxt = 0;
        endcase
    end

    assign hit = (cache_valid[addr_idx] == 1) & (cache_tag[addr_idx] == addr[ADDR_SIZE-1: ADDR_SIZE-TAG_SIZE]);
    assign dirty = (!hit) & cache_dirty[addr_idx];

    // always @(*) begin
    //     if (cache_valid[addr_idx] == 1) begin
    //         if (cache_tag[addr_idx] == addr[ADDR_SIZE-1: ADDR_SIZE-TAG_SIZE])
    //             hit = 1;
    //         else
    //             hit = 0;
    //     end
    //     else
    //         hit = 0;
    //     dirty = (!hit) & cache_dirty[addr_idx];
    // end

    // operation in each state
    always @(*) begin
        cache_data_nxt = cache_data[addr_idx];
        cache_dirty_nxt = cache_dirty[addr_idx];
        cache_valid_nxt = cache_valid[addr_idx];
        cache_tag_nxt = cache_tag[addr_idx];
        case(state)
            S_READ: begin
                if (hit) begin
                    o_proc_data_nxt = cache_data[addr_idx][(addr_blk_ofs+1)*BIT_W-1 -: BIT_W];
                end
                else
                    o_proc_data_nxt = 32'b0;
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
        end
        else begin
            state <= state_nxt;
            o_proc_data_reg <= o_proc_data_nxt;
            o_cwen_cnt <= o_cwen_cnt_nxt;
            if(state == S_IDLE)
                addr <= i_proc_addr;
            cache_data[addr_idx] <= cache_data_nxt;
            cache_dirty[addr_idx] <= cache_dirty_nxt;
            cache_tag[addr_idx] <= cache_tag_nxt;
            cache_valid[addr_idx] <= cache_valid_nxt;
        end
    end

endmodule