module Datapath (
    input clk,
    input reset,
    input [31:0] instruction,
    input reg_dst,
    input alu_src,
    input mem_to_reg,
    input reg_write,
    input mem_read,
    input mem_write,
    input branch,
    input jump,
    input [1:0] alu_op,
    output [31:0] alu_result,
    output [31:0] pc
);
    wire [31:0] next_pc, sign_ext_imm, next_instruction, jump_address, branch_address, next_address, branch_offset, read_data1, read_data2, alu_in2, write_data, mem_data;
    wire [4:0] write_reg;
    wire [3:0] alu_control;
    wire PCSrc;

    // Data Memory
    DataMemory dataMemory (.clk(clk), .mem_read(mem_read), .mem_write(mem_write), .address(alu_result), .write_data(read_data2), .read_data(mem_data));

    // Memory Output Selection
    Mux2to1 #(.WIDTH(32)) writeDataSel (.in0(alu_result), .in1(mem_data), .sel(mem_to_reg), .out(write_data));

    // Write Register Selection
    Mux2to1 #(.WIDTH(5)) writeRegisterSel (.in0(instruction[20:16]), .in1(instruction[15:11]), .sel(reg_dst), .out(write_reg));

    // Register File
    RegisterFile registerFile (.clk(clk), .reg_write(reg_write), .read_reg1(instruction[25:21]), .read_reg2(instruction[20:16]),
                           .write_reg(write_reg), .write_data(write_data), .read_data1(read_data1), .read_data2(read_data2));

    // Sign Extension
    SignExtend sign_ext (.in(instruction[15:0]), .out(sign_ext_imm));

    // ALU Control
    ALUControl aluControl (.alu_op(alu_op), .funct(instruction[5:0]), .alu_control(alu_control));

    // ALU 2nd Operand Selection
    Mux2to1 #(.WIDTH(32)) aluIn2Sel (.in0(read_data2), .in1(sign_ext_imm), .sel(alu_src), .out(alu_in2));

    // ALU
    ALU alu (.op1_i(read_data1), .op2_i(alu_in2), .alu_control(alu_control), .result(alu_result), .zero(zero));

    // Program Counter Register
    FlipFlop #(.WIDTH(32)) pcRegister (.clk(clk), .reset(reset), .d(next_pc), .q(pc));

    // Next Instruction Address Calculation
    Add nextInstruction (.in1(pc), .in2(4), .result(next_instruction));

    // Branch Address Calculation
    assign branch_offset = sign_ext_imm << 2;
    Add branchAddress (.in1(next_instruction), .in2(branch_offset), .result(branch_address));

    // Jump Address Calculation
    assign jump_address = {pc[31:28], instruction[25:0], 2'b00};

    // Branch Decision
    assign PCSrc = branch & zero;

    // Next PC Selection
    Mux2to1 #(.WIDTH(32)) nextAddressSel (.in0(next_instruction), .in1(branch_address), .sel(PCSrc), .out(next_address));
    Mux2to1 #(.WIDTH(32)) jumpAddressSel (.in0(next_address), .in1(jump_address), .sel(jump), .out(next_pc));

endmodule
