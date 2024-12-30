module InstructionMemory (
    input [31:0] address,
    output [31:0] instruction,
    output reg invalid_instruction
);
    reg [31:0] memory [0:128];

    initial begin
        $readmemb("instructions.dat", memory);
    end

    assign instruction = memory[address[31:2]];

    always @(address) begin
        if (memory[address[31:2]] === 32'bxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx) begin
            invalid_instruction = 1;
        end else begin
            invalid_instruction = 0;
        end
    end

    // Task to read memory contents for testing
    task read_memory;
        input integer index;
        output [31:0] data;
        begin
            data = memory[index];
        end
    endtask

endmodule

module DataMemory (
	input clk,
	input mem_read,
	input mem_write,
	input [31:0] address,
	input [31:0] write_data,
	output [31:0] read_data
);
	reg [31:0] memory [0:4095];

    assign read_data = mem_read ? memory[address[31:2]]: 32'b0; // To ensure Word Allignment

    always @(posedge clk) begin
        if (mem_write) begin
            memory[address[31:2]] <= write_data;
        end
    end

// Task to read memory contents for testing
    task read_memory;
        input integer index;
        output [31:0] data;
        begin
            data = memory[index];
        end
    endtask

endmodule

module SignExtend (
    input [15:0] in,
    output [31:0] out
);
    assign out = {{16{in[15]}}, in};
endmodule
module Mux2to1 #(
    parameter WIDTH = 32
)(
    input sel,
    input [WIDTH-1:0] in0,
    input [WIDTH-1:0] in1,
    output reg [WIDTH-1:0] out
);
    always @(*) begin
        case (sel)
            1'b0: out = in0;
            1'b1: out = in1;
            default: out = {WIDTH{1'b0}};
        endcase
    end
endmodule

module FlipFlop #(
    parameter WIDTH = 32
)(
    input clk,
    input reset,
    input [WIDTH-1:0] d,
    output reg [WIDTH-1:0] q
);
    always @(posedge clk or posedge reset) begin
        if (reset)
            q <= {WIDTH{1'b0}};
        else
            q <= d;
    end
endmodule

module RegisterFile (
    input clk,
    input reg_write,
    input [4:0] read_reg1,
    input [4:0] read_reg2,
    input [4:0] write_reg,
    input [31:0] write_data,
    output [31:0] read_data1,
    output [31:0] read_data2
);
    reg [31:0] registers [31:0];


    initial begin
      registers[0] = 0;
      registers[1] = 2;
      registers[2] = 2;
      registers[4] = 4;
      registers[5] = 5;
      registers[7] = 7;
      registers[8] = 8;
    end


    assign read_data1 = registers[read_reg1];
    assign read_data2 = registers[read_reg2];

    always @(posedge clk) begin
        if (reg_write) begin
            registers[write_reg] <= write_data;
        end
    end
endmodule

module Add (
input [31:0] in1,
input [31:0] in2,
output [31:0] result
);
assign result = in1 + in2 ;

endmodule
module ALUControl (
	input reg [1:0] alu_op,
	input reg [5:0] funct,
	output reg [3:0] alu_control
);
always @(*) begin
	case (alu_op)
	2'b00: alu_control = 4'b0010; // add for sw and lw
	2'b01: alu_control = 4'b0110; // sub for beq
	2'b10: begin
		case (funct)
		6'b100000: alu_control = 4'b0010; // add
		6'b100010: alu_control = 4'b0110; // sub
		6'b100100: alu_control = 4'b0000; // and
		6'b100101: alu_control = 4'b0001; // or
		6'b101010: alu_control = 4'b0111; // slt
		default: alu_control = 4'bxxxx;
		endcase
	end
	default: alu_control = 4'bxxxx;
	endcase
end
endmodule

module ALU (
    input [31:0] op1_i,
    input [31:0] op2_i,
    input [3:0] alu_control,
    output reg [31:0] result,
    output zero	// Zero Flag
);
    always @(*) begin
        case (alu_control)
            4'b0000: result = op1_i & op2_i; 		// AND
            4'b0001: result = op1_i | op2_i; 		// OR
            4'b0010: result = op1_i + op2_i; 		// ADD
            4'b0110: result = op1_i - op2_i; 		// SUB
            4'b0111: result = (op1_i < op2_i) ? 1 : 0; 	// SLT
            4'b1100: result = ~(op1_i | op2_i); 	// NOR
            default: result = 0;
        endcase
    end
    assign zero = (result == 0);
endmodule

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
    output [31:0] pc
);
    wire [31:0] next_pc, sign_ext_imm, next_instruction, jump_address, branch_address, next_address, branch_offset, read_data1, read_data2, alu_in2, write_data, mem_data;
    wire [4:0] write_reg;
    wire [3:0] alu_control;
    wire PCSrc;
    wire [31:0] alu_result; // Declare alu_result
    wire zero; // Declare zero

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

module ControlUnit (
    input [5:0] opcode,
    output reg reg_dst,
    output reg alu_src,
    output reg mem_to_reg,
    output reg reg_write,
    output reg mem_read,
    output reg mem_write,
    output reg branch,
    output reg jump,
    output reg [1:0] alu_op
);
localparam R = 6'b000000;
localparam lw = 6'b100011;
localparam sw = 6'b101011;
localparam beq = 6'b000100;
localparam j = 6'b000010;

always @(*) begin
    case (opcode)
        R: begin
            reg_dst = 1;
            reg_write = 1;
            alu_src = 0;
            mem_to_reg = 0;
            mem_read = 0;
            mem_write = 0;
            branch = 0;
            jump = 0;
            alu_op = 2'b10; // ALU Op to be determined by the funct field
        end
        lw: begin
            reg_dst = 0;
            reg_write = 1;
            alu_src = 1;
            mem_to_reg = 1;
            mem_read = 1;
            mem_write = 0;
            branch = 0;
            jump = 0;
            alu_op = 2'b00; // ALU Op for addition
        end
        sw: begin
            reg_dst = 0; // Don't care
            reg_write = 0;
            alu_src = 1;
            mem_to_reg = 0; // Don't care
            mem_read = 0;
            mem_write = 1;
            branch = 0;
            jump = 0;
            alu_op = 2'b00; // ALU Op for addition
        end
        beq: begin
            reg_dst = 0; // Don't care
            reg_write = 0;
            alu_src = 0;
            mem_to_reg = 0; // Don't care
            mem_read = 0;
            mem_write = 0;
            branch = 1;
            jump = 0;
            alu_op = 2'b01; // ALU Op for subtraction
        end
        j: begin
            reg_dst = 0; // Don't care
            reg_write = 0;
            alu_src = 0; // Don't care
            mem_to_reg = 0; // Don't care
            mem_read = 0;
            mem_write = 0;
            branch = 0;
            jump = 1;
            alu_op = 2'b00; // Don't care
        end
        default: begin
            {reg_dst, reg_write, alu_src, mem_to_reg, mem_read, mem_write, branch, jump, alu_op} = 10'b0;
        end
    endcase
end
endmodule




module MIPSProcessor (
    input clk,
    input reset,
    output invalid_instruction
);
    wire [31:0] instruction, alu_result, pc;
    // Control Signals
    wire reg_dst, alu_src, mem_to_reg, reg_write, mem_read, mem_write, branch, jump;
    wire [1:0] alu_op;

    InstructionMemory instructionMemory (.address(pc), .instruction(instruction), .invalid_instruction(invalid_instruction));

    ControlUnit controlUnit (.opcode(instruction[31:26]), .reg_dst(reg_dst), .alu_src(alu_src), .mem_to_reg(mem_to_reg),
                .reg_write(reg_write), .mem_read(mem_read),.mem_write(mem_write), .branch(branch),.jump(jump),.alu_op(alu_op));

    Datapath dataPath (.clk(clk), .reset(reset), .instruction(instruction), .reg_dst(reg_dst), .alu_src(alu_src), .mem_to_reg(mem_to_reg), .reg_write(reg_write),
               .mem_read(mem_read), .mem_write(mem_write), .branch(branch), .jump(jump), .alu_op(alu_op) , .pc(pc));

endmodule


`timescale 1ns / 1ps

module MIPSProcessor_tb;
    reg clk;
    reg reset;
    wire invalid_instruction;

    // Instantiate the MIPSProcessor
    MIPSProcessor uut (
        .clk(clk),
        .reset(reset),
        .invalid_instruction(invalid_instruction)
    );

    // Clock generation
    always begin
        #5 clk = ~clk; // 10ns period clock
    end

    initial begin
        // Initialize clock and reset
        clk = 0;
        reset = 1;

        // Reset the processor
        #10 reset = 0;

        // Load instructions and initial memory values
        $readmemb("instructions.dat", uut.instructionMemory.memory); // Load instructions
        $readmemh("data.dat", uut.dataPath.dataMemory.memory); // Load data memory

        // Run simulation until an invalid instruction is detected
        while (!invalid_instruction) begin
            #10;
        end

        // Display register file contents
        $display("Register File Contents:");
        for (integer i = 0; i < 32; i = i + 1) begin
            $display("R[%0d] = %h", i, uut.dataPath.registerFile.registers[i]);
        end

        // Display data memory contents
        $display("Data Memory Contents:");
        for (integer i = 0; i < 10; i = i + 1) begin
            $display("MEM[%0d] = %h", i, uut.dataPath.dataMemory.memory[i]);
        end

        $finish;
    end

    // debug information
    always @(posedge clk) begin
        $display("Time: %0t | PC: %h | Instruction: %h | ALU Result: %h | RegWrite: %b | WriteReg: %d | WriteData: %h | MemWrite: %b | MemRead: %b | MemData: %h",
                 $time, uut.dataPath.pc, uut.dataPath.instruction, uut.dataPath.alu_result, uut.dataPath.reg_write, uut.dataPath.write_reg, uut.dataPath.write_data, uut.dataPath.mem_write, uut.dataPath.mem_read, uut.dataPath.dataMemory.memory[3]);
    end

endmodule
