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

