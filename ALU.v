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
