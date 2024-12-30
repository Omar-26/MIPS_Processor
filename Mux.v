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

