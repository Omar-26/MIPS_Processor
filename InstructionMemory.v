module InstructionMemory (
    input [31:0] address,
    output [31:0] instruction
);
    reg [31:0] memory [0:128];

    initial begin
        $readmemb("instructions.dat", memory);
    end

    assign instruction = memory[address[31:2]];

    // Task to read memory contents for testing
    task read_memory;
        input integer index;
        output [31:0] data;
        begin
            data = memory[index];
        end
    endtask

endmodule
