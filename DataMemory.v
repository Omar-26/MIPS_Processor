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
