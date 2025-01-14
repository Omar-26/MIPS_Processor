module MIPSProcessor_tb;
    reg clk;
    reg reset;
    integer i;
    reg [31:0] instruction_data;
    reg [31:0] memory_data;

    // Instantiate the MIPSProcessor
    MIPSProcessor uut (
        .clk(clk),
        .reset(reset)
    );

    initial begin
        // Initialize signals
        clk = 0;
        reset = 1;
        #10 reset = 0;

        // Monitor the PC value
        $monitor("Time: %0t | PC: %h", $time, uut.dataPath.pc);

        // Wait for some time to let the processor execute instructions
        #100;

        // Display the contents of the instruction memory
        display_instruction_memory();

        // Wait for some more time
        #900;

        // Display the contents of the data memory
        display_data_memory();

        // Check the value of register $2
        check_register_value(2, 4);

        // Check the value of memory at address 4
        check_memory_value(4, 4);

        // Check the value of PC
        check_pc_value(8);

        // Finish simulation
        $finish;
    end

    // Clock generation
    always begin
        #5 clk = ~clk; // 10ns period clock
    end

    // Task to display the contents of the instruction memory
    task display_instruction_memory;
        begin
            $display("Instruction Memory Contents:");
            for (i = 0; i < 2; i = i + 1) begin
                uut.instructionMemory.read_memory(i, instruction_data);
                $display("Address %0d: %h", i*4, instruction_data);
            end
        end
    endtask

    // Task to display the contents of the data memory
    task display_data_memory;
        begin
            $display("Data Memory Contents:");
            for (i = 0; i < 2; i = i + 1) begin
                uut.dataPath.dataMemory.read_memory(i, memory_data);
                $display("Address %0d: %h", i*4, memory_data);
            end
        end
    endtask

    // Task to check the value of a register
    task check_register_value;
        input integer reg_num;
        input [31:0] expected_value;
        reg [31:0] reg_value;
        begin
            reg_value = uut.dataPath.registerFile.registers[reg_num];
            if (reg_value !== expected_value) begin
                $display("ERROR: Register $%0d contains %h, expected %h", reg_num, reg_value, expected_value);
            end else begin
                $display("Register $%0d contains the expected value %h", reg_num, reg_value);
            end
        end
    endtask

    // Task to check the value of memory at a specific address
    task check_memory_value;
        input integer address;
        input [31:0] expected_value;
        reg [31:0] mem_value;
        begin
            uut.dataPath.dataMemory.read_memory(address >> 2, mem_value);
            if (mem_value !== expected_value) begin
                $display("ERROR: Memory at address %0d contains %h, expected %h", address, mem_value, expected_value);
            end else begin
                $display("Memory at address %0d contains the expected value %h", address, mem_value);
            end
        end
    endtask

    // Task to check the value of PC
    task check_pc_value;
        input [31:0] expected_value;
        begin
            if (uut.dataPath.pc !== expected_value) begin
                $display("ERROR: PC contains %h, expected %h", uut.dataPath.pc, expected_value);
            end else begin
                $display("PC contains the expected value %h", uut.dataPath.pc);
            end
        end
    endtask

    // Stop the simulation after a certain number of cycles
    always @(posedge clk) begin
        if (uut.dataPath.pc >= 32'h0000002C) begin
            $display("Simulation finished: PC reached %h", uut.dataPath.pc);
            $finish;
        end
    end

endmodule
