`timescale 1ns/1ps

module driver_interface_tb();
    // Parameters
    parameter DATA_SIZE = 28;
    parameter CLK_PERIOD = 20; // 50MHz clock

    // Test signals
    logic clk;
    logic reset;
    logic chipselect;
    logic address;
    logic read;
    logic source_valid;
    logic [DATA_SIZE-1:0] source_data;
    logic source_ready;
    logic [31:0] read_data;

    // Instantiate the driver interface
    driver_interface #(
        .DATA_SIZE(DATA_SIZE)
    ) dut (
        .clk(clk),
        .reset(reset),
        .chipselect(chipselect),
        .address(address),
        .read(read),
        .source_valid(source_valid),
        .source_data(source_data),
        .source_ready(source_ready),
        .read_data(read_data)
    );

    // Clock generation
    initial begin
        clk = 0;
        forever #(CLK_PERIOD/2) clk = ~clk;
    end

    // Test stimulus
    initial begin
        // Initialize signals
        reset = 1;
        chipselect = 0;
        address = 0;
        read = 0;
        source_valid = 0;
        source_data = 0;

        // Reset sequence
        #(CLK_PERIOD*2);
        reset = 0;
        #(CLK_PERIOD*2);

        // Test Case 1: Basic data transfer and read
        // Send data
        source_valid = 1;
        source_data = 28'h1234567;
        #(CLK_PERIOD);
        source_valid = 0;
        #(CLK_PERIOD*2);

        // Read the data
        chipselect = 1;
        read = 1;
        address = 0;
        #(CLK_PERIOD);
        chipselect = 0;
        read = 0;
        #(CLK_PERIOD*2);

        // Test Case 2: Try to write when data_full
        source_valid = 1;
        source_data = 28'hABCDEF0;
        #(CLK_PERIOD);
        source_valid = 0;
        #(CLK_PERIOD*2);

        // Read first data
        chipselect = 1;
        read = 1;
        address = 0;
        #(CLK_PERIOD);
        chipselect = 0;
        read = 0;
        #(CLK_PERIOD*2);

        // End simulation
        #(CLK_PERIOD*20);
        $finish;
    end

    // Monitor and display results
    initial begin
        $monitor("Time=%0t reset=%b chipselect=%b address=%b read=%b valid=%b data=%h ready=%b read_data=%h",
                 $time, reset, chipselect, address, read, source_valid, source_data, source_ready, read_data);
    end

    // Add waveform dumping
    initial begin
        $dumpfile("driver_interface_tb.vcd");
        $dumpvars(0, driver_interface_tb);
    end

    // Assertions
    property source_ready_when_empty;
        @(posedge clk) !dut.data_full |-> source_ready;
    endproperty
    assert property (source_ready_when_empty) else $error("source_ready should be 1 when data_full is 0");

    property source_ready_when_full;
        @(posedge clk) dut.data_full |-> !source_ready;
    endproperty
    assert property (source_ready_when_full) else $error("source_ready should be 0 when data_full is 1");

endmodule