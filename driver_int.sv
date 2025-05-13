module driver_interface
    #(parameter DATA_SIZE = 28)
    
    // bus to interface
   (input logic clk, // 50 MHz
    input logic rst, 
    input logic chipselect,
    input logic [1:0] address, // what is the address for?
    input logic read,

    //shifter inputs 
    input logic [1:0] source_valid,
    //input logic [1:0] source_sop,
    //input logic [1:0] source_eop,
    input logic [DATA_SIZE-1:0] source_data,

    // to shifter
    output logic [1:0] source_ready,

    // to bus 
    output logic [31:0] read_data,
    output logic irq
    );

    logic [DATA_SIZE-1:0] data_buffer;

    always_ff @(posedge clk) begin
        if (source_valid) begin
            data_buffer <= source_data;
            irq <= 1;  // set to 1        
        end
        if (chipselect && read) begin
            case(address)
                3'h0 : read_data <= {{32-DATA_SIZE{1'b0}}, data_buffer};

                source_ready <= 1;   // tell shifter ready to recieve again 
            endcase
        end
    end
endmodule
