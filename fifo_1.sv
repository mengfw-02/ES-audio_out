// Simple synchronous FIFO with parameterizable width & depth

module fifo #(
    parameter int DATA_WIDTH = 32,
    parameter int DEPTH      = 256,
    parameter int ADDR_WIDTH = $clog2(DEPTH)
)(
    input logic  clk,
    input logic   rst,       // active-high synchronous reset

    // Write port
    input  logic  wr_en,
    input  logic [DATA_WIDTH-1:0]  wr_data,
    output logic  full,

    // Read port
    input  logic                   rd_en,
    output logic [DATA_WIDTH-1:0]  rd_data,
    output logic                   empty
);

    // Memory array
    logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];

    // Pointers and count
    logic [ADDR_WIDTH-1:0] wr_ptr, rd_ptr;
    logic [ADDR_WIDTH:0]   count;

    // Full/Empty signals
    assign full  = (count == DEPTH);
    assign empty = (count == 0);

    // Read data register
    logic [DATA_WIDTH-1:0] rd_data_reg;
    assign rd_data = rd_data_reg;

    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            wr_ptr      <= '0;
            rd_ptr      <= '0;
            count       <= '0;
            rd_data_reg <= '0;
        end else begin
            // Write side
            if (wr_en && !full) begin
                mem[wr_ptr] <= wr_data;
                wr_ptr      <= wr_ptr + 1;
            end
            
            // Read side
            if (rd_en && !empty) begin
                rd_data_reg <= mem[rd_ptr];
                rd_ptr      <= rd_ptr + 1;
            end

            // Update count: +1 on write only, -1 on read only, unchanged if both
            unique case ({wr_en && !full, rd_en && !empty})
                2'b10: count <= count + 1;
                2'b01: count <= count - 1;
                default: count <= count;
            endcase
        end
    end

endmodule
