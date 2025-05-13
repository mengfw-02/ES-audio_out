//------------------------------------------------------------------------------
// FIFO Stream: 2048‑deep × 28‑bit, Ready/Valid handshake (one clock domain)
//------------------------------------------------------------------------------
//   • Upstream interface  :  src_valid / src_data  →  fifo  →  src_ready
//   • Downstream interface:  valid / data          →  consumer ← ready
//
// Behaviour
//   * Write:  if (src_valid && src_ready)         → store src_data
//   * Read :  if (ready && valid)                 → output next word
//   * src_ready  = 1  when !full                  (FIFO can accept more data)
//   * valid      = 1  when !empty                 (FIFO has data to send)
//   * src_ready is *true when FIFO is *empty* per user note but keeping standard
//     semantics (ready when *not full*); comment left for clarity.
//------------------------------------------------------------------------------
`timescale 1ns/1ps

module fifo_stream #(
    parameter int DATA_WIDTH = 28,
    parameter int DEPTH      = 2048,
    parameter int ADDR_WIDTH = $clog2(DEPTH)
)(
    input  logic                   clk,
    input  logic                   rst,        // synchronous active‑high reset

    // ─── Upstream (producer) side ─────────────────────────────────────────────
    input  logic                   src_valid,  // producer asserts when data present
    input  logic [DATA_WIDTH-1:0]  src_data,   // data word from producer
    output logic                   src_ready,  // FIFO ready to accept (1 ⇒ not full)

    // ─── Downstream (consumer) side ───────────────────────────────────────────
    input  logic                   ready,      // consumer ready for next word
    output logic                   valid,      // FIFO drives 1 when data present
    output logic [DATA_WIDTH-1:0]  data        // data word toward consumer
);

    // ──────────────────────────────────────────────────────────────────────────
    // Storage
    logic [DATA_WIDTH-1:0] mem [0:DEPTH-1];

    // Pointers and occupancy counter
    logic [ADDR_WIDTH-1:0] wr_ptr, rd_ptr;
    logic [ADDR_WIDTH:0]   cnt;    // 0 … DEPTH (needs ADDR_WIDTH+1 bits)

    // ─── Write path ───────────────────────────────────────────────────────────
    always_ff @(posedge clk) begin
        if (rst) begin
            wr_ptr <= '0;
        end else if (src_valid && src_ready) begin
            mem[wr_ptr] <= src_data;
            wr_ptr      <= wr_ptr + 1'b1;
        end
    end

    // ─── Read path ────────────────────────────────────────────────────────────
    logic [DATA_WIDTH-1:0] data_r;

    always_ff @(posedge clk) begin
        if (rst) begin
            rd_ptr  <= '0;
            data_r  <= '0;
        end else if (ready && valid) begin
            data_r <= mem[rd_ptr];
            rd_ptr <= rd_ptr + 1'b1;
        end
    end

    assign data  = data_r;

    // ─── Occupancy counter ───────────────────────────────────────────────────
    always_ff @(posedge clk) begin
        if (rst) begin
            cnt <= '0;
        end else begin
            unique case ({src_valid && src_ready, ready && valid})
                2'b10: cnt <= cnt + 1'b1; // write only
                2'b01: cnt <= cnt - 1'b1; // read only
                default: ;               // 00 idle or 11 simultaneous
            endcase
        end
    end

    // ─── Status ───────────────────────────────────────────────────────────────
    assign full  = (cnt == DEPTH); // internal use
    assign empty = (cnt == 0);

    assign src_ready = !full;   // producer may write when not full
    assign valid     = !empty;  // consumer may read  when not empty

endmodule

