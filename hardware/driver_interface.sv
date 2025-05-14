//------------------------------------------------------------------------------
// driver_interface.sv (IRQ removed – tied low)
//------------------------------------------------------------------------------
// Stream‑to‑bus bridge with an internal 2048 ×28‑bit FIFO.
// • Accepts source_valid / source_data and returns source_ready (2‑bit vector)
// • Bus read pops one word at address 0.
// • `irq` kept as a port but held LOW permanently.
//------------------------------------------------------------------------------
`timescale 1ns/1ps

module driver_interface #(
    parameter int DATA_SIZE  = 28,
    parameter int DEPTH      = 100,
    parameter int ADDR_WIDTH = $clog2(DEPTH)
)(
    // ─── Clock / Reset ───────────────────────────────────────────────────────
    input  logic                   clk,       // 50 MHz
    input  logic                   reset,       // synchronous active‑high

    // ─── Simple bus (read‑only) ──────────────────────────────────────────────
    input  logic                   chipselect,
    input  logic                   address,   // only bit‑0 used
    input  logic                   read,
    output logic [31:0]            read_data,

    // ─── Stream input ────────────────────────────────────────────────────────
    input  logic                   source_valid,
    input  logic [DATA_SIZE-1:0]   source_data,
    output logic                   source_ready,

    // ─── Interrupt (unused → tied low) ───────────────────────────────────────
    
);
   logic irq;

    // ──────────────────────────────────────────────────────────────────────────
    // FIFO storage (DEPTH × DATA_SIZE)
    logic [DATA_SIZE-1:0] mem [0:DEPTH-1];
    logic [ADDR_WIDTH-1:0] wr_ptr, rd_ptr;
    logic [ADDR_WIDTH:0]   cnt;               // occupancy counter 0‥DEPTH

    // Status flags
    wire full  = (cnt == DEPTH);
    wire empty = (cnt == 0);

    // ─── Write path ───────────────────────────────────────────────────────────
    always_ff @(posedge clk) begin
        if (reset) begin
            wr_ptr <= '0;
            cnt <= '0;
        end else if (source_valid && !full) begin
            mem[wr_ptr] <= source_data;
            wr_ptr <= wr_ptr + 1'b1;
            cnt <= cnt + 1'b1;
        end
    end

    // ─── Read path (bus pop) ─────────────────────────────────────────────────
    always_ff @(posedge clk) begin
        if (reset) begin
            rd_ptr <= '0;
            read_data <= '0;
        end else begin
            if (chipselect && read && !empty && (address == 1'b0)) begin
                read_data <= {{32-DATA_SIZE{1'b0}}, mem[rd_ptr]};
                rd_ptr <= rd_ptr + 1'b1;
                cnt <= cnt - 1'b1;
            end else if (!empty) begin
                read_data <= {{32-DATA_SIZE{1'b0}}, mem[rd_ptr]};
            end else begin
                read_data <= '0;
            end
        end
    end

    // ─── Ready signal to producer ────────────────────────────────────────────
    assign source_ready = full ? 1'b00 : 1'b11; // mirrors ready state on both bits

    // ─── IRQ permanently inactive ────────────────────────────────────────────
    assign irq = 1'b0;

endmodule
