// SPDX-FileCopyrightText: 2020 Efabless Corporation
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
// SPDX-License-Identifier: Apache-2.0

`default_nettype none
/*
 *-------------------------------------------------------------
 *
 * user_proj_example
 *
 * This is an example of a (trivially simple) user project,
 * showing how the user project can connect to the logic
 * analyzer, the wishbone bus, and the I/O pads.
 *
 * This project generates an integer count, which is output
 * on the user area GPIO pads (digital output only).  The
 * wishbone connection allows the project to be controlled
 * (start and stop) from the management SoC program.
 *
 * See the testbenches in directory "mprj_counter" for the
 * example programs that drive this user project.  The three
 * testbenches are "io_ports", "la_test1", and "la_test2".
 *
 *-------------------------------------------------------------
 */

module user_proj_example #(
    parameter BITS = 32
)(
`ifdef USE_POWER_PINS
    inout vccd1,	// User area 1 1.8V supply
    inout vssd1,	// User area 1 digital ground
`endif

    // Wishbone Slave ports (WB MI A)
    input wb_clk_i,
    input wb_rst_i,
    input wbs_stb_i,
    input wbs_cyc_i,
    input wbs_we_i,
    input [3:0] wbs_sel_i,
    input [31:0] wbs_dat_i,
    input [31:0] wbs_adr_i,
    output wbs_ack_o,
    output [31:0] wbs_dat_o,

    // Logic Analyzer Signals
    input  [127:0] la_data_in,
    output [127:0] la_data_out,
    input  [127:0] la_oenb,

    // IOs
    input  [`MPRJ_IO_PADS-1:0] io_in,
    output [`MPRJ_IO_PADS-1:0] io_out,
    output [`MPRJ_IO_PADS-1:0] io_oeb,

    // IRQ
    output [2:0] irq
);
    wire clk;
    wire rst;

    wire [`MPRJ_IO_PADS-1:0] io_in;
    wire [`MPRJ_IO_PADS-1:0] io_out;
    wire [`MPRJ_IO_PADS-1:0] io_oeb;

    wire [31:0] rdata; 
    wire [31:0] wdata;
    wire [BITS-1:0] count;

    wire valid;
    wire [3:0] wstrb;
    wire [31:0] la_write;

    // WB MI A
    assign valid = wbs_cyc_i && wbs_stb_i; 
    assign wstrb = wbs_sel_i & {4{wbs_we_i}};
    assign wbs_dat_o = rdata;
    assign wdata = wbs_dat_i;

    // IO
    assign io_out = count;
    assign io_oeb = {(`MPRJ_IO_PADS-1){rst}};

    // IRQ
    assign irq = 3'b000;	// Unused

    // LA
    assign la_data_out = {{(127-BITS){1'b0}}, count};
    // Assuming LA probes [63:32] are for controlling the count register  
    assign la_write = ~la_oenb[63:32] & ~{BITS{valid}};
    // Assuming LA probes [65:64] are for controlling the count clk & reset  
    assign clk = (~la_oenb[64]) ? la_data_in[64]: wb_clk_i;
    assign rst = (~la_oenb[65]) ? la_data_in[65]: wb_rst_i;

accumulator_npar_parallel_complete dut(

i0s,i1s,i2s,i3s,i4s,i5s,i6s,i7s,i8s,i9s,i10s,i11s,i12s,i13s,i14s,i15s,i16s,i17s,i18s,i19s,i20s,i21s,i22s,i23s,i24s,i25s,i26s,i27s,i28s,i29s,i30s,i31s,
i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,i24,i25,i26,i27,i28,i29,i30,i31,
s,ss,clk,reset,
se0,se1,se2,se3,se4,se5,se6,se7,se8,se9,se10,se11,se12,se13,se14,se15,se16,se17,se18,se19,se20,se21,se22,se23,se24,se25,se26,se27,se28,se29,se30,se31,

oo0,oo1,oo2,oo3,oo4,oo5,oo6,oo7,oo8,oo9,oo10,oo11,oo12,oo13,oo14,oo15,oo16,oo17,oo18,oo19,oo20,oo21,oo22,oo23,oo24,oo25,oo26,oo27,oo28,oo29,oo30,oo31,
oo0s,oo1s,oo2s,oo3s,oo4s,oo5s,oo6s,oo7s,oo8s,oo9s,oo10s,oo11s,oo12s,oo13s,oo14s,oo15s,oo16s,oo17s,oo18s,oo19s,oo20s,oo21s,oo22s,oo23s,
oo24s,oo25s,oo26s,oo27s,oo28s,oo29s,oo30s,oo31s

);
endmodule

//accumulator based 2D parallel architecture (N-outputs at a time)
//area and throughput efficient IDCT/IDST architecutre for hevc standard

//`include "accumulator_npar_parallel.v"
//`include "dflipflop25.v"
//`include "storage32_25.v"

module accumulator_npar_parallel_complete(

i0s,i1s,i2s,i3s,i4s,i5s,i6s,i7s,i8s,i9s,i10s,i11s,i12s,i13s,i14s,i15s,i16s,i17s,i18s,i19s,i20s,i21s,i22s,i23s,i24s,i25s,i26s,i27s,i28s,i29s,i30s,i31s,
i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,i24,i25,i26,i27,i28,i29,i30,i31,
s,ss,clk,reset,
se0,se1,se2,se3,se4,se5,se6,se7,se8,se9,se10,se11,se12,se13,se14,se15,se16,se17,se18,se19,se20,se21,se22,se23,se24,se25,se26,se27,se28,se29,se30,se31,

oo0,oo1,oo2,oo3,oo4,oo5,oo6,oo7,oo8,oo9,oo10,oo11,oo12,oo13,oo14,oo15,oo16,oo17,oo18,oo19,oo20,oo21,oo22,oo23,oo24,oo25,oo26,oo27,oo28,oo29,oo30,oo31,
oo0s,oo1s,oo2s,oo3s,oo4s,oo5s,oo6s,oo7s,oo8s,oo9s,oo10s,oo11s,oo12s,oo13s,oo14s,oo15s,oo16s,oo17s,oo18s,oo19s,oo20s,oo21s,oo22s,oo23s,
oo24s,oo25s,oo26s,oo27s,oo28s,oo29s,oo30s,oo31s

);

input clk,reset;

input i0s,i1s,i2s,i3s,i4s,i5s,i6s,i7s,i8s,i9s,i10s,i11s,i12s,i13s,i14s,i15s,i16s,i17s,i18s,i19s,i20s,i21s,i22s,i23s,i24s,i25s,i26s,i27s,i28s,i29s,i30s,i31s;
input [7:0] i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,i24,i25,i26,i27,i28,i29,i30,i31;

input s,ss;//ss=0 for row process and ss=1 for column process

input se0,se1,se2,se3,se4,se5,se6,se7,se8,se9,se10,se11,se12,se13,se14,se15,se16,se17,se18,se19,se20,se21,se22,se23,se24,se25,se26,se27,se28,se29,se30,se31;

output [39:0] oo0,oo1,oo2,oo3,oo4,oo5,oo6,oo7,oo8,oo9,oo10,oo11,oo12,oo13,oo14,oo15,oo16,oo17,oo18,oo19,oo20,oo21,oo22,oo23,oo24,oo25,oo26,oo27,oo28,oo29,oo30,oo31;
output oo0s,oo1s,oo2s,oo3s,oo4s,oo5s,oo6s,oo7s,oo8s,oo9s,oo10s,oo11s,oo12s,oo13s,oo14s,oo15s,oo16s,oo17s,oo18s,oo19s,oo20s,oo21s,oo22s,
oo23s,oo24s,oo25s,oo26s,oo27s,oo28s,oo29s,oo30s,oo31s;

//row process

wire ou0s,ou1s,ou2s,ou3s,ou4s,ou5s,ou6s,ou7s,ou8s,ou9s,ou10s,ou11s,ou12s,ou13s,ou14s,ou15s,
ou16s,ou17s,ou18s,ou19s,ou20s,ou21s,ou22s,ou23s,ou24s,ou25s,ou26s,ou27s,ou28s,ou29s,ou30s,ou31s;
wire [23:0] ou0,ou1,ou2,ou3,ou4,ou5,ou6,ou7,ou8,ou9,ou10,ou11,ou12,ou13,ou14,ou15,
ou16,ou17,ou18,ou19,ou20,ou21,ou22,ou23,ou24,ou25,ou26,ou27,ou28,ou29,ou30,ou31;

accumulator_npar_parallel dfd(

i0s,i1s,i2s,i3s,i4s,i5s,i6s,i7s,i8s,i9s,i10s,i11s,i12s,i13s,i14s,i15s,i16s,i17s,i18s,i19s,i20s,i21s,i22s,i23s,i24s,i25s,i26s,i27s,i28s,i29s,i30s,i31s,
i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,i24,i25,i26,i27,i28,i29,i30,i31,
s,clk,reset,
ou0s,ou1s,ou2s,ou3s,ou4s,ou5s,ou6s,ou7s,ou8s,ou9s,ou10s,ou11s,ou12s,ou13s,ou14s,ou15s,ou16s,ou17s,ou18s,ou19s,ou20s,ou21s,ou22s,ou23s,ou24s,ou25s,ou26s,ou27s,ou28s,ou29s,ou30s,ou31s,
ou0,ou1,ou2,ou3,ou4,ou5,ou6,ou7,ou8,ou9,ou10,ou11,ou12,ou13,ou14,ou15,ou16,ou17,ou18,ou19,ou20,ou21,ou22,ou23,ou24,ou25,ou26,ou27,ou28,ou29,ou30,ou31

);

//32x32-transpose buffer

wire od0s,od1s,od2s,od3s,od4s,od5s,od6s,od7s,od8s,od9s,od10s,od11s,od12s,od13s,od14s,od15s,
od16s,od17s,od18s,od19s,od20s,od21s,od22s,od23s,od24s,od25s,od26s,od27s,od28s,od29s,od30s,od31s;
wire [23:0] od0,od1,od2,od3,od4,od5,od6,od7,od8,od9,od10,od11,od12,od13,od14,od15,
od16,od17,od18,od19,od20,od21,od22,od23,od24,od25,od26,od27,od28,od29,od30,od31;

storage32_25 ds00({ou0s,ou0},{od0s,od0},se0,clk,reset);
storage32_25 ds01({ou1s,ou1},{od1s,od1},se1,clk,reset);
storage32_25 ds02({ou2s,ou2},{od2s,od2},se2,clk,reset);
storage32_25 ds03({ou3s,ou3},{od3s,od3},se3,clk,reset);
storage32_25 ds04({ou4s,ou4},{od4s,od4},se4,clk,reset);
storage32_25 ds05({ou5s,ou5},{od5s,od5},se5,clk,reset);
storage32_25 ds06({ou6s,ou6},{od6s,od6},se6,clk,reset);
storage32_25 ds07({ou7s,ou7},{od7s,od7},se7,clk,reset);
storage32_25 ds08({ou8s,ou8},{od8s,od8},se8,clk,reset);
storage32_25 ds09({ou9s,ou9},{od9s,od9},se9,clk,reset);
storage32_25 ds10({ou10s,ou10},{od10s,od10},se10,clk,reset);
storage32_25 ds11({ou11s,ou11},{od11s,od11},se11,clk,reset);
storage32_25 ds12({ou12s,ou12},{od12s,od12},se12,clk,reset);
storage32_25 ds13({ou13s,ou13},{od13s,od13},se13,clk,reset);
storage32_25 ds14({ou14s,ou14},{od14s,od14},se14,clk,reset);
storage32_25 ds15({ou15s,ou15},{od15s,od15},se15,clk,reset);
storage32_25 ds16({ou16s,ou16},{od16s,od16},se16,clk,reset);
storage32_25 ds17({ou17s,ou17},{od17s,od17},se17,clk,reset);
storage32_25 ds18({ou18s,ou18},{od18s,od18},se18,clk,reset);
storage32_25 ds19({ou19s,ou19},{od19s,od19},se19,clk,reset);
storage32_25 ds20({ou20s,ou20},{od20s,od20},se20,clk,reset);
storage32_25 ds21({ou21s,ou21},{od21s,od21},se21,clk,reset);
storage32_25 ds22({ou22s,ou22},{od22s,od22},se22,clk,reset);
storage32_25 ds23({ou23s,ou23},{od23s,od23},se23,clk,reset);
storage32_25 ds24({ou24s,ou24},{od24s,od24},se24,clk,reset);
storage32_25 ds25({ou25s,ou25},{od25s,od25},se25,clk,reset);
storage32_25 ds26({ou26s,ou26},{od26s,od26},se26,clk,reset);
storage32_25 ds27({ou27s,ou27},{od27s,od27},se27,clk,reset);
storage32_25 ds28({ou28s,ou28},{od28s,od28},se28,clk,reset);
storage32_25 ds29({ou29s,ou29},{od29s,od29},se29,clk,reset);
storage32_25 ds30({ou30s,ou30},{od30s,od30},se30,clk,reset);
storage32_25 ds31({ou31s,ou31},{od31s,od31},se31,clk,reset);

//column process

accumulator_npar_folded ddd(

od0s,od1s,od2s,od3s,od4s,od5s,od6s,od7s,od8s,od9s,od10s,od11s,od12s,od13s,od14s,od15s,
od16s,od17s,od18s,od19s,od20s,od21s,od22s,od23s,od24s,od25s,od26s,od27s,od28s,od29s,od30s,od31s,
{16'd0,od0},{16'd0,od1},{16'd0,od2},{16'd0,od3},{16'd0,od4},{16'd0,od5},{16'd0,od6},{16'd0,od7},{16'd0,od8},{16'd0,od9},{16'd0,od10},{16'd0,od11},{16'd0,od12},{16'd0,od13},{16'd0,od14},{16'd0,od15},{16'd0,od16},{16'd0,od17},{16'd0,od18},{16'd0,od19},{16'd0,od20},{16'd0,od21},{16'd0,od22},{16'd0,od23},{16'd0,od24},{16'd0,od25},{16'd0,od26},{16'd0,od27},{16'd0,od28},{16'd0,od29},{16'd0,od30},{16'd0,od31},
s,clk,reset,
oo0s,oo1s,oo2s,oo3s,oo4s,oo5s,oo6s,oo7s,oo8s,oo9s,oo10s,oo11s,oo12s,oo13s,oo14s,oo15s,
oo16s,oo17s,oo18s,oo19s,oo20s,oo21s,oo22s,oo23s,oo24s,oo25s,oo26s,oo27s,oo28s,oo29s,oo30s,oo31s,
oo0,oo1,oo2,oo3,oo4,oo5,oo6,oo7,oo8,oo9,oo10,oo11,oo12,oo13,oo14,oo15,oo16,oo17,oo18,oo19,oo20,oo21,oo22,oo23,oo24,oo25,oo26,oo27,oo28,oo29,oo30,oo31

);

endmodule


//accumulator based 1D DCT used for 2D parallel architecture (N-outputs at a time)
//area and throughput efficient IDCT/IDST architecutre for hevc standard

/*`include "adder24.v"
`include "kgp.v"
`include "kgp_carry.v"
`include "recursive_stage1.v"
`include "recurse24.v"
`include "add_shift_parallel.v"
`include "mux2to1_25.v"
`include "dflipflop25.v"*/

module accumulator_npar_parallel(

i0s,i1s,i2s,i3s,i4s,i5s,i6s,i7s,i8s,i9s,i10s,i11s,i12s,i13s,i14s,i15s,i16s,i17s,i18s,i19s,i20s,i21s,i22s,i23s,i24s,i25s,i26s,i27s,i28s,i29s,i30s,i31s,
i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,i24,i25,i26,i27,i28,i29,i30,i31,
s,clk,reset,

ou0s,ou1s,ou2s,ou3s,ou4s,ou5s,ou6s,ou7s,ou8s,ou9s,ou10s,ou11s,ou12s,ou13s,ou14s,ou15s,ou16s,ou17s,ou18s,ou19s,ou20s,ou21s,ou22s,ou23s,ou24s,ou25s,ou26s,ou27s,ou28s,ou29s,ou30s,ou31s,
ou0,ou1,ou2,ou3,ou4,ou5,ou6,ou7,ou8,ou9,ou10,ou11,ou12,ou13,ou14,ou15,ou16,ou17,ou18,ou19,ou20,ou21,ou22,ou23,ou24,ou25,ou26,ou27,ou28,ou29,ou30,ou31

);

input clk,reset;

input i0s,i1s,i2s,i3s,i4s,i5s,i6s,i7s,i8s,i9s,i10s,i11s,i12s,i13s,i14s,i15s,i16s,i17s,i18s,i19s,i20s,i21s,i22s,i23s,i24s,i25s,i26s,i27s,i28s,i29s,i30s,i31s;
input [7:0] i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,i24,i25,i26,i27,i28,i29,i30,i31;

input s;

output ou0s,ou1s,ou2s,ou3s,ou4s,ou5s,ou6s,ou7s,ou8s,ou9s,ou10s,ou11s,ou12s,ou13s,ou14s,ou15s,ou16s,ou17s,ou18s,ou19s,ou20s,ou21s,ou22s,ou23s,ou24s,ou25s,ou26s,ou27s,ou28s,ou29s,ou30s,ou31s;
output [23:0] ou0,ou1,ou2,ou3,ou4,ou5,ou6,ou7,ou8,ou9,ou10,ou11,ou12,ou13,ou14,ou15,ou16,ou17,ou18,ou19,ou20,ou21,ou22,ou23,ou24,ou25,ou26,ou27,ou28,ou29,ou30,ou31;

//stage1-add-shift n/w

wire z0s,z1s,z2s,z3s,z4s,z5s,z6s,z7s,z8s,z9s,z10s,z11s,z12s,z13s,z14s,z15s;
wire [23:0] z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15;

wire zz0s,zz1s,zz2s,zz3s,zz4s,zz5s,zz6s,zz7s,zz8s,zz9s,zz10s,zz11s,zz12s,zz13s,zz14s,zz15s;
wire [23:0] zz0,zz1,zz2,zz3,zz4,zz5,zz6,zz7,zz8,zz9,zz10,zz11,zz12,zz13,zz14,zz15;

add_shift_parallel sds0(i0s,z0s,{16'd0,i0},z0,s);
add_shift_parallel sds1(i1s,z1s,{16'd0,i1},z1,s);
add_shift_parallel sds2(i2s,z2s,{16'd0,i2},z2,s);
add_shift_parallel sds3(i3s,z3s,{16'd0,i3},z3,s);
add_shift_parallel sds4(i4s,z4s,{16'd0,i4},z4,s);
add_shift_parallel sds5(i5s,z5s,{16'd0,i5},z5,s);
add_shift_parallel sds6(i6s,z6s,{16'd0,i6},z6,s);
add_shift_parallel sds7(i7s,z7s,{16'd0,i7},z7,s);
add_shift_parallel sds8(i8s,z8s,{16'd0,i8},z8,s);
add_shift_parallel sds9(i9s,z9s,{16'd0,i9},z9,s);
add_shift_parallel sds10(i10s,z10s,{16'd0,i10},z10,s);
add_shift_parallel sds11(i11s,z11s,{16'd0,i11},z11,s);
add_shift_parallel sds12(i12s,z12s,{16'd0,i12},z12,s);
add_shift_parallel sds13(i13s,z13s,{16'd0,i13},z13,s);
add_shift_parallel sds14(i14s,z14s,{16'd0,i14},z14,s);
add_shift_parallel sds15(i15s,z15s,{16'd0,i15},z15,s);

add_shift_parallel ss0(i16s,zz0s,{16'd0,i16},zz0,s);
add_shift_parallel ss1(i17s,zz1s,{16'd0,i17},zz1,s);
add_shift_parallel ss2(i18s,zz2s,{16'd0,i18},zz2,s);
add_shift_parallel ss3(i19s,zz3s,{16'd0,i19},zz3,s);
add_shift_parallel ss4(i20s,zz4s,{16'd0,i20},zz4,s);
add_shift_parallel ss5(i21s,zz5s,{16'd0,i21},zz5,s);
add_shift_parallel ss6(i22s,zz6s,{16'd0,i22},zz6,s);
add_shift_parallel ss7(i23s,zz7s,{16'd0,i23},zz7,s);
add_shift_parallel ss8(i24s,zz8s,{16'd0,i24},zz8,s);
add_shift_parallel ss9(i25s,zz9s,{16'd0,i25},zz9,s);
add_shift_parallel ss10(i26s,zz10s,{16'd0,i26},zz10,s);
add_shift_parallel ss11(i27s,zz11s,{16'd0,i27},zz11,s);
add_shift_parallel ss12(i28s,zz12s,{16'd0,i28},zz12,s);
add_shift_parallel ss13(i29s,zz13s,{16'd0,i29},zz13,s);
add_shift_parallel ss14(i30s,zz14s,{16'd0,i30},zz14,s);
add_shift_parallel ss15(i31s,zz15s,{16'd0,i31},zz15,s);

//stage2-accumulators

wire o0s,o1s,o2s,o3s,o4s,o5s,o6s,o7s,o8s,o9s,o10s,o11s,o12s,o13s,o14s,o15s,o16s,o17s,o18s,o19s,o20s,o21s,o22s,o23s,o24s,o25s,o26s,o27s,o28s,o29s,o30s,o31s;
wire [23:0] o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11,o12,o13,o14,o15,o16,o17,o18,o19,o20,o21,o22,o23,o24,o25,o26,o27,o28,o29,o30,o31;

adder24 ad00(z0s,z0,ou0s,ou0,o0s,o0);
adder24 ad01(z1s,z1,ou1s,ou1,o1s,o1);
adder24 ad02(z2s,z2,ou2s,ou2,o2s,o2);
adder24 ad03(z3s,z3,ou3s,ou3,o3s,o3);
adder24 ad04(z4s,z4,ou4s,ou4,o4s,o4);
adder24 ad05(z5s,z5,ou5s,ou5,o5s,o5);
adder24 ad06(z6s,z6,ou6s,ou6,o6s,o6);
adder24 ad07(z7s,z7,ou7s,ou7,o7s,o7);
adder24 ad08(z8s,z8,ou8s,ou8,o8s,o8);
adder24 ad09(z9s,z9,ou9s,ou9,o9s,o9);
adder24 ad10(z10s,z10,ou10s,ou10,o10s,o10);
adder24 ad11(z11s,z11,ou11s,ou11,o11s,o11);
adder24 ad12(z12s,z12,ou12s,ou12,o12s,o12);
adder24 ad13(z13s,z13,ou13s,ou13,o13s,o13);
adder24 ad14(z14s,z14,ou14s,ou14,o14s,o14);
adder24 ad15(z15s,z15,ou15s,ou15,o15s,o15);

adder24 ad16(zz0s,zz0,ou16s,ou16,o16s,o16);
adder24 ad17(zz1s,zz1,ou17s,ou17,o17s,o17);
adder24 ad18(zz2s,zz2,ou18s,ou18,o18s,o18);
adder24 ad19(zz3s,zz3,ou19s,ou19,o19s,o19);
adder24 ad20(zz4s,zz4,ou20s,ou20,o20s,o20);
adder24 ad21(zz5s,zz5,ou21s,ou21,o21s,o21);
adder24 ad22(zz6s,zz6,ou22s,ou22,o22s,o22);
adder24 ad23(zz7s,zz7,ou23s,ou23,o23s,o23);
adder24 ad24(zz8s,zz8,ou24s,ou24,o24s,o24);
adder24 ad25(zz9s,zz9,ou25s,ou25,o25s,o25);
adder24 ad26(zz10s,zz10,ou26s,ou26,o26s,o26);
adder24 ad27(zz11s,zz11,ou27s,ou27,o27s,o27);
adder24 ad28(zz12s,zz12,ou28s,ou28,o28s,o28);
adder24 ad29(zz13s,zz13,ou29s,ou29,o29s,o29);
adder24 ad30(zz14s,zz14,ou30s,ou30,o30s,o30);
adder24 ad31(zz15s,zz15,ou31s,ou31,o31s,o31);


dflipflop25 df00({ou0s,ou0},{o0s,o0},clk,reset);
dflipflop25 df01({ou1s,ou1},{o1s,o1},clk,reset);
dflipflop25 df02({ou2s,ou2},{o2s,o2},clk,reset);
dflipflop25 df03({ou3s,ou3},{o3s,o3},clk,reset);
dflipflop25 df04({ou4s,ou4},{o4s,o4},clk,reset);
dflipflop25 df05({ou5s,ou5},{o5s,o5},clk,reset);
dflipflop25 df06({ou6s,ou6},{o6s,o6},clk,reset);
dflipflop25 df07({ou7s,ou7},{o7s,o7},clk,reset);
dflipflop25 df08({ou8s,ou8},{o8s,o8},clk,reset);
dflipflop25 df09({ou9s,ou9},{o9s,o9},clk,reset);
dflipflop25 df10({ou10s,ou10},{o10s,o10},clk,reset);
dflipflop25 df11({ou11s,ou11},{o11s,o11},clk,reset);
dflipflop25 df12({ou12s,ou12},{o12s,o12},clk,reset);
dflipflop25 df13({ou13s,ou13},{o13s,o13},clk,reset);
dflipflop25 df14({ou14s,ou14},{o14s,o14},clk,reset);
dflipflop25 df15({ou15s,ou15},{o15s,o15},clk,reset);
dflipflop25 df16({ou16s,ou16},{o16s,o16},clk,reset);
dflipflop25 df17({ou17s,ou17},{o17s,o17},clk,reset);
dflipflop25 df18({ou18s,ou18},{o18s,o18},clk,reset);
dflipflop25 df19({ou19s,ou19},{o19s,o19},clk,reset);
dflipflop25 df20({ou20s,ou20},{o20s,o20},clk,reset);
dflipflop25 df21({ou21s,ou21},{o21s,o21},clk,reset);
dflipflop25 df22({ou22s,ou22},{o22s,o22},clk,reset);
dflipflop25 df23({ou23s,ou23},{o23s,o23},clk,reset);
dflipflop25 df24({ou24s,ou24},{o24s,o24},clk,reset);
dflipflop25 df25({ou25s,ou25},{o25s,o25},clk,reset);
dflipflop25 df26({ou26s,ou26},{o26s,o26},clk,reset);
dflipflop25 df27({ou27s,ou27},{o27s,o27},clk,reset);
dflipflop25 df28({ou28s,ou28},{o28s,o28},clk,reset);
dflipflop25 df29({ou29s,ou29},{o29s,o29},clk,reset);
dflipflop25 df30({ou30s,ou30},{o30s,o30},clk,reset);
dflipflop25 df31({ou31s,ou31},{o31s,o31},clk,reset);


endmodule




//add shift network used for accumulator based integer DCT

//`include "kgp.v"
//`include "kgp_carry.v"
//`include "recursive_stage1.v"
//`include "recurse24.v"
//`include "mux2to1_25.v"

module add_shift_parallel(xs,ys,x,y,sel);

input xs,sel;
output ys;
input [23:0] x;
output [23:0] y;

wire [23:0] s1,s2,s3,s4,s5,s6,s7;
wire c1,c2,c3,c4,c5,c6,c7;

recurse24 r1(s1,c1,{6'b0,x[23:6]},{4'b0,x[23:4]}); 
recurse24 r2(s2,c2,{2'b0,x[23:2]},{1'b0,x[23:1]});
recurse24 r3(s3,c3,s1,s2);
recurse24 r4(s4,c4,s3,x);

recurse24 r5(s5,c5,s4,x);

recurse24 r6(s6,c6,s5,x);

adder24 ad24(xs,s6,xs,x,c7,s7);

mux2to1_25 m1({ys,y},{xs,s6},{c7,s7},sel);


endmodule

//24 bit fixed point adder

//`include "recurse24.v"
//`include "kgp.v"
//`include "kgp_carry.v"
//`include "recursive_stage1.v"

module adder24(as,a,bs,in_b,rrs,rr);

input as,bs;
input [23:0] a,in_b;
output rrs;
output [23:0] rr;

reg rrs;
reg [23:0] rr;
wire z;
assign z=as^bs;
wire cout,cout1;

wire [23:0] r1,b1,b2;
assign b1=(~in_b);

recurse24 c0(b2,cout1,b1,24'b000000000000000000000001);

reg [23:0] b;

always@(z or in_b or b2)
	begin
		if(z==0)
			b=in_b;
		else if (z==1)
			b=b2;
	end
	
recurse24 c1(r1,cout,a,b);

wire cout2;
wire [23:0] r11,r22;
assign r11=(~r1);
recurse24 c2(r22,cout2,r11,24'b000000000000000000000001);

reg carry;
always@(r1 or cout or z or as or bs or r22)
 begin
	if(z==0)	
		begin
			rrs=as;
			rr=r1;
			carry=cout;
		end
	else if (z==1 && cout==1)
		begin	
			rrs=as;
			rr=r1;
			carry=1'b0;
		end
	else if (z==1 && cout==0)
		begin
			rrs=(~as);
			rr=r22;
			carry=1'b0;
		end
 end

endmodule


//24 bit recursive doubling technique

module recurse24(sum,carry,a,b); 

output [23:0] sum;
output  carry;
input [23:0] a,b;

wire [49:0] x;

assign x[1:0]=2'b00;  // kgp generation

kgp a00(a[0],b[0],x[3:2]);
kgp a01(a[1],b[1],x[5:4]);
kgp a02(a[2],b[2],x[7:6]);
kgp a03(a[3],b[3],x[9:8]);
kgp a04(a[4],b[4],x[11:10]);
kgp a05(a[5],b[5],x[13:12]);
kgp a06(a[6],b[6],x[15:14]);
kgp a07(a[7],b[7],x[17:16]);
kgp a08(a[8],b[8],x[19:18]);
kgp a09(a[9],b[9],x[21:20]);
kgp a10(a[10],b[10],x[23:22]);
kgp a11(a[11],b[11],x[25:24]);
kgp a12(a[12],b[12],x[27:26]);
kgp a13(a[13],b[13],x[29:28]);
kgp a14(a[14],b[14],x[31:30]);
kgp a15(a[15],b[15],x[33:32]);
kgp a16(a[16],b[16],x[35:34]);
kgp a17(a[17],b[17],x[37:36]);
kgp a18(a[18],b[18],x[39:38]);
kgp a19(a[19],b[19],x[41:40]);
kgp a20(a[20],b[20],x[43:42]);
kgp a21(a[21],b[21],x[45:44]);
kgp a22(a[22],b[22],x[47:46]);
kgp a23(a[23],b[23],x[49:48]);

wire [49:0] x1;  //recursive doubling stage 1
assign x1[1:0]=x[1:0];

recursive_stage1 s00(x[1:0],x[3:2],x1[3:2]);
recursive_stage1 s01(x[3:2],x[5:4],x1[5:4]);
recursive_stage1 s02(x[5:4],x[7:6],x1[7:6]);
recursive_stage1 s03(x[7:6],x[9:8],x1[9:8]);
recursive_stage1 s04(x[9:8],x[11:10],x1[11:10]);
recursive_stage1 s05(x[11:10],x[13:12],x1[13:12]);
recursive_stage1 s06(x[13:12],x[15:14],x1[15:14]);
recursive_stage1 s07(x[15:14],x[17:16],x1[17:16]);
recursive_stage1 s08(x[17:16],x[19:18],x1[19:18]);
recursive_stage1 s09(x[19:18],x[21:20],x1[21:20]);
recursive_stage1 s10(x[21:20],x[23:22],x1[23:22]);
recursive_stage1 s11(x[23:22],x[25:24],x1[25:24]);
recursive_stage1 s12(x[25:24],x[27:26],x1[27:26]);
recursive_stage1 s13(x[27:26],x[29:28],x1[29:28]);
recursive_stage1 s14(x[29:28],x[31:30],x1[31:30]);
recursive_stage1 s15(x[31:30],x[33:32],x1[33:32]);
recursive_stage1 s16(x[33:32],x[35:34],x1[35:34]);
recursive_stage1 s17(x[35:34],x[37:36],x1[37:36]);
recursive_stage1 s18(x[37:36],x[39:38],x1[39:38]);
recursive_stage1 s19(x[39:38],x[41:40],x1[41:40]);
recursive_stage1 s20(x[41:40],x[43:42],x1[43:42]);
recursive_stage1 s21(x[43:42],x[45:44],x1[45:44]);
recursive_stage1 s22(x[45:44],x[47:46],x1[47:46]);
recursive_stage1 s23(x[47:46],x[49:48],x1[49:48]);

wire [49:0] x2;  //recursive doubling stage2
assign x2[3:0]=x1[3:0];

recursive_stage1 s101(x1[1:0],x1[5:4],x2[5:4]);
recursive_stage1 s102(x1[3:2],x1[7:6],x2[7:6]);
recursive_stage1 s103(x1[5:4],x1[9:8],x2[9:8]);
recursive_stage1 s104(x1[7:6],x1[11:10],x2[11:10]);
recursive_stage1 s105(x1[9:8],x1[13:12],x2[13:12]);
recursive_stage1 s106(x1[11:10],x1[15:14],x2[15:14]);
recursive_stage1 s107(x1[13:12],x1[17:16],x2[17:16]);
recursive_stage1 s108(x1[15:14],x1[19:18],x2[19:18]);
recursive_stage1 s109(x1[17:16],x1[21:20],x2[21:20]);
recursive_stage1 s110(x1[19:18],x1[23:22],x2[23:22]);
recursive_stage1 s111(x1[21:20],x1[25:24],x2[25:24]);
recursive_stage1 s112(x1[23:22],x1[27:26],x2[27:26]);
recursive_stage1 s113(x1[25:24],x1[29:28],x2[29:28]);
recursive_stage1 s114(x1[27:26],x1[31:30],x2[31:30]);
recursive_stage1 s115(x1[29:28],x1[33:32],x2[33:32]);
recursive_stage1 s116(x1[31:30],x1[35:34],x2[35:34]);
recursive_stage1 s117(x1[33:32],x1[37:36],x2[37:36]);
recursive_stage1 s118(x1[35:34],x1[39:38],x2[39:38]);
recursive_stage1 s119(x1[37:36],x1[41:40],x2[41:40]);
recursive_stage1 s120(x1[39:38],x1[43:42],x2[43:42]);
recursive_stage1 s121(x1[41:40],x1[45:44],x2[45:44]);
recursive_stage1 s122(x1[43:42],x1[47:46],x2[47:46]);
recursive_stage1 s123(x1[45:44],x1[49:48],x2[49:48]);

wire [49:0] x3;  //recursive doubling stage3
assign x3[7:0]=x2[7:0];

recursive_stage1 s203(x2[1:0],x2[9:8],x3[9:8]);
recursive_stage1 s204(x2[3:2],x2[11:10],x3[11:10]);
recursive_stage1 s205(x2[5:4],x2[13:12],x3[13:12]);
recursive_stage1 s206(x2[7:6],x2[15:14],x3[15:14]);
recursive_stage1 s207(x2[9:8],x2[17:16],x3[17:16]);
recursive_stage1 s208(x2[11:10],x2[19:18],x3[19:18]);
recursive_stage1 s209(x2[13:12],x2[21:20],x3[21:20]);
recursive_stage1 s210(x2[15:14],x2[23:22],x3[23:22]);
recursive_stage1 s211(x2[17:16],x2[25:24],x3[25:24]);
recursive_stage1 s212(x2[19:18],x2[27:26],x3[27:26]);
recursive_stage1 s213(x2[21:20],x2[29:28],x3[29:28]);
recursive_stage1 s214(x2[23:22],x2[31:30],x3[31:30]);
recursive_stage1 s215(x2[25:24],x2[33:32],x3[33:32]);
recursive_stage1 s216(x2[27:26],x2[35:34],x3[35:34]);
recursive_stage1 s217(x2[29:28],x2[37:36],x3[37:36]);
recursive_stage1 s218(x2[31:30],x2[39:38],x3[39:38]);
recursive_stage1 s219(x2[33:32],x2[41:40],x3[41:40]);
recursive_stage1 s220(x2[35:34],x2[43:42],x3[43:42]);
recursive_stage1 s221(x2[37:36],x2[45:44],x3[45:44]);
recursive_stage1 s222(x2[39:38],x2[47:46],x3[47:46]);
recursive_stage1 s223(x2[41:40],x2[49:48],x3[49:48]);

wire [49:0] x4;  //recursive doubling stage 4
assign x4[15:0]=x3[15:0];

recursive_stage1 s307(x3[1:0],x3[17:16],x4[17:16]);
recursive_stage1 s308(x3[3:2],x3[19:18],x4[19:18]);
recursive_stage1 s309(x3[5:4],x3[21:20],x4[21:20]);
recursive_stage1 s310(x3[7:6],x3[23:22],x4[23:22]);
recursive_stage1 s311(x3[9:8],x3[25:24],x4[25:24]);
recursive_stage1 s312(x3[11:10],x3[27:26],x4[27:26]);
recursive_stage1 s313(x3[13:12],x3[29:28],x4[29:28]);
recursive_stage1 s314(x3[15:14],x3[31:30],x4[31:30]);
recursive_stage1 s315(x3[17:16],x3[33:32],x4[33:32]);
recursive_stage1 s316(x3[19:18],x3[35:34],x4[35:34]);
recursive_stage1 s317(x3[21:20],x3[37:36],x4[37:36]);
recursive_stage1 s318(x3[23:22],x3[39:38],x4[39:38]);
recursive_stage1 s319(x3[25:24],x3[41:40],x4[41:40]);
recursive_stage1 s320(x3[27:26],x3[43:42],x4[43:42]);
recursive_stage1 s321(x3[29:28],x3[45:44],x4[45:44]);
recursive_stage1 s322(x3[31:30],x3[47:46],x4[47:46]);
recursive_stage1 s323(x3[33:32],x3[49:48],x4[49:48]);

wire [49:0] x5;  //recursive doubling stage 5
assign x5[31:0]=x4[31:0];

recursive_stage1 s415(x4[1:0],x4[33:32],x5[33:32]);
recursive_stage1 s416(x4[3:2],x4[35:34],x5[35:34]);
recursive_stage1 s417(x4[5:4],x4[37:36],x5[37:36]);
recursive_stage1 s418(x4[7:6],x4[39:38],x5[39:38]);
recursive_stage1 s419(x4[9:8],x4[41:40],x5[41:40]);
recursive_stage1 s420(x4[11:10],x4[43:42],x5[43:42]);
recursive_stage1 s421(x4[13:12],x4[45:44],x5[45:44]);
recursive_stage1 s422(x4[15:14],x4[47:46],x5[47:46]);
recursive_stage1 s423(x4[17:16],x4[49:48],x5[49:48]);

 // final sum and carry

assign sum[0]=a[0]^b[0]^x5[0];
assign sum[1]=a[1]^b[1]^x5[2];
assign sum[2]=a[2]^b[2]^x5[4];
assign sum[3]=a[3]^b[3]^x5[6];
assign sum[4]=a[4]^b[4]^x5[8];
assign sum[5]=a[5]^b[5]^x5[10];
assign sum[6]=a[6]^b[6]^x5[12];
assign sum[7]=a[7]^b[7]^x5[14];
assign sum[8]=a[8]^b[8]^x5[16];
assign sum[9]=a[9]^b[9]^x5[18];
assign sum[10]=a[10]^b[10]^x5[20];
assign sum[11]=a[11]^b[11]^x5[22];
assign sum[12]=a[12]^b[12]^x5[24];
assign sum[13]=a[13]^b[13]^x5[26];
assign sum[14]=a[14]^b[14]^x5[28];
assign sum[15]=a[15]^b[15]^x5[30];
assign sum[16]=a[16]^b[16]^x5[32];
assign sum[17]=a[17]^b[17]^x5[34];
assign sum[18]=a[18]^b[18]^x5[36];
assign sum[19]=a[19]^b[19]^x5[38];
assign sum[20]=a[20]^b[20]^x5[40];
assign sum[21]=a[21]^b[21]^x5[42];
assign sum[22]=a[22]^b[22]^x5[44];
assign sum[23]=a[23]^b[23]^x5[46];

kgp_carry kkc(x[49:48],x5[47:46],carry);

endmodule


module recursive_stage1(a,b,y);

input [1:0] a,b;
output [1:0] y;

wire [1:0] y;
wire b0;
not n1(b0,b[1]);
wire f,g0,g1;
and a1(f,b[0],b[1]);
and a2(g0,b0,b[0],a[0]);
and a3(g1,b0,b[0],a[1]);

or o1(y[0],f,g0);
or o2(y[1],f,g1);

//reg [1:0] y;
//always@(a or b)
//begin
//case(b)
//2'b00:y=2'b00;  
//2'b11:y=2'b11;
//2'b01:y=a;
//default:y=2'bx;
//endcase
//end

//always@(a or b)
//begin
//if(b==2'b00)
//	y=2'b00;  
//else if (b==2'b11)
//	y=2'b11;
//else if (b==2'b01)
//	y=a;
//end

//wire x;
//assign x=a[0] ^ b[0];
//always@(a or b or x)
//begin
//case(x)
//1'b0:y[0]=b[0];  
//1'b1:y[0]=a[0]; 
//endcase
//end
//
//always@(a or b or x)
//begin
//case(x)
//1'b0:y[1]=b[1];  
//1'b1:y[1]=a[1];
//endcase
//end


//always@(a or b)
//begin
//if (b==2'b00)
//	y=2'b00; 
//else if (b==2'b11)	
//	y=2'b11;
//else if (b==2'b01 && a==2'b00)
//	y=2'b00;
//else if (b==2'b01 && a==2'b11)
//	y=2'b11;
//else if (b==2'b01 && a==2'b01)
//	y=2'b01;
//end

endmodule



module kgp(a,b,y);

input a,b;
output [1:0] y;
//reg [1:0] y;

//always@(a or b)
//begin
//case({a,b})
//2'b00:y=2'b00;  //kill
//2'b11:y=2'b11;	  //generate
//2'b01:y=2'b01;	//propagate
//2'b10:y=2'b01;  //propagate
//endcase   //y[1]=ab  y[0]=a+b  
//end

assign y[0]=a | b;
assign y[1]=a & b;

endmodule



module kgp_carry(a,b,carry);

input [1:0] a,b;
output carry;
reg carry;

always@(a or b)
begin
case(a)
2'b00:carry=1'b0;  
2'b11:carry=1'b1;
2'b01:carry=b[0];
2'b10:carry=b[0];
default:carry=1'bx;
endcase
end

/*wire carry;

wire f,g;
assign g=a[0] & a[1];
assign f=a[0] ^ a[1];

assign carry=g|(b[0] & f);*/

endmodule

//2 to 1 multiplexer design

module mux2to1_25(out,i1,i2,s);

input [24:0] i1,i2;
input s;
output [24:0] out;
reg [24:0] out;

always@(i1 or i2 or s)
	begin
	 case(s)
	  1'b0:out=i1;
	  1'b1:out=i2;
	 endcase
	end

endmodule


// D flip flop

module dflipflop25(q,d,clk,reset);
output [24:0] q;
input [24:0] d;
input clk,reset;
reg [24:0] q;
always@(posedge reset or negedge clk)
if(reset)
q<=25'b00000000;
else
q<=d;
endmodule


//accumulator based 1D DCT used for 2D folded architecture (N-outputs at a time)
//area and throughput efficient IDCT/IDST architecutre for hevc standard

/*`include "adder40.v"
`include "kgp.v"
`include "kgp_carry.v"
`include "recursive_stage1.v"
`include "recurse40.v"
`include "add_shift_folded.v"
`include "mux2to1_41.v"
`include "dflipflop41.v"*/

module accumulator_npar_folded(

i0s,i1s,i2s,i3s,i4s,i5s,i6s,i7s,i8s,i9s,i10s,i11s,i12s,i13s,i14s,i15s,i16s,i17s,i18s,i19s,i20s,i21s,i22s,i23s,i24s,i25s,i26s,i27s,i28s,i29s,i30s,i31s,
i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,i24,i25,i26,i27,i28,i29,i30,i31,
s,clk,reset,

ou0s,ou1s,ou2s,ou3s,ou4s,ou5s,ou6s,ou7s,ou8s,ou9s,ou10s,ou11s,ou12s,ou13s,ou14s,ou15s,ou16s,ou17s,ou18s,ou19s,ou20s,ou21s,ou22s,ou23s,ou24s,ou25s,ou26s,ou27s,ou28s,ou29s,ou30s,ou31s,
ou0,ou1,ou2,ou3,ou4,ou5,ou6,ou7,ou8,ou9,ou10,ou11,ou12,ou13,ou14,ou15,ou16,ou17,ou18,ou19,ou20,ou21,ou22,ou23,ou24,ou25,ou26,ou27,ou28,ou29,ou30,ou31

);

input clk,reset;

input i0s,i1s,i2s,i3s,i4s,i5s,i6s,i7s,i8s,i9s,i10s,i11s,i12s,i13s,i14s,i15s,i16s,i17s,i18s,i19s,i20s,i21s,i22s,i23s,i24s,i25s,i26s,i27s,i28s,i29s,i30s,i31s;
input [39:0] i0,i1,i2,i3,i4,i5,i6,i7,i8,i9,i10,i11,i12,i13,i14,i15,i16,i17,i18,i19,i20,i21,i22,i23,i24,i25,i26,i27,i28,i29,i30,i31;

input s;

output ou0s,ou1s,ou2s,ou3s,ou4s,ou5s,ou6s,ou7s,ou8s,ou9s,ou10s,ou11s,ou12s,ou13s,ou14s,ou15s,ou16s,ou17s,ou18s,ou19s,ou20s,ou21s,ou22s,ou23s,ou24s,ou25s,ou26s,ou27s,ou28s,ou29s,ou30s,ou31s;
output [39:0] ou0,ou1,ou2,ou3,ou4,ou5,ou6,ou7,ou8,ou9,ou10,ou11,ou12,ou13,ou14,ou15,ou16,ou17,ou18,ou19,ou20,ou21,ou22,ou23,ou24,ou25,ou26,ou27,ou28,ou29,ou30,ou31;

//stage1-add-shift n/w

wire z0s,z1s,z2s,z3s,z4s,z5s,z6s,z7s,z8s,z9s,z10s,z11s,z12s,z13s,z14s,z15s;
wire [39:0] z0,z1,z2,z3,z4,z5,z6,z7,z8,z9,z10,z11,z12,z13,z14,z15;

wire zz0s,zz1s,zz2s,zz3s,zz4s,zz5s,zz6s,zz7s,zz8s,zz9s,zz10s,zz11s,zz12s,zz13s,zz14s,zz15s;
wire [39:0] zz0,zz1,zz2,zz3,zz4,zz5,zz6,zz7,zz8,zz9,zz10,zz11,zz12,zz13,zz14,zz15;

add_shift_folded sds0(i0s,z0s,i0,z0,s);
add_shift_folded sds1(i1s,z1s,i1,z1,s);
add_shift_folded sds2(i2s,z2s,i2,z2,s);
add_shift_folded sds3(i3s,z3s,i3,z3,s);
add_shift_folded sds4(i4s,z4s,i4,z4,s);
add_shift_folded sds5(i5s,z5s,i5,z5,s);
add_shift_folded sds6(i6s,z6s,i6,z6,s);
add_shift_folded sds7(i7s,z7s,i7,z7,s);
add_shift_folded sds8(i8s,z8s,i8,z8,s);
add_shift_folded sds9(i9s,z9s,i9,z9,s);
add_shift_folded sds10(i10s,z10s,i10,z10,s);
add_shift_folded sds11(i11s,z11s,i11,z11,s);
add_shift_folded sds12(i12s,z12s,i12,z12,s);
add_shift_folded sds13(i13s,z13s,i13,z13,s);
add_shift_folded sds14(i14s,z14s,i14,z14,s);
add_shift_folded sds15(i15s,z15s,i15,z15,s);

add_shift_folded ss0(i16s,zz0s,i16,zz0,s);
add_shift_folded ss1(i17s,zz1s,i17,zz1,s);
add_shift_folded ss2(i18s,zz2s,i18,zz2,s);
add_shift_folded ss3(i19s,zz3s,i19,zz3,s);
add_shift_folded ss4(i20s,zz4s,i20,zz4,s);
add_shift_folded ss5(i21s,zz5s,i21,zz5,s);
add_shift_folded ss6(i22s,zz6s,i22,zz6,s);
add_shift_folded ss7(i23s,zz7s,i23,zz7,s);
add_shift_folded ss8(i24s,zz8s,i24,zz8,s);
add_shift_folded ss9(i25s,zz9s,i25,zz9,s);
add_shift_folded ss10(i26s,zz10s,i26,zz10,s);
add_shift_folded ss11(i27s,zz11s,i27,zz11,s);
add_shift_folded ss12(i28s,zz12s,i28,zz12,s);
add_shift_folded ss13(i29s,zz13s,i29,zz13,s);
add_shift_folded ss14(i30s,zz14s,i30,zz14,s);
add_shift_folded ss15(i31s,zz15s,i31,zz15,s);

//stage2-accumulators

wire o0s,o1s,o2s,o3s,o4s,o5s,o6s,o7s,o8s,o9s,o10s,o11s,o12s,o13s,o14s,o15s,o16s,o17s,o18s,o19s,o20s,o21s,o22s,o23s,o24s,o25s,o26s,o27s,o28s,o29s,o30s,o31s;
wire [39:0] o0,o1,o2,o3,o4,o5,o6,o7,o8,o9,o10,o11,o12,o13,o14,o15,o16,o17,o18,o19,o20,o21,o22,o23,o24,o25,o26,o27,o28,o29,o30,o31;

adder40 ad00(z0s,z0,ou0s,ou0,o0s,o0);
adder40 ad01(z1s,z1,ou1s,ou1,o1s,o1);
adder40 ad02(z2s,z2,ou2s,ou2,o2s,o2);
adder40 ad03(z3s,z3,ou3s,ou3,o3s,o3);
adder40 ad04(z4s,z4,ou4s,ou4,o4s,o4);
adder40 ad05(z5s,z5,ou5s,ou5,o5s,o5);
adder40 ad06(z6s,z6,ou6s,ou6,o6s,o6);
adder40 ad07(z7s,z7,ou7s,ou7,o7s,o7);
adder40 ad08(z8s,z8,ou8s,ou8,o8s,o8);
adder40 ad09(z9s,z9,ou9s,ou9,o9s,o9);
adder40 ad10(z10s,z10,ou10s,ou10,o10s,o10);
adder40 ad11(z11s,z11,ou11s,ou11,o11s,o11);
adder40 ad12(z12s,z12,ou12s,ou12,o12s,o12);
adder40 ad13(z13s,z13,ou13s,ou13,o13s,o13);
adder40 ad14(z14s,z14,ou14s,ou14,o14s,o14);
adder40 ad15(z15s,z15,ou15s,ou15,o15s,o15);

adder40 ad16(zz0s,zz0,ou16s,ou16,o16s,o16);
adder40 ad17(zz1s,zz1,ou17s,ou17,o17s,o17);
adder40 ad18(zz2s,zz2,ou18s,ou18,o18s,o18);
adder40 ad19(zz3s,zz3,ou19s,ou19,o19s,o19);
adder40 ad20(zz4s,zz4,ou20s,ou20,o20s,o20);
adder40 ad21(zz5s,zz5,ou21s,ou21,o21s,o21);
adder40 ad22(zz6s,zz6,ou22s,ou22,o22s,o22);
adder40 ad23(zz7s,zz7,ou23s,ou23,o23s,o23);
adder40 ad24(zz8s,zz8,ou24s,ou24,o24s,o24);
adder40 ad25(zz9s,zz9,ou25s,ou25,o25s,o25);
adder40 ad26(zz10s,zz10,ou26s,ou26,o26s,o26);
adder40 ad27(zz11s,zz11,ou27s,ou27,o27s,o27);
adder40 ad28(zz12s,zz12,ou28s,ou28,o28s,o28);
adder40 ad29(zz13s,zz13,ou29s,ou29,o29s,o29);
adder40 ad30(zz14s,zz14,ou30s,ou30,o30s,o30);
adder40 ad31(zz15s,zz15,ou31s,ou31,o31s,o31);


dflipflop41 df00({ou0s,ou0},{o0s,o0},clk,reset);
dflipflop41 df01({ou1s,ou1},{o1s,o1},clk,reset);
dflipflop41 df02({ou2s,ou2},{o2s,o2},clk,reset);
dflipflop41 df03({ou3s,ou3},{o3s,o3},clk,reset);
dflipflop41 df04({ou4s,ou4},{o4s,o4},clk,reset);
dflipflop41 df05({ou5s,ou5},{o5s,o5},clk,reset);
dflipflop41 df06({ou6s,ou6},{o6s,o6},clk,reset);
dflipflop41 df07({ou7s,ou7},{o7s,o7},clk,reset);
dflipflop41 df08({ou8s,ou8},{o8s,o8},clk,reset);
dflipflop41 df09({ou9s,ou9},{o9s,o9},clk,reset);
dflipflop41 df10({ou10s,ou10},{o10s,o10},clk,reset);
dflipflop41 df11({ou11s,ou11},{o11s,o11},clk,reset);
dflipflop41 df12({ou12s,ou12},{o12s,o12},clk,reset);
dflipflop41 df13({ou13s,ou13},{o13s,o13},clk,reset);
dflipflop41 df14({ou14s,ou14},{o14s,o14},clk,reset);
dflipflop41 df15({ou15s,ou15},{o15s,o15},clk,reset);
dflipflop41 df16({ou16s,ou16},{o16s,o16},clk,reset);
dflipflop41 df17({ou17s,ou17},{o17s,o17},clk,reset);
dflipflop41 df18({ou18s,ou18},{o18s,o18},clk,reset);
dflipflop41 df19({ou19s,ou19},{o19s,o19},clk,reset);
dflipflop41 df20({ou20s,ou20},{o20s,o20},clk,reset);
dflipflop41 df21({ou21s,ou21},{o21s,o21},clk,reset);
dflipflop41 df22({ou22s,ou22},{o22s,o22},clk,reset);
dflipflop41 df23({ou23s,ou23},{o23s,o23},clk,reset);
dflipflop41 df24({ou24s,ou24},{o24s,o24},clk,reset);
dflipflop41 df25({ou25s,ou25},{o25s,o25},clk,reset);
dflipflop41 df26({ou26s,ou26},{o26s,o26},clk,reset);
dflipflop41 df27({ou27s,ou27},{o27s,o27},clk,reset);
dflipflop41 df28({ou28s,ou28},{o28s,o28},clk,reset);
dflipflop41 df29({ou29s,ou29},{o29s,o29},clk,reset);
dflipflop41 df30({ou30s,ou30},{o30s,o30},clk,reset);
dflipflop41 df31({ou31s,ou31},{o31s,o31},clk,reset);


endmodule



//add shift network used for odd/even decomposed based integer DCT

//`include "kgp.v"
//`include "kgp_carry.v"
//`include "recursive_stage1.v"
//`include "recurse40.v"
//`include "mux2to1_41.v"

module add_shift_folded(xs,ys,x,y,sel);

input xs,sel;
output ys;
input [39:0] x;
output [39:0] y;

wire [39:0] s1,s2,s3,s4,s5,s6,s7;
wire c1,c2,c3,c4,c5,c6,c7;

recurse40 r1(s1,c1,{6'b0,x[39:6]},{4'b0,x[39:4]}); 
recurse40 r2(s2,c2,{2'b0,x[39:2]},{1'b0,x[39:1]});
recurse40 r3(s3,c3,s1,s2);
recurse40 r4(s4,c4,s3,x);

recurse40 r5(s5,c5,s4,x);

recurse40 r6(s6,c6,s5,x);

adder40 ad24(xs,s6,xs,x,c7,s7);

mux2to1_41 m1({ys,y},{xs,s6},{c7,s7},sel);


endmodule

//40 bit fixed point adder

//`include "recurse40.v"
//`include "kgp.v"
//`include "kgp_carry.v"
//`include "recursive_stage1.v"

module adder40(as,a,bs,in_b,rrs,rr);

input as,bs;
input [39:0] a,in_b;
output rrs;
output [39:0] rr;

reg rrs;
reg [39:0] rr;
wire z;
assign z=as^bs;
wire cout,cout1;

wire [39:0] r1,b1,b2;
assign b1=(~in_b);

recurse40 c0(b2,cout1,b1,40'd1);

reg [39:0] b;

always@(z or in_b or b2)
	begin
		if(z==0)
			b=in_b;
		else if (z==1)
			b=b2;
	end
	
recurse40 c1(r1,cout,a,b);

wire cout2;
wire [39:0] r11,r22;
assign r11=(~r1);
recurse40 c2(r22,cout2,r11,40'd1);

reg carry;
always@(r1 or cout or z or as or bs or r22)
 begin
	if(z==0)	
		begin
			rrs=as;
			rr=r1;
			carry=cout;
		end
	else if (z==1 && cout==1)
		begin	
			rrs=as;
			rr=r1;
			carry=1'b0;
		end
	else if (z==1 && cout==0)
		begin
			rrs=(~as);
			rr=r22;
			carry=1'b0;
		end
 end

endmodule



//40 bit recursive doubling technique

module recurse40(sum,carry,a,b); 

output [39:0] sum;
output  carry;
input [39:0] a,b;

wire [81:0] x;

assign x[1:0]=2'b00;  // kgp generation

kgp a00(a[0],b[0],x[3:2]);
kgp a01(a[1],b[1],x[5:4]);
kgp a02(a[2],b[2],x[7:6]);
kgp a03(a[3],b[3],x[9:8]);
kgp a04(a[4],b[4],x[11:10]);
kgp a05(a[5],b[5],x[13:12]);
kgp a06(a[6],b[6],x[15:14]);
kgp a07(a[7],b[7],x[17:16]);
kgp a08(a[8],b[8],x[19:18]);
kgp a09(a[9],b[9],x[21:20]);
kgp a10(a[10],b[10],x[23:22]);
kgp a11(a[11],b[11],x[25:24]);
kgp a12(a[12],b[12],x[27:26]);
kgp a13(a[13],b[13],x[29:28]);
kgp a14(a[14],b[14],x[31:30]);
kgp a15(a[15],b[15],x[33:32]);
kgp a16(a[16],b[16],x[35:34]);
kgp a17(a[17],b[17],x[37:36]);
kgp a18(a[18],b[18],x[39:38]);
kgp a19(a[19],b[19],x[41:40]);
kgp a20(a[20],b[20],x[43:42]);
kgp a21(a[21],b[21],x[45:44]);
kgp a22(a[22],b[22],x[47:46]);
kgp a23(a[23],b[23],x[49:48]);
kgp a24(a[24],b[24],x[51:50]);
kgp a25(a[25],b[25],x[53:52]);
kgp a26(a[26],b[26],x[55:54]);
kgp a27(a[27],b[27],x[57:56]);
kgp a28(a[28],b[28],x[59:58]);
kgp a29(a[29],b[29],x[61:60]);
kgp a30(a[30],b[30],x[63:62]);
kgp a31(a[31],b[31],x[65:64]);
kgp a32(a[32],b[32],x[67:66]);
kgp a33(a[33],b[33],x[69:68]);
kgp a34(a[34],b[34],x[71:70]);
kgp a35(a[35],b[35],x[73:72]);
kgp a36(a[36],b[36],x[75:74]);
kgp a37(a[37],b[37],x[77:76]);
kgp a38(a[38],b[38],x[79:78]);
kgp a39(a[39],b[39],x[81:80]);

wire [79:0] x1;  //recursive doubling stage 1
assign x1[1:0]=x[1:0];

recursive_stage1 s00(x[1:0],x[3:2],x1[3:2]);
recursive_stage1 s01(x[3:2],x[5:4],x1[5:4]);
recursive_stage1 s02(x[5:4],x[7:6],x1[7:6]);
recursive_stage1 s03(x[7:6],x[9:8],x1[9:8]);
recursive_stage1 s04(x[9:8],x[11:10],x1[11:10]);
recursive_stage1 s05(x[11:10],x[13:12],x1[13:12]);
recursive_stage1 s06(x[13:12],x[15:14],x1[15:14]);
recursive_stage1 s07(x[15:14],x[17:16],x1[17:16]);
recursive_stage1 s08(x[17:16],x[19:18],x1[19:18]);
recursive_stage1 s09(x[19:18],x[21:20],x1[21:20]);
recursive_stage1 s10(x[21:20],x[23:22],x1[23:22]);
recursive_stage1 s11(x[23:22],x[25:24],x1[25:24]);
recursive_stage1 s12(x[25:24],x[27:26],x1[27:26]);
recursive_stage1 s13(x[27:26],x[29:28],x1[29:28]);
recursive_stage1 s14(x[29:28],x[31:30],x1[31:30]);
recursive_stage1 s15(x[31:30],x[33:32],x1[33:32]);
recursive_stage1 s16(x[33:32],x[35:34],x1[35:34]);
recursive_stage1 s17(x[35:34],x[37:36],x1[37:36]);
recursive_stage1 s18(x[37:36],x[39:38],x1[39:38]);
recursive_stage1 s19(x[39:38],x[41:40],x1[41:40]);
recursive_stage1 s20(x[41:40],x[43:42],x1[43:42]);
recursive_stage1 s21(x[43:42],x[45:44],x1[45:44]);
recursive_stage1 s22(x[45:44],x[47:46],x1[47:46]);
recursive_stage1 s23(x[47:46],x[49:48],x1[49:48]);
recursive_stage1 s24(x[49:48],x[51:50],x1[51:50]);
recursive_stage1 s25(x[51:50],x[53:52],x1[53:52]);
recursive_stage1 s26(x[53:52],x[55:54],x1[55:54]);
recursive_stage1 s27(x[55:54],x[57:56],x1[57:56]);
recursive_stage1 s28(x[57:56],x[59:58],x1[59:58]);
recursive_stage1 s29(x[59:58],x[61:60],x1[61:60]);
recursive_stage1 s30(x[61:60],x[63:62],x1[63:62]);
recursive_stage1 s31(x[63:62],x[65:64],x1[65:64]);
recursive_stage1 s32(x[65:64],x[67:66],x1[67:66]);
recursive_stage1 s33(x[67:66],x[69:68],x1[69:68]);
recursive_stage1 s34(x[69:68],x[71:70],x1[71:70]);
recursive_stage1 s35(x[71:70],x[73:72],x1[73:72]);
recursive_stage1 s36(x[73:72],x[75:74],x1[75:74]);
recursive_stage1 s37(x[75:74],x[77:76],x1[77:76]);
recursive_stage1 s38(x[77:76],x[79:78],x1[79:78]);

wire [79:0] x2;  //recursive doubling stage2
assign x2[3:0]=x1[3:0];

recursive_stage1 s101(x1[1:0],x1[5:4],x2[5:4]);
recursive_stage1 s102(x1[3:2],x1[7:6],x2[7:6]);
recursive_stage1 s103(x1[5:4],x1[9:8],x2[9:8]);
recursive_stage1 s104(x1[7:6],x1[11:10],x2[11:10]);
recursive_stage1 s105(x1[9:8],x1[13:12],x2[13:12]);
recursive_stage1 s106(x1[11:10],x1[15:14],x2[15:14]);
recursive_stage1 s107(x1[13:12],x1[17:16],x2[17:16]);
recursive_stage1 s108(x1[15:14],x1[19:18],x2[19:18]);
recursive_stage1 s109(x1[17:16],x1[21:20],x2[21:20]);
recursive_stage1 s110(x1[19:18],x1[23:22],x2[23:22]);
recursive_stage1 s111(x1[21:20],x1[25:24],x2[25:24]);
recursive_stage1 s112(x1[23:22],x1[27:26],x2[27:26]);
recursive_stage1 s113(x1[25:24],x1[29:28],x2[29:28]);
recursive_stage1 s114(x1[27:26],x1[31:30],x2[31:30]);
recursive_stage1 s115(x1[29:28],x1[33:32],x2[33:32]);
recursive_stage1 s116(x1[31:30],x1[35:34],x2[35:34]);
recursive_stage1 s117(x1[33:32],x1[37:36],x2[37:36]);
recursive_stage1 s118(x1[35:34],x1[39:38],x2[39:38]);
recursive_stage1 s119(x1[37:36],x1[41:40],x2[41:40]);
recursive_stage1 s120(x1[39:38],x1[43:42],x2[43:42]);
recursive_stage1 s121(x1[41:40],x1[45:44],x2[45:44]);
recursive_stage1 s122(x1[43:42],x1[47:46],x2[47:46]);
recursive_stage1 s123(x1[45:44],x1[49:48],x2[49:48]);
recursive_stage1 s124(x1[47:46],x1[51:50],x2[51:50]);
recursive_stage1 s125(x1[49:48],x1[53:52],x2[53:52]);
recursive_stage1 s126(x1[51:50],x1[55:54],x2[55:54]);
recursive_stage1 s127(x1[53:52],x1[57:56],x2[57:56]);
recursive_stage1 s128(x1[55:54],x1[59:58],x2[59:58]);
recursive_stage1 s129(x1[57:56],x1[61:60],x2[61:60]);
recursive_stage1 s130(x1[59:58],x1[63:62],x2[63:62]);
recursive_stage1 s131(x1[61:60],x1[65:64],x2[65:64]);
recursive_stage1 s132(x1[63:62],x1[67:66],x2[67:66]);
recursive_stage1 s133(x1[65:64],x1[69:68],x2[69:68]);
recursive_stage1 s134(x1[67:66],x1[71:70],x2[71:70]);
recursive_stage1 s135(x1[69:68],x1[73:72],x2[73:72]);
recursive_stage1 s136(x1[71:70],x1[75:74],x2[75:74]);
recursive_stage1 s137(x1[73:72],x1[77:76],x2[77:76]);
recursive_stage1 s138(x1[75:74],x1[79:78],x2[79:78]);

wire [79:0] x3;  //recursive doubling stage3
assign x3[7:0]=x2[7:0];

recursive_stage1 s203(x2[1:0],x2[9:8],x3[9:8]);
recursive_stage1 s204(x2[3:2],x2[11:10],x3[11:10]);
recursive_stage1 s205(x2[5:4],x2[13:12],x3[13:12]);
recursive_stage1 s206(x2[7:6],x2[15:14],x3[15:14]);
recursive_stage1 s207(x2[9:8],x2[17:16],x3[17:16]);
recursive_stage1 s208(x2[11:10],x2[19:18],x3[19:18]);
recursive_stage1 s209(x2[13:12],x2[21:20],x3[21:20]);
recursive_stage1 s210(x2[15:14],x2[23:22],x3[23:22]);
recursive_stage1 s211(x2[17:16],x2[25:24],x3[25:24]);
recursive_stage1 s212(x2[19:18],x2[27:26],x3[27:26]);
recursive_stage1 s213(x2[21:20],x2[29:28],x3[29:28]);
recursive_stage1 s214(x2[23:22],x2[31:30],x3[31:30]);
recursive_stage1 s215(x2[25:24],x2[33:32],x3[33:32]);
recursive_stage1 s216(x2[27:26],x2[35:34],x3[35:34]);
recursive_stage1 s217(x2[29:28],x2[37:36],x3[37:36]);
recursive_stage1 s218(x2[31:30],x2[39:38],x3[39:38]);
recursive_stage1 s219(x2[33:32],x2[41:40],x3[41:40]);
recursive_stage1 s220(x2[35:34],x2[43:42],x3[43:42]);
recursive_stage1 s221(x2[37:36],x2[45:44],x3[45:44]);
recursive_stage1 s222(x2[39:38],x2[47:46],x3[47:46]);
recursive_stage1 s223(x2[41:40],x2[49:48],x3[49:48]);
recursive_stage1 s224(x2[43:42],x2[51:50],x3[51:50]);
recursive_stage1 s225(x2[45:44],x2[53:52],x3[53:52]);
recursive_stage1 s226(x2[47:46],x2[55:54],x3[55:54]);
recursive_stage1 s227(x2[49:48],x2[57:56],x3[57:56]);
recursive_stage1 s228(x2[51:50],x2[59:58],x3[59:58]);
recursive_stage1 s229(x2[53:52],x2[61:60],x3[61:60]);
recursive_stage1 s230(x2[55:54],x2[63:62],x3[63:62]);
recursive_stage1 s231(x2[57:56],x2[65:64],x3[65:64]);
recursive_stage1 s232(x2[59:58],x2[67:66],x3[67:66]);
recursive_stage1 s233(x2[61:60],x2[69:68],x3[69:68]);
recursive_stage1 s234(x2[63:62],x2[71:70],x3[71:70]);
recursive_stage1 s235(x2[65:64],x2[73:72],x3[73:72]);
recursive_stage1 s236(x2[67:66],x2[75:74],x3[75:74]);
recursive_stage1 s237(x2[69:68],x2[77:76],x3[77:76]);
recursive_stage1 s238(x2[71:70],x2[79:78],x3[79:78]);

wire [79:0] x4;  //recursive doubling stage 4
assign x4[15:0]=x3[15:0];

recursive_stage1 s307(x3[1:0],x3[17:16],x4[17:16]);
recursive_stage1 s308(x3[3:2],x3[19:18],x4[19:18]);
recursive_stage1 s309(x3[5:4],x3[21:20],x4[21:20]);
recursive_stage1 s310(x3[7:6],x3[23:22],x4[23:22]);
recursive_stage1 s311(x3[9:8],x3[25:24],x4[25:24]);
recursive_stage1 s312(x3[11:10],x3[27:26],x4[27:26]);
recursive_stage1 s313(x3[13:12],x3[29:28],x4[29:28]);
recursive_stage1 s314(x3[15:14],x3[31:30],x4[31:30]);
recursive_stage1 s315(x3[17:16],x3[33:32],x4[33:32]);
recursive_stage1 s316(x3[19:18],x3[35:34],x4[35:34]);
recursive_stage1 s317(x3[21:20],x3[37:36],x4[37:36]);
recursive_stage1 s318(x3[23:22],x3[39:38],x4[39:38]);
recursive_stage1 s319(x3[25:24],x3[41:40],x4[41:40]);
recursive_stage1 s320(x3[27:26],x3[43:42],x4[43:42]);
recursive_stage1 s321(x3[29:28],x3[45:44],x4[45:44]);
recursive_stage1 s322(x3[31:30],x3[47:46],x4[47:46]);
recursive_stage1 s323(x3[33:32],x3[49:48],x4[49:48]);
recursive_stage1 s324(x3[35:34],x3[51:50],x4[51:50]);
recursive_stage1 s325(x3[37:36],x3[53:52],x4[53:52]);
recursive_stage1 s326(x3[39:38],x3[55:54],x4[55:54]);
recursive_stage1 s327(x3[41:40],x3[57:56],x4[57:56]);
recursive_stage1 s328(x3[43:42],x3[59:58],x4[59:58]);
recursive_stage1 s329(x3[45:44],x3[61:60],x4[61:60]);
recursive_stage1 s330(x3[47:46],x3[63:62],x4[63:62]);
recursive_stage1 s331(x3[49:48],x3[65:64],x4[65:64]);
recursive_stage1 s332(x3[51:50],x3[67:66],x4[67:66]);
recursive_stage1 s333(x3[53:52],x3[69:68],x4[69:68]);
recursive_stage1 s334(x3[55:54],x3[71:70],x4[71:70]);
recursive_stage1 s335(x3[57:56],x3[73:72],x4[73:72]);
recursive_stage1 s336(x3[59:58],x3[75:74],x4[75:74]);
recursive_stage1 s337(x3[61:60],x3[77:76],x4[77:76]);
recursive_stage1 s338(x3[63:62],x3[79:78],x4[79:78]);

wire [79:0] x5;  //recursive doubling stage 5
assign x5[31:0]=x4[31:0];

recursive_stage1 s415(x4[1:0],x4[33:32],x5[33:32]);
recursive_stage1 s416(x4[3:2],x4[35:34],x5[35:34]);
recursive_stage1 s417(x4[5:4],x4[37:36],x5[37:36]);
recursive_stage1 s418(x4[7:6],x4[39:38],x5[39:38]);
recursive_stage1 s419(x4[9:8],x4[41:40],x5[41:40]);
recursive_stage1 s420(x4[11:10],x4[43:42],x5[43:42]);
recursive_stage1 s421(x4[13:12],x4[45:44],x5[45:44]);
recursive_stage1 s422(x4[15:14],x4[47:46],x5[47:46]);
recursive_stage1 s423(x4[17:16],x4[49:48],x5[49:48]);
recursive_stage1 s424(x4[19:18],x4[51:50],x5[51:50]);
recursive_stage1 s425(x4[21:20],x4[53:52],x5[53:52]);
recursive_stage1 s426(x4[23:22],x4[55:54],x5[55:54]);
recursive_stage1 s427(x4[25:24],x4[57:56],x5[57:56]);
recursive_stage1 s428(x4[27:26],x4[59:58],x5[59:58]);
recursive_stage1 s429(x4[29:28],x4[61:60],x5[61:60]);
recursive_stage1 s430(x4[31:30],x4[63:62],x5[63:62]);
recursive_stage1 s431(x4[33:32],x4[65:64],x5[65:64]);
recursive_stage1 s432(x4[35:34],x4[67:66],x5[67:66]);
recursive_stage1 s433(x4[37:36],x4[69:68],x5[69:68]);
recursive_stage1 s434(x4[39:38],x4[71:70],x5[71:70]);
recursive_stage1 s435(x4[41:40],x4[73:72],x5[73:72]);
recursive_stage1 s436(x4[43:42],x4[75:74],x5[75:74]);
recursive_stage1 s437(x4[45:44],x4[77:76],x5[77:76]);
recursive_stage1 s438(x4[47:46],x4[79:78],x5[79:78]);

wire [79:0] x6;  // recursive doubling stage 6
assign x6[63:0]=x5[63:0];

recursive_stage1 s531(x5[1:0],x5[65:64],x6[65:64]);
recursive_stage1 s532(x5[3:2],x5[67:66],x6[67:66]);
recursive_stage1 s533(x5[5:4],x5[69:68],x6[69:68]);
recursive_stage1 s534(x5[7:6],x5[71:70],x6[71:70]);
recursive_stage1 s535(x5[9:8],x5[73:72],x6[73:72]);
recursive_stage1 s536(x5[11:10],x5[75:74],x6[75:74]);
recursive_stage1 s537(x5[13:12],x5[77:76],x6[77:76]);
recursive_stage1 s538(x5[15:14],x5[79:78],x6[79:78]);

// final sum and carry

assign sum[0]=a[0]^b[0]^x6[0];
assign sum[1]=a[1]^b[1]^x6[2];
assign sum[2]=a[2]^b[2]^x6[4];
assign sum[3]=a[3]^b[3]^x6[6];
assign sum[4]=a[4]^b[4]^x6[8];
assign sum[5]=a[5]^b[5]^x6[10];
assign sum[6]=a[6]^b[6]^x6[12];
assign sum[7]=a[7]^b[7]^x6[14];
assign sum[8]=a[8]^b[8]^x6[16];
assign sum[9]=a[9]^b[9]^x6[18];
assign sum[10]=a[10]^b[10]^x6[20];
assign sum[11]=a[11]^b[11]^x6[22];
assign sum[12]=a[12]^b[12]^x6[24];
assign sum[13]=a[13]^b[13]^x6[26];
assign sum[14]=a[14]^b[14]^x6[28];
assign sum[15]=a[15]^b[15]^x6[30];
assign sum[16]=a[16]^b[16]^x6[32];
assign sum[17]=a[17]^b[17]^x6[34];
assign sum[18]=a[18]^b[18]^x6[36];
assign sum[19]=a[19]^b[19]^x6[38];
assign sum[20]=a[20]^b[20]^x6[40];
assign sum[21]=a[21]^b[21]^x6[42];
assign sum[22]=a[22]^b[22]^x6[44];
assign sum[23]=a[23]^b[23]^x6[46];
assign sum[24]=a[24]^b[24]^x6[48];
assign sum[25]=a[25]^b[25]^x6[50];
assign sum[26]=a[26]^b[26]^x6[52];
assign sum[27]=a[27]^b[27]^x6[54];
assign sum[28]=a[28]^b[28]^x6[56];
assign sum[29]=a[29]^b[29]^x6[58];
assign sum[30]=a[30]^b[30]^x6[60];
assign sum[31]=a[31]^b[31]^x6[62];
assign sum[32]=a[32]^b[32]^x6[64];
assign sum[33]=a[33]^b[33]^x6[66];
assign sum[34]=a[34]^b[34]^x6[68];
assign sum[35]=a[35]^b[35]^x6[70];
assign sum[36]=a[36]^b[36]^x6[72];
assign sum[37]=a[37]^b[37]^x6[74];
assign sum[38]=a[38]^b[38]^x6[76];
assign sum[39]=a[39]^b[39]^x6[79];

kgp_carry kkc(x[81:80],x6[79:78],carry);

endmodule



//2 to 1 multiplexer design

module mux2to1_41(out,i1,i2,s);

input [40:0] i1,i2;
input s;
output [40:0] out;
reg [40:0] out;

always@(i1 or i2 or s)
	begin
	 case(s)
	  1'b0:out=i1;
	  1'b1:out=i2;
	 endcase
	end

endmodule

// D flip flop

module dflipflop41(q,d,clk,reset);
output [40:0] q;
input [40:0] d;
input clk,reset;
reg [40:0] q;
always@(posedge reset or negedge clk)
if(reset)
q<=41'b00000000;
else
q<=d;
endmodule

// storage buffer

//`include "mux2to1_25.v"
//`include "dflipflop25.v"

module storage32_25(i,d32,s,clk,reset);

input [24:0] i;
input s,clk,reset;//s is 0 for feed back and 1 for feed forward
output [24:0] d32;

wire [24:0] m1,m2,m3,m4,m5,m6,m7,m8,m9,m10,m11,m12,m13,m14,m15,m16,m17,m18,m19,m20,m21,m22,m23,m24,m25,m26,m27,m28,m29,m30,m31,m32;
wire [24:0] d1,d2,d3,d4,d5,d6,d7,d8,d9,d10,d11,d12,d13,d14,d15,d16,d17,d18,d19,d20,d21,d22,d23,d24,d25,d26,d27,d28,d29,d30,d31,d32;

mux2to1_25 mu1(m1,d1,i,s); 
dflipflop25 df1(d1,m1,clk,reset);

mux2to1_25 mu2(m2,d2,d1,s);
dflipflop25 df2(d2,m2,clk,reset);

mux2to1_25 mu3(m3,d3,d2,s);
dflipflop25 df3(d3,m3,clk,reset);

mux2to1_25 mu4(m4,d4,d3,s);
dflipflop25 df4(d4,m4,clk,reset);

mux2to1_25 mu5(m5,d5,d4,s);
dflipflop25 df5(d5,m5,clk,reset);

mux2to1_25 mu6(m6,d6,d5,s);
dflipflop25 df6(d6,m6,clk,reset);

mux2to1_25 mu7(m7,d7,d6,s);
dflipflop25 df7(d7,m7,clk,reset);

mux2to1_25 mu8(m8,d8,d7,s);
dflipflop25 df8(d8,m8,clk,reset);

mux2to1_25 mu9(m9,d9,d8,s);
dflipflop25 df9(d9,m9,clk,reset);

mux2to1_25 mu10(m10,d10,d9,s);
dflipflop25 df10(d10,m10,clk,reset);

mux2to1_25 mu11(m11,d11,d10,s);
dflipflop25 df11(d11,m11,clk,reset);

mux2to1_25 mu12(m12,d12,d11,s);
dflipflop25 df12(d12,m12,clk,reset);

mux2to1_25 mu13(m13,d13,d12,s);
dflipflop25 df13(d13,m13,clk,reset);

mux2to1_25 mu14(m14,d14,d13,s);
dflipflop25 df14(d14,m14,clk,reset);

mux2to1_25 mu15(m15,d15,d14,s);
dflipflop25 df15(d15,m15,clk,reset);

mux2to1_25 mu16(m16,d16,d15,s);
dflipflop25 df16(d16,m16,clk,reset);

mux2to1_25 mu17(m17,d17,d16,s);
dflipflop25 df17(d17,m17,clk,reset);

mux2to1_25 mu18(m18,d18,d17,s);
dflipflop25 df18(d18,m18,clk,reset);

mux2to1_25 mu19(m19,d19,d18,s);
dflipflop25 df19(d19,m19,clk,reset);

mux2to1_25 mu20(m20,d20,d19,s);
dflipflop25 df20(d20,m20,clk,reset);

mux2to1_25 mu21(m21,d21,d20,s);
dflipflop25 df21(d21,m21,clk,reset);

mux2to1_25 mu22(m22,d22,d21,s);
dflipflop25 df22(d22,m22,clk,reset);

mux2to1_25 mu23(m23,d23,d22,s);
dflipflop25 df23(d23,m23,clk,reset);

mux2to1_25 mu24(m24,d24,d23,s);
dflipflop25 df24(d24,m24,clk,reset);

mux2to1_25 mu25(m25,d25,d24,s);
dflipflop25 df25(d25,m25,clk,reset);

mux2to1_25 mu26(m26,d26,d25,s);
dflipflop25 df26(d26,m26,clk,reset);

mux2to1_25 mu27(m27,d27,d26,s);
dflipflop25 df27(d27,m27,clk,reset);

mux2to1_25 mu28(m28,d28,d27,s);
dflipflop25 df28(d28,m28,clk,reset);

mux2to1_25 mu29(m29,d29,d28,s);
dflipflop25 df29(d29,m29,clk,reset);

mux2to1_25 mu30(m30,d30,d29,s);
dflipflop25 df30(d30,m30,clk,reset);

mux2to1_25 mu31(m31,d31,d30,s);
dflipflop25 df31(d31,m31,clk,reset);

mux2to1_25 mu32(m32,d32,d31,s);
dflipflop25 df32(d32,m32,clk,reset);

endmodule




`default_nettype wire
