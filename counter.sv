module counter(output logic [15:0] data_out,
               input  logic rst, ld_cnt, updn_cnt, count_enb, clk, [15:0] data_in);
logic [2:0] state_info;

always_ff @ (posedge clk, negedge rst) 
begin
    if(!rst) data_out <= 16'b0;
    else 
    begin
        priority case(state_info) 
            3'b 000: data_out <= data_in;
            3'b 001: data_out <= data_in;
            3'b 010: data_out <= data_in;
            3'b 011: data_out <= data_in;
            3'b 100: data_out <= data_out; 
            3'b 101: data_out <= data_out; 
            3'b 110: data_out <= data_out - 1;
            3'b 111: data_out <= data_out + 1;
        endcase
    end
end

always_comb begin : set_state
    state_info = {ld_cnt,count_enb,updn_cnt};
end 
endmodule

