
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "1010000000", info);
    add_bitstring(bits, "0000000100", info);
    add_bitstring(bits, "0000010001", info);
    add_bitstring(bits, "0000100000", info);
    add_bitstring(bits, "1000010110", info);
    add_bitstring(bits, "0000000001", info);
    add_bitstring(bits, "0000110000", info);
    add_bitstring(bits, "0010000010", info);
    add_bitstring(bits, "0000000011", info);
    add_bitstring(bits, "1011110100", info);
    add_bitstring(bits, "0001010000", info);
    add_bitstring(bits, "0011100001", info);
    add_bitstring(bits, "0001000000", info);
    add_bitstring(bits, "1000011100", info);
    add_bitstring(bits, "0000000010", info);
    add_bitstring(bits, "0000001000", info);
    add_bitstring(bits, "1001000000", info);
    add_bitstring(bits, "0000011000", info);
    add_bitstring(bits, "0010000000", info);
    add_bitstring(bits, "1010000010", info);
    add_bitstring(bits, "1000000000", info);
    add_bitstring(bits, "0011100000", info);
    add_bitstring(bits, "0000001100", info);
    add_bitstring(bits, "1000000001", info);
    add_bitstring(bits, "0000000110", info);
    add_bitstring(bits, "0000001001", info);
    add_bitstring(bits, "0001010001", info);
    add_bitstring(bits, "0000100010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(13);
    ts[0] = encrypt_input("0111111111111110111111101111110110111111111010", info);
    ts[2] = encrypt_input("1111111111111111101111011111100111101111111010", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[16];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -8, gk, ss[0]); // __s0 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -1, gk, ss[1]); // __s1 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -6, gk, ss[2]); // __s2 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -2, gk, ss[3]); // __s3 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -4, gk, ss[4]); // __s4 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -9, gk, ss[5]); // __s5 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -5, gk, ss[6]); // __s6 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -3, gk, ss[7]); // __s7 = __v0 >> 3
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -8, gk, ss[8]); // __s8 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -2, gk, ss[9]); // __s9 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -3, gk, ss[10]); // __s10 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -4, gk, ss[11]); // __s11 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -6, gk, ss[12]); // __s12 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -1, gk, ss[13]); // __s13 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -9, gk, ss[14]); // __s14 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -7, gk, ss[15]); // __s15 = __v1 >> 7
    
    // __t4 = blend(__s1@1010000000, __s2@0001010000, __v0@0000100000, __s4@0000001100, __s3@0000000010, __s0@0000000001)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5, t4_6;
    info.eval->multiply_plain(ss[1], bits["1010000000"], t4_1);
    info.eval->multiply_plain(ss[2], bits["0001010000"], t4_2);
    info.eval->multiply_plain(vs[0], bits["0000100000"], t4_3);
    info.eval->multiply_plain(ss[4], bits["0000001100"], t4_4);
    info.eval->multiply_plain(ss[3], bits["0000000010"], t4_5);
    info.eval->multiply_plain(ss[0], bits["0000000001"], t4_6);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, t4_6}, ts[4]);
    
    
    // __t5 = blend(__s12@1001000000, __v1@0010000000, __s10@0000100000, __s9@0000010001, __s13@0000001000, __s11@0000000110)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5, t5_6;
    info.eval->multiply_plain(ss[12], bits["1001000000"], t5_1);
    info.eval->multiply_plain(vs[1], bits["0010000000"], t5_2);
    info.eval->multiply_plain(ss[10], bits["0000100000"], t5_3);
    info.eval->multiply_plain(ss[9], bits["0000010001"], t5_4);
    info.eval->multiply_plain(ss[13], bits["0000001000"], t5_5);
    info.eval->multiply_plain(ss[11], bits["0000000110"], t5_6);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5, t5_6}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__s6@1000000000, __s4@0010000010, __s0@0001000000, __s3@0000100000, __v0@0000011000, __s5@0000000100, __s2@0000000001)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7;
    info.eval->multiply_plain(ss[6], bits["1000000000"], t6_1);
    info.eval->multiply_plain(ss[4], bits["0010000010"], t6_2);
    info.eval->multiply_plain(ss[0], bits["0001000000"], t6_3);
    info.eval->multiply_plain(ss[3], bits["0000100000"], t6_4);
    info.eval->multiply_plain(vs[0], bits["0000011000"], t6_5);
    info.eval->multiply_plain(ss[5], bits["0000000100"], t6_6);
    info.eval->multiply_plain(ss[2], bits["0000000001"], t6_7);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7}, ts[6]);
    
    
    // __t7 = blend(__v1@1000000001, __s9@0010000000, __s8@0001000000, __s12@0000100010, __s15@0000011000, __s14@0000000100)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5, t7_6;
    info.eval->multiply_plain(vs[1], bits["1000000001"], t7_1);
    info.eval->multiply_plain(ss[9], bits["0010000000"], t7_2);
    info.eval->multiply_plain(ss[8], bits["0001000000"], t7_3);
    info.eval->multiply_plain(ss[12], bits["0000100010"], t7_4);
    info.eval->multiply_plain(ss[15], bits["0000011000"], t7_5);
    info.eval->multiply_plain(ss[14], bits["0000000100"], t7_6);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5, t7_6}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__s7@1000000000, __s5@0010000000, __s4@0001000000, __s0@0000110000, __s3@0000001000, __s2@0000000110, __s1@0000000001)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5, t8_6, t8_7;
    info.eval->multiply_plain(ss[7], bits["1000000000"], t8_1);
    info.eval->multiply_plain(ss[5], bits["0010000000"], t8_2);
    info.eval->multiply_plain(ss[4], bits["0001000000"], t8_3);
    info.eval->multiply_plain(ss[0], bits["0000110000"], t8_4);
    info.eval->multiply_plain(ss[3], bits["0000001000"], t8_5);
    info.eval->multiply_plain(ss[2], bits["0000000110"], t8_6);
    info.eval->multiply_plain(ss[1], bits["0000000001"], t8_7);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5, t8_6, t8_7}, ts[8]);
    
    
    // __t9 = blend(__s8@1010000010, __s11@0001010001, __s13@0000100000, __s14@0000001000, __s12@0000000100)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5;
    info.eval->multiply_plain(ss[8], bits["1010000010"], t9_1);
    info.eval->multiply_plain(ss[11], bits["0001010001"], t9_2);
    info.eval->multiply_plain(ss[13], bits["0000100000"], t9_3);
    info.eval->multiply_plain(ss[14], bits["0000001000"], t9_4);
    info.eval->multiply_plain(ss[12], bits["0000000100"], t9_5);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t10 = blend(__v2@1000010110, __v4@0011100000, __v3@0000001001)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[2], bits["1000010110"], t10_1);
    info.eval->multiply_plain(vs[4], bits["0011100000"], t10_2);
    info.eval->multiply_plain(vs[3], bits["0000001001"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__v3@1011110100, __v2@0000001000, __v4@0000000011)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[3], bits["1011110100"], t11_1);
    info.eval->multiply_plain(vs[2], bits["0000001000"], t11_2);
    info.eval->multiply_plain(vs[4], bits["0000000011"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[5]); // __v5 = __t10 + __t11
    
    // __t12 = blend(__v4@1000011100, __v2@0011100001, __v3@0000000010)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(vs[4], bits["1000011100"], t12_1);
    info.eval->multiply_plain(vs[2], bits["0011100001"], t12_2);
    info.eval->multiply_plain(vs[3], bits["0000000010"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    info.eval->add(vs[5], ts[12], vs[6]); // __v6 = __v5 + __t12
    return vs[6];
}
    