
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000000010000000100000000000000", info);
    add_bitstring(bits, "1000000100000010000000000000000", info);
    add_bitstring(bits, "0000000000000010110000000000000", info);
    add_bitstring(bits, "0000000000000001000000000000010", info);
    add_bitstring(bits, "0000000010000000000000000000000", info);
    add_bitstring(bits, "0000000000000000000000100000000", info);
    add_bitstring(bits, "0001000000000000000000000000000", info);
    add_bitstring(bits, "0000000000000100000000010000000", info);
    add_bitstring(bits, "0000000000000000000000000010101", info);
    add_bitstring(bits, "0000000000010000000000000100000", info);
    add_bitstring(bits, "1000010010010001000101101000010", info);
    add_bitstring(bits, "0000000000000000000000010000000", info);
    add_bitstring(bits, "0000000000000000000010100001000", info);
    add_bitstring(bits, "0000000000000000001001000000000", info);
    add_bitstring(bits, "0000000000000000000001010000000", info);
    add_bitstring(bits, "0000000000000000000000000000011", info);
    add_bitstring(bits, "0001000100000000000000000000000", info);
    add_bitstring(bits, "0000000000000000000001000000000", info);
    add_bitstring(bits, "0000000000000001000000000000001", info);
    add_bitstring(bits, "0000000000110101000000000000000", info);
    add_bitstring(bits, "0000010000000000000110100000000", info);
    add_bitstring(bits, "1000010000000000000000000000000", info);
    add_bitstring(bits, "1000000000000000000000000000000", info);
    add_bitstring(bits, "0000000000010001000001000000000", info);
    add_bitstring(bits, "0000000000000000001000000010100", info);
    add_bitstring(bits, "1000010010000000000100101000010", info);
    add_bitstring(bits, "0000000000000000000010000001000", info);
    add_bitstring(bits, "0000000000000000000000001000010", info);
    add_bitstring(bits, "0001000100100000011010000000000", info);
    add_bitstring(bits, "0000000000000100000001000000000", info);
    add_bitstring(bits, "0000000000010000001000000110100", info);
    add_bitstring(bits, "0000000000000000100000000000000", info);
    add_bitstring(bits, "0000000000100000010000000001000", info);
    add_bitstring(bits, "0000000000000000000100000000000", info);
    add_bitstring(bits, "0000000000000000000000001000000", info);
    add_bitstring(bits, "0000000000000000000000010100000", info);
    add_bitstring(bits, "0000000000000000000010000000000", info);
    add_bitstring(bits, "0000000010100100000000000000000", info);
    add_bitstring(bits, "0000000000000000000000000100000", info);
    add_bitstring(bits, "0000010000000000000100100000000", info);
    add_bitstring(bits, "0000000000000000001000000000000", info);
    add_bitstring(bits, "0000000000000000000000010010101", info);
    add_bitstring(bits, "0000000000000110100000000011101", info);
    add_bitstring(bits, "1001010100000000000000000000000", info);
    add_bitstring(bits, "0000000000000000000000001100010", info);
    add_bitstring(bits, "0000000000000010110100000000000", info);
    add_bitstring(bits, "0000000100000010000000000000000", info);
    add_bitstring(bits, "0000000010010001000000000000000", info);
    add_bitstring(bits, "0000000000100000010000001001000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("000000000000000000000001111111111111111111111111111101111111111111111111111111111111111111111111111111111111110011111111111111111111111111111011111111111111111111111111111", info);
    ts[1] = encrypt_input("000000000000000000000001111111111111111111111111111101111111111111111111111111111111111111111111111111111111110011111111111111111111111111111011111111111111111111111111111", info);
    ts[2] = encrypt_input("000000000001111111111111111111111111111100000011111111111111111111111111111000000111111111111111111111111111111111111111111111111111111111101111111111111111111111111111000", info);
    ts[3] = encrypt_input("000000000001111111111111111111111111111100000011111111111111111111111111111000000111111111111111111111111111111111111111111111111111111111101111111111111111111111111111000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[13];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -8, gk, ss[0]); // __s0 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -16, gk, ss[1]); // __s1 = __v0 >> 16
    info.eval->rotate_rows(vs[0], -28, gk, ss[2]); // __s2 = __v0 >> 28
    info.eval->rotate_rows(vs[0], -22, gk, ss[3]); // __s3 = __v0 >> 22
    info.eval->rotate_rows(vs[0], -24, gk, ss[4]); // __s4 = __v0 >> 24
    info.eval->rotate_rows(vs[0], -30, gk, ss[5]); // __s5 = __v0 >> 30
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -25, gk, ss[6]); // __s6 = __v1 >> 25
    info.eval->rotate_rows(vs[1], -4, gk, ss[7]); // __s7 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -20, gk, ss[8]); // __s8 = __v1 >> 20
    info.eval->rotate_rows(vs[1], -30, gk, ss[9]); // __s9 = __v1 >> 30
    info.eval->rotate_rows(vs[1], -26, gk, ss[10]); // __s10 = __v1 >> 26
    info.eval->rotate_rows(vs[1], -21, gk, ss[11]); // __s11 = __v1 >> 21
    info.eval->rotate_rows(vs[1], -6, gk, ss[12]); // __s12 = __v1 >> 6
    
    // __t4 = blend(__s0@0001000100000000000000000000000, __s1@0000000000110101000000000000000, __s3@0000000000000010110000000000000, __s4@0000000000000000001001000000000, __s2@0000000000000000000010000001000, __s5@0000000000000000000000000100000, __v0@0000000000000000000000000010101)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, t4_7;
    info.eval->multiply_plain(ss[0], bits["0001000100000000000000000000000"], t4_1);
    info.eval->multiply_plain(ss[1], bits["0000000000110101000000000000000"], t4_2);
    info.eval->multiply_plain(ss[3], bits["0000000000000010110000000000000"], t4_3);
    info.eval->multiply_plain(ss[4], bits["0000000000000000001001000000000"], t4_4);
    info.eval->multiply_plain(ss[2], bits["0000000000000000000010000001000"], t4_5);
    info.eval->multiply_plain(ss[5], bits["0000000000000000000000000100000"], t4_6);
    info.eval->multiply_plain(vs[0], bits["0000000000000000000000000010101"], t4_7);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, t4_7}, ts[4]);
    
    
    // __t5 = blend(__s12@0001000000000000000000000000000, __s8@0000000100000010000000000000000, __s9@0000000000100000010000000001000, __v1@0000000000010000001000000110100, __s10@0000000000000100000001000000000, __s7@0000000000000001000000000000001, __s11@0000000000000000100000000000000, __s6@0000000000000000000010000000000)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5, t5_6, t5_7, t5_8;
    info.eval->multiply_plain(ss[12], bits["0001000000000000000000000000000"], t5_1);
    info.eval->multiply_plain(ss[8], bits["0000000100000010000000000000000"], t5_2);
    info.eval->multiply_plain(ss[9], bits["0000000000100000010000000001000"], t5_3);
    info.eval->multiply_plain(vs[1], bits["0000000000010000001000000110100"], t5_4);
    info.eval->multiply_plain(ss[10], bits["0000000000000100000001000000000"], t5_5);
    info.eval->multiply_plain(ss[7], bits["0000000000000001000000000000001"], t5_6);
    info.eval->multiply_plain(ss[11], bits["0000000000000000100000000000000"], t5_7);
    info.eval->multiply_plain(ss[6], bits["0000000000000000000010000000000"], t5_8);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5, t5_6, t5_7, t5_8}, ts[5]);
    
    info.eval->sub(ts[4], ts[5], vs[2]); // __v2 = __t4 - __t5
    
    // __t6 = blend(__s0@1001010100000000000000000000000, __s1@0000000010100100000000000000000, __s3@0000000000000010110100000000000, __s4@0000000000000000001000000000000, __s2@0000000000000000000010100001000, __v0@0000000000000000000000010010101, __s5@0000000000000000000000001000010)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7;
    info.eval->multiply_plain(ss[0], bits["1001010100000000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[1], bits["0000000010100100000000000000000"], t6_2);
    info.eval->multiply_plain(ss[3], bits["0000000000000010110100000000000"], t6_3);
    info.eval->multiply_plain(ss[4], bits["0000000000000000001000000000000"], t6_4);
    info.eval->multiply_plain(ss[2], bits["0000000000000000000010100001000"], t6_5);
    info.eval->multiply_plain(vs[0], bits["0000000000000000000000010010101"], t6_6);
    info.eval->multiply_plain(ss[5], bits["0000000000000000000000001000010"], t6_7);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7}, ts[6]);
    
    
    // __t7 = blend(__s8@1000000100000010000000000000000, __s12@0001000000000000000000000000000, __s6@0000010000000000000110100000000, __s11@0000000010000000100000000000000, __s9@0000000000100000010000001001000, __s10@0000000000000100000000010000000, __v1@0000000000000000001000000010100, __s7@0000000000000000000000000000011)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7, t7_8;
    info.eval->multiply_plain(ss[8], bits["1000000100000010000000000000000"], t7_1);
    info.eval->multiply_plain(ss[12], bits["0001000000000000000000000000000"], t7_2);
    info.eval->multiply_plain(ss[6], bits["0000010000000000000110100000000"], t7_3);
    info.eval->multiply_plain(ss[11], bits["0000000010000000100000000000000"], t7_4);
    info.eval->multiply_plain(ss[9], bits["0000000000100000010000001001000"], t7_5);
    info.eval->multiply_plain(ss[10], bits["0000000000000100000000010000000"], t7_6);
    info.eval->multiply_plain(vs[1], bits["0000000000000000001000000010100"], t7_7);
    info.eval->multiply_plain(ss[7], bits["0000000000000000000000000000011"], t7_8);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7, t7_8}, ts[7]);
    
    info.eval->sub(ts[6], ts[7], vs[3]); // __v3 = __t6 - __t7
    
    // __t8 = blend(__v3@0001000100100000011010000000000, __v2@0000000000000110100000000011101)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[3], bits["0001000100100000011010000000000"], t8_1);
    info.eval->multiply_plain(vs[2], bits["0000000000000110100000000011101"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__v2@0001000100100000011010000000000, __v3@0000000000000110100000000011101)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[2], bits["0001000100100000011010000000000"], t9_1);
    info.eval->multiply_plain(vs[3], bits["0000000000000110100000000011101"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t10 = blend(__s0@1000010000000000000000000000000, __s1@0000000010010001000000000000000, __s3@0000000000000000000100000000000, __s4@0000000000000000000001000000000, __s2@0000000000000000000000100000000, __v0@0000000000000000000000010000000, __s5@0000000000000000000000001100010)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5, t10_6, t10_7;
    info.eval->multiply_plain(ss[0], bits["1000010000000000000000000000000"], t10_1);
    info.eval->multiply_plain(ss[1], bits["0000000010010001000000000000000"], t10_2);
    info.eval->multiply_plain(ss[3], bits["0000000000000000000100000000000"], t10_3);
    info.eval->multiply_plain(ss[4], bits["0000000000000000000001000000000"], t10_4);
    info.eval->multiply_plain(ss[2], bits["0000000000000000000000100000000"], t10_5);
    info.eval->multiply_plain(vs[0], bits["0000000000000000000000010000000"], t10_6);
    info.eval->multiply_plain(ss[5], bits["0000000000000000000000001100010"], t10_7);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5, t10_6, t10_7}, ts[10]);
    
    
    // __t11 = blend(__s8@1000000000000000000000000000000, __s6@0000010000000000000100100000000, __s11@0000000010000000000000000000000, __v1@0000000000010000000000000100000, __s7@0000000000000001000000000000010, __s10@0000000000000000000001010000000, __s9@0000000000000000000000001000000)
    ctxt t11_1, t11_2, t11_3, t11_4, t11_5, t11_6, t11_7;
    info.eval->multiply_plain(ss[8], bits["1000000000000000000000000000000"], t11_1);
    info.eval->multiply_plain(ss[6], bits["0000010000000000000100100000000"], t11_2);
    info.eval->multiply_plain(ss[11], bits["0000000010000000000000000000000"], t11_3);
    info.eval->multiply_plain(vs[1], bits["0000000000010000000000000100000"], t11_4);
    info.eval->multiply_plain(ss[7], bits["0000000000000001000000000000010"], t11_5);
    info.eval->multiply_plain(ss[10], bits["0000000000000000000001010000000"], t11_6);
    info.eval->multiply_plain(ss[9], bits["0000000000000000000000001000000"], t11_7);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, t11_5, t11_6, t11_7}, ts[11]);
    
    info.eval->sub(ts[10], ts[11], vs[5]); // __v5 = __t10 - __t11
    
    // __t12 = blend(__v5@1000010010010001000101101000010, __v3@0000000000000000000000010000000, __v2@0000000000000000000000000100000)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(vs[5], bits["1000010010010001000101101000010"], t12_1);
    info.eval->multiply_plain(vs[3], bits["0000000000000000000000010000000"], t12_2);
    info.eval->multiply_plain(vs[2], bits["0000000000000000000000000100000"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    
    // __t13 = blend(__v3@1000010010000000000100101000010, __v2@0000000000010001000001000000000, __v5@0000000000000000000000010100000)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(vs[3], bits["1000010010000000000100101000010"], t13_1);
    info.eval->multiply_plain(vs[2], bits["0000000000010001000001000000000"], t13_2);
    info.eval->multiply_plain(vs[5], bits["0000000000000000000000010100000"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[6]); // __v6 = __t12 * __t13
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    