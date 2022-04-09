
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000010000000000000000000000", info);
    add_bitstring(bits, "01000000000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000100000000010", info);
    add_bitstring(bits, "00000000000000000000000100000000", info);
    add_bitstring(bits, "01000000000000000000000000000100", info);
    add_bitstring(bits, "00000001000000000000001000000000", info);
    add_bitstring(bits, "00000000000000010000100000000000", info);
    add_bitstring(bits, "00000001000000000000000000000000", info);
    add_bitstring(bits, "00100000000000000000000000000000", info);
    add_bitstring(bits, "00100000000000000100000000000010", info);
    add_bitstring(bits, "00000000100000000000000000000000", info);
    add_bitstring(bits, "00000000000000010000000000000000", info);
    add_bitstring(bits, "00000010000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000001000000000", info);
    add_bitstring(bits, "00000010000000000001000001000000", info);
    add_bitstring(bits, "00000000000000000000010000000000", info);
    add_bitstring(bits, "00000000000000000000000000010000", info);
    add_bitstring(bits, "00100000000000000000000100000000", info);
    add_bitstring(bits, "00000000000000000000000001000000", info);
    add_bitstring(bits, "00000000000000000100000000010000", info);
    add_bitstring(bits, "00000000000000000000000000000100", info);
    add_bitstring(bits, "00000000000000001000000000000000", info);
    add_bitstring(bits, "00000001100000000000001000000000", info);
    add_bitstring(bits, "00000000000000000001000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("01111010101100111000001110011101110011000111001010011111", info);
    ts[1] = encrypt_input("011111101110010010000011001110111001100111001110011110", info);
    ts[2] = encrypt_input("11100101011110001111111111011100111111011101111110111111011111001101100", info);
    ts[3] = encrypt_input("111001110111110011011111111110101111100111011111101111110111111011111100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[11];
    ctxt ss[19];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -31, gk, ss[0]); // __s0 = __v0 >> 31
    info.eval->rotate_rows(vs[0], -5, gk, ss[1]); // __s1 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -2, gk, ss[2]); // __s2 = __v0 >> 2
    info.eval->add(ts[2], ts[3], vs[1]); // __v1 = __t2 + __t3
    info.eval->rotate_rows(vs[1], -2, gk, ss[3]); // __s3 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -31, gk, ss[4]); // __s4 = __v1 >> 31
    info.eval->rotate_rows(vs[1], -28, gk, ss[5]); // __s5 = __v1 >> 28
    info.eval->rotate_rows(vs[1], -5, gk, ss[6]); // __s6 = __v1 >> 5
    
    // __t4 = blend(__v0@01000000000000000000000000000000, __s0@00000010000000000000000000000000, __s6@00000000000000000001000000000000, __v1@00000000000000000000000001000000, __s1@00000000000000000000000000000100)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5;
    info.eval->multiply_plain(vs[0], bits["01000000000000000000000000000000"], t4_1);
    info.eval->multiply_plain(ss[0], bits["00000010000000000000000000000000"], t4_2);
    info.eval->multiply_plain(ss[6], bits["00000000000000000001000000000000"], t4_3);
    info.eval->multiply_plain(vs[1], bits["00000000000000000000000001000000"], t4_4);
    info.eval->multiply_plain(ss[1], bits["00000000000000000000000000000100"], t4_5);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5}, ts[4]);
    
    
    // __t5 = blend(__s0@01000000000000000000000000000100, __s5@00000010000000000001000001000000)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(ss[0], bits["01000000000000000000000000000100"], t5_1);
    info.eval->multiply_plain(ss[5], bits["00000010000000000001000001000000"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -28, gk, ss[7]); // __s7 = __v2 >> 28
    info.eval->rotate_rows(vs[2], -25, gk, ss[8]); // __s8 = __v2 >> 25
    
    // __t6 = blend(__s3@00100000000000000100000000000010, __s5@00000001000000000000001000000000, __v1@00000000100000000000000000000000, __s1@00000000010000000000000000000000, __s2@00000000000000010000100000000000, __s4@00000000000000001000000000000000, __v0@00000000000000000000000000010000)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7;
    info.eval->multiply_plain(ss[3], bits["00100000000000000100000000000010"], t6_1);
    info.eval->multiply_plain(ss[5], bits["00000001000000000000001000000000"], t6_2);
    info.eval->multiply_plain(vs[1], bits["00000000100000000000000000000000"], t6_3);
    info.eval->multiply_plain(ss[1], bits["00000000010000000000000000000000"], t6_4);
    info.eval->multiply_plain(ss[2], bits["00000000000000010000100000000000"], t6_5);
    info.eval->multiply_plain(ss[4], bits["00000000000000001000000000000000"], t6_6);
    info.eval->multiply_plain(vs[0], bits["00000000000000000000000000010000"], t6_7);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6, t6_7}, ts[6]);
    
    
    // __t7 = blend(__s4@00100000000000000000000000000000, __s3@00000001100000000000001000000000, __v1@00000000010000000000000000000000, __s5@00000000000000010000000000000000, __v0@00000000000000001000000000000000, __s6@00000000000000000100000000010000, __s0@00000000000000000000100000000010)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7;
    info.eval->multiply_plain(ss[4], bits["00100000000000000000000000000000"], t7_1);
    info.eval->multiply_plain(ss[3], bits["00000001100000000000001000000000"], t7_2);
    info.eval->multiply_plain(vs[1], bits["00000000010000000000000000000000"], t7_3);
    info.eval->multiply_plain(ss[5], bits["00000000000000010000000000000000"], t7_4);
    info.eval->multiply_plain(vs[0], bits["00000000000000001000000000000000"], t7_5);
    info.eval->multiply_plain(ss[6], bits["00000000000000000100000000010000"], t7_6);
    info.eval->multiply_plain(ss[0], bits["00000000000000000000100000000010"], t7_7);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7}, ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[3]); // __v3 = __t6 + __t7
    info.eval->rotate_rows(vs[3], -5, gk, ss[9]); // __s9 = __v3 >> 5
    info.eval->rotate_rows(vs[3], -25, gk, ss[10]); // __s10 = __v3 >> 25
    info.eval->rotate_rows(vs[3], -13, gk, ss[11]); // __s11 = __v3 >> 13
    info.eval->rotate_rows(vs[3], -28, gk, ss[12]); // __s12 = __v3 >> 28
    
    // __t8 = blend(__s10@00100000000000000000000100000000, __s7@00000000000000010000000000000000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(ss[10], bits["00100000000000000000000100000000"], t8_1);
    info.eval->multiply_plain(ss[7], bits["00000000000000010000000000000000"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__s7@00100000000000000000000000000000, __s10@00000000000000010000000000000000, __s12@00000000000000000000000100000000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(ss[7], bits["00100000000000000000000000000000"], t9_1);
    info.eval->multiply_plain(ss[10], bits["00000000000000010000000000000000"], t9_2);
    info.eval->multiply_plain(ss[12], bits["00000000000000000000000100000000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3}, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    info.eval->rotate_rows(vs[4], -7, gk, ss[13]); // __s13 = __v4 >> 7
    
    // __t10 = blend(__s11@01000000000000000000000000000000, __v3@00000001000000000000000000000000, __s10@00000000100000000000000000000000, __s9@00000000000000000000010000000000, __s8@00000000000000000000001000000000)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5;
    info.eval->multiply_plain(ss[11], bits["01000000000000000000000000000000"], t10_1);
    info.eval->multiply_plain(vs[3], bits["00000001000000000000000000000000"], t10_2);
    info.eval->multiply_plain(ss[10], bits["00000000100000000000000000000000"], t10_3);
    info.eval->multiply_plain(ss[9], bits["00000000000000000000010000000000"], t10_4);
    info.eval->multiply_plain(ss[8], bits["00000000000000000000001000000000"], t10_5);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5}, ts[10]);
    
    
    // __t11 = blend(__v2@01000000000000000000000000000000, __s9@00000001000000000000001000000000, __v3@00000000100000000000000000000000, __s7@00000000000000000000010000000000)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(vs[2], bits["01000000000000000000000000000000"], t11_1);
    info.eval->multiply_plain(ss[9], bits["00000001000000000000001000000000"], t11_2);
    info.eval->multiply_plain(vs[3], bits["00000000100000000000000000000000"], t11_3);
    info.eval->multiply_plain(ss[7], bits["00000000000000000000010000000000"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[5]); // __v5 = __t10 * __t11
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -7, gk, ss[14]); // __s14 = __v5 >> 7
    info.eval->rotate_rows(vs[5], -2, gk, ss[15]); // __s15 = __v5 >> 2
    
    // __t12 = blend(__s13@00000000010000000000000000000000, __v5@00000000000000000000001000000000, __s15@00000000000000000000000100000000)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(ss[13], bits["00000000010000000000000000000000"], t12_1);
    info.eval->multiply_plain(vs[5], bits["00000000000000000000001000000000"], t12_2);
    info.eval->multiply_plain(ss[15], bits["00000000000000000000000100000000"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    
    // __t13 = blend(__s15@00000000010000000000000000000000, __s13@00000000000000000000001000000000, __v4@00000000000000000000000100000000)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(ss[15], bits["00000000010000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[13], bits["00000000000000000000001000000000"], t13_2);
    info.eval->multiply_plain(vs[4], bits["00000000000000000000000100000000"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[6]); // __v6 = __t12 + __t13
    info.eval->rotate_rows(vs[6], -14, gk, ss[16]); // __s16 = __v6 >> 14
    info.eval->multiply(vs[5], ss[14], vs[7]); // __v7 = __v5 * __s14
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -14, gk, ss[17]); // __s17 = __v7 >> 14
    info.eval->add(ss[17], vs[6], vs[8]); // __v8 = __s17 + __v6
    info.eval->multiply(ss[16], vs[6], vs[9]); // __v9 = __s16 * __v6
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->rotate_rows(vs[9], -31, gk, ss[18]); // __s18 = __v9 >> 31
    info.eval->multiply(ss[18], vs[8], vs[10]); // __v10 = __s18 * __v8
    info.eval->relinearize_inplace(vs[10], rk);
    return vs[10];
}
    