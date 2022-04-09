
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000000000101000000000000000", info);
    add_bitstring(bits, "00000000000000000000000010000000", info);
    add_bitstring(bits, "00010000000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000010000000000000", info);
    add_bitstring(bits, "00000000000000000000000000100000", info);
    add_bitstring(bits, "00000000000000010000001100000000", info);
    add_bitstring(bits, "00000000000000000000000100000000", info);
    add_bitstring(bits, "10000000000000000000000000000000", info);
    add_bitstring(bits, "10000000001000000000100000000000", info);
    add_bitstring(bits, "00000000000001000000000000000000", info);
    add_bitstring(bits, "00000000000000000001000000000000", info);
    add_bitstring(bits, "00000000000000000000100000000000", info);
    add_bitstring(bits, "00000000100000000000000000100000", info);
    add_bitstring(bits, "00000000100000100000000000000000", info);
    add_bitstring(bits, "00000000001000000000000000000000", info);
    add_bitstring(bits, "00000000000000001000000000000000", info);
    add_bitstring(bits, "00000000100000000000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(16);
    ts[0] = encrypt_input("1111111111100000001111010000011111110111111101010110110111011111111111", info);
    ts[1] = encrypt_input("110111110111000000111111000001111111111111010111111111110110101110111", info);
    ts[2] = encrypt_input("00001011111111011111001111111111011110000011100001110000", info);
    ts[3] = encrypt_input("0000111111111111111111001001111111111110000011100001110000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[12];
    ctxt ss[20];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -9, gk, ss[0]); // __s0 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -1, gk, ss[1]); // __s1 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -10, gk, ss[2]); // __s2 = __v0 >> 10
    info.eval->rotate_rows(vs[0], -29, gk, ss[3]); // __s3 = __v0 >> 29
    info.eval->rotate_rows(vs[0], -24, gk, ss[4]); // __s4 = __v0 >> 24
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -9, gk, ss[5]); // __s5 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -29, gk, ss[6]); // __s6 = __v1 >> 29
    info.eval->rotate_rows(vs[1], -24, gk, ss[7]); // __s7 = __v1 >> 24
    info.eval->rotate_rows(vs[1], -10, gk, ss[8]); // __s8 = __v1 >> 10
    info.eval->rotate_rows(vs[1], -1, gk, ss[9]); // __s9 = __v1 >> 1
    
    // __t4 = blend(__v0@10000000001000000000100000000000, __s6@00000000000000000000000010000000)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[0], bits["10000000001000000000100000000000"], t4_1);
    info.eval->multiply_plain(ss[6], bits["00000000000000000000000010000000"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__s7@10000000000000000000000000000000, __s0@00000000001000000000000000000000, __s4@00000000000000000000100000000000, __v0@00000000000000000000000010000000)
    ctxt t5_1, t5_2, t5_3, t5_4;
    info.eval->multiply_plain(ss[7], bits["10000000000000000000000000000000"], t5_1);
    info.eval->multiply_plain(ss[0], bits["00000000001000000000000000000000"], t5_2);
    info.eval->multiply_plain(ss[4], bits["00000000000000000000100000000000"], t5_3);
    info.eval->multiply_plain(vs[0], bits["00000000000000000000000010000000"], t5_4);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4}, ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[2]); // __v2 = __t4 + __t5
    info.eval->rotate_rows(vs[2], -3, gk, ss[10]); // __s10 = __v2 >> 3
    info.eval->rotate_rows(vs[2], -26, gk, ss[11]); // __s11 = __v2 >> 26
    
    // __t6 = blend(__s6@00010000000000000000000000000000, __s3@00000000100000000000000000100000, __s2@00000000000001000000000000000000, __s5@00000000000000101000000000000000, __s4@00000000000000010000001100000000, __s8@00000000000000000001000000000000)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6;
    info.eval->multiply_plain(ss[6], bits["00010000000000000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[3], bits["00000000100000000000000000100000"], t6_2);
    info.eval->multiply_plain(ss[2], bits["00000000000001000000000000000000"], t6_3);
    info.eval->multiply_plain(ss[5], bits["00000000000000101000000000000000"], t6_4);
    info.eval->multiply_plain(ss[4], bits["00000000000000010000001100000000"], t6_5);
    info.eval->multiply_plain(ss[8], bits["00000000000000000001000000000000"], t6_6);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6}, ts[6]);
    
    
    // __t7 = blend(__s1@00010000000000000000000000000000, __s7@00000000100000100000000000000000, __s5@00000000000001000000000000000000, __s3@00000000000000010000001100000000, __s9@00000000000000001000000000000000, __v0@00000000000000000001000000000000, __s0@00000000000000000000000000100000)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7;
    info.eval->multiply_plain(ss[1], bits["00010000000000000000000000000000"], t7_1);
    info.eval->multiply_plain(ss[7], bits["00000000100000100000000000000000"], t7_2);
    info.eval->multiply_plain(ss[5], bits["00000000000001000000000000000000"], t7_3);
    info.eval->multiply_plain(ss[3], bits["00000000000000010000001100000000"], t7_4);
    info.eval->multiply_plain(ss[9], bits["00000000000000001000000000000000"], t7_5);
    info.eval->multiply_plain(vs[0], bits["00000000000000000001000000000000"], t7_6);
    info.eval->multiply_plain(ss[0], bits["00000000000000000000000000100000"], t7_7);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5, t7_6, t7_7}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -26, gk, ss[12]); // __s12 = __v3 >> 26
    info.eval->rotate_rows(vs[3], -3, gk, ss[13]); // __s13 = __v3 >> 3
    
    // __t8 = blend(__v3@00000000100000000000000000000000, __s4@00000000000001000000000000000000, __s12@00000000000000001000000000000000, __s13@00000000000000000010000000000000, __s8@00000000000000000000000100000000)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5;
    info.eval->multiply_plain(vs[3], bits["00000000100000000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[4], bits["00000000000001000000000000000000"], t8_2);
    info.eval->multiply_plain(ss[12], bits["00000000000000001000000000000000"], t8_3);
    info.eval->multiply_plain(ss[13], bits["00000000000000000010000000000000"], t8_4);
    info.eval->multiply_plain(ss[8], bits["00000000000000000000000100000000"], t8_5);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5}, ts[8]);
    
    
    // __t9 = blend(__s12@00000000100000000000000000000000, __s9@00000000000001000000000000000000, __v3@00000000000000001000000000000000, __s11@00000000000000000010000000000000, __s5@00000000000000000000000100000000)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5;
    info.eval->multiply_plain(ss[12], bits["00000000100000000000000000000000"], t9_1);
    info.eval->multiply_plain(ss[9], bits["00000000000001000000000000000000"], t9_2);
    info.eval->multiply_plain(vs[3], bits["00000000000000001000000000000000"], t9_3);
    info.eval->multiply_plain(ss[11], bits["00000000000000000010000000000000"], t9_4);
    info.eval->multiply_plain(ss[5], bits["00000000000000000000000100000000"], t9_5);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5}, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    info.eval->rotate_rows(vs[4], -10, gk, ss[14]); // __s14 = __v4 >> 10
    info.eval->rotate_rows(vs[4], -17, gk, ss[15]); // __s15 = __v4 >> 17
    
    // __t10 = blend(__v3@00000000000001000000000000000000, __v4@00000000000000000000000100000000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[3], bits["00000000000001000000000000000000"], t10_1);
    info.eval->multiply_plain(vs[4], bits["00000000000000000000000100000000"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    
    // __t11 = blend(__v4@00000000000001000000000000000000, __s10@00000000000000000000000100000000)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(vs[4], bits["00000000000001000000000000000000"], t11_1);
    info.eval->multiply_plain(ss[10], bits["00000000000000000000000100000000"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[5]); // __v5 = __t10 + __t11
    info.eval->rotate_rows(vs[5], -17, gk, ss[16]); // __s16 = __v5 >> 17
    
    // __t12 = blend(__s10@00010000000000000000000000000000, __s12@00000000000001000000000000000000)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(ss[10], bits["00010000000000000000000000000000"], t12_1);
    info.eval->multiply_plain(ss[12], bits["00000000000001000000000000000000"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    
    // __t13 = blend(__v3@00010000000000000000000000000000, __s10@00000000000001000000000000000000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[3], bits["00010000000000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[10], bits["00000000000001000000000000000000"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[6]); // __v6 = __t12 + __t13
    
    // __t14 = blend(__v6@00010000000000000000000000000000, __s16@00000000100000000000000000000000, __v5@00000000000001000000000000000000, __s13@00000000000000000000000000100000)
    ctxt t14_1, t14_2, t14_3, t14_4;
    info.eval->multiply_plain(vs[6], bits["00010000000000000000000000000000"], t14_1);
    info.eval->multiply_plain(ss[16], bits["00000000100000000000000000000000"], t14_2);
    info.eval->multiply_plain(vs[5], bits["00000000000001000000000000000000"], t14_3);
    info.eval->multiply_plain(ss[13], bits["00000000000000000000000000100000"], t14_4);
    info.eval->add_many({t14_1, t14_2, t14_3, t14_4}, ts[14]);
    
    
    // __t15 = blend(__s15@00010000000000000000000000000000, __v4@00000000100000000000000000000000, __v6@00000000000001000000000000000000, __v3@00000000000000000000000000100000)
    ctxt t15_1, t15_2, t15_3, t15_4;
    info.eval->multiply_plain(ss[15], bits["00010000000000000000000000000000"], t15_1);
    info.eval->multiply_plain(vs[4], bits["00000000100000000000000000000000"], t15_2);
    info.eval->multiply_plain(vs[6], bits["00000000000001000000000000000000"], t15_3);
    info.eval->multiply_plain(vs[3], bits["00000000000000000000000000100000"], t15_4);
    info.eval->add_many({t15_1, t15_2, t15_3, t15_4}, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[7]); // __v7 = __t14 * __t15
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -27, gk, ss[17]); // __s17 = __v7 >> 27
    info.eval->rotate_rows(vs[7], -22, gk, ss[18]); // __s18 = __v7 >> 22
    info.eval->add(vs[7], ss[14], vs[8]); // __v8 = __v7 + __s14
    info.eval->rotate_rows(vs[8], -9, gk, ss[19]); // __s19 = __v8 >> 9
    info.eval->multiply(ss[18], ss[19], vs[9]); // __v9 = __s18 * __s19
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->add(ss[17], vs[7], vs[10]); // __v10 = __s17 + __v7
    info.eval->multiply(vs[9], vs[10], vs[11]); // __v11 = __v9 * __v10
    info.eval->relinearize_inplace(vs[11], rk);
    return vs[11];
}
    