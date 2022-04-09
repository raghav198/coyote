
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000000000000000001000000010", info);
    add_bitstring(bits, "00000000000100000000000000000000", info);
    add_bitstring(bits, "00000000000000000000010000000000", info);
    add_bitstring(bits, "00010000000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000100000000000", info);
    add_bitstring(bits, "00000010000000000000000000000010", info);
    add_bitstring(bits, "00000000000000000000000100000000", info);
    add_bitstring(bits, "00000000000000000000000000000010", info);
    add_bitstring(bits, "00000000000000100000000000000000", info);
    add_bitstring(bits, "00000000000000010000000010000000", info);
    add_bitstring(bits, "00000000000001000000000000000000", info);
    add_bitstring(bits, "00000000000000001000001000000000", info);
    add_bitstring(bits, "00000000001000000000000000000000", info);
    add_bitstring(bits, "00000000000000000001000000000000", info);
    add_bitstring(bits, "00000000000000000000001000000000", info);
    add_bitstring(bits, "00000001000000000000000000000000", info);
    add_bitstring(bits, "00000000000000010000000000000000", info);
    add_bitstring(bits, "00000000000000000000000000001000", info);
    add_bitstring(bits, "00000010000000000000000000000000", info);
    add_bitstring(bits, "00000010000000000000000100000000", info);
    add_bitstring(bits, "00000000000000001000000000000000", info);
    add_bitstring(bits, "00000000000000000000000010000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(18);
    ts[0] = encrypt_input("111010101111110111111001010111011011001100011101110010101101110111", info);
    ts[1] = encrypt_input("11001111011101111010011101010111111011100011101110011101111100110", info);
    ts[2] = encrypt_input("01110000001101110101101100110111111101011011111100001110", info);
    ts[3] = encrypt_input("0111000000111100101110111001110111111110111011111100001110", info);
    ts[6] = encrypt_input("000000111000000001110000000000000000", info);
    ts[7] = encrypt_input("000000111000000001110000000000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[13];
    ctxt ss[21];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -6, gk, ss[0]); // __s0 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -4, gk, ss[1]); // __s1 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -3, gk, ss[2]); // __s2 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -23, gk, ss[3]); // __s3 = __v0 >> 23
    info.eval->rotate_rows(vs[0], -26, gk, ss[4]); // __s4 = __v0 >> 26
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -6, gk, ss[5]); // __s5 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -3, gk, ss[6]); // __s6 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -26, gk, ss[7]); // __s7 = __v1 >> 26
    info.eval->rotate_rows(vs[1], -4, gk, ss[8]); // __s8 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -23, gk, ss[9]); // __s9 = __v1 >> 23
    
    // __t4 = blend(__s1@00000010000000000000000000000010, __s2@00000000001000000000000000000000, __s6@00000000000100000000000000000000, __v1@00000000000001000000000000000000, __v0@00000000000000100000000000000000, __s8@00000000000000000000100000000000, __s3@00000000000000000000001000000000, __s0@00000000000000000000000100000000, __s5@00000000000000000000000000001000)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, t4_7, t4_8, t4_9;
    info.eval->multiply_plain(ss[1], bits["00000010000000000000000000000010"], t4_1);
    info.eval->multiply_plain(ss[2], bits["00000000001000000000000000000000"], t4_2);
    info.eval->multiply_plain(ss[6], bits["00000000000100000000000000000000"], t4_3);
    info.eval->multiply_plain(vs[1], bits["00000000000001000000000000000000"], t4_4);
    info.eval->multiply_plain(vs[0], bits["00000000000000100000000000000000"], t4_5);
    info.eval->multiply_plain(ss[8], bits["00000000000000000000100000000000"], t4_6);
    info.eval->multiply_plain(ss[3], bits["00000000000000000000001000000000"], t4_7);
    info.eval->multiply_plain(ss[0], bits["00000000000000000000000100000000"], t4_8);
    info.eval->multiply_plain(ss[5], bits["00000000000000000000000000001000"], t4_9);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, t4_7, t4_8, t4_9}, ts[4]);
    
    
    // __t5 = blend(__v0@00000010000000000000000100000000, __s0@00000000001000000000000000000000, __s9@00000000000100000000000000000000, __s2@00000000000001000000000000000000, __s6@00000000000000100000000000000000, __s3@00000000000000000000100000000000, __s4@00000000000000000000001000000000, __s8@00000000000000000000000000001000, __v1@00000000000000000000000000000010)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5, t5_6, t5_7, t5_8, t5_9;
    info.eval->multiply_plain(vs[0], bits["00000010000000000000000100000000"], t5_1);
    info.eval->multiply_plain(ss[0], bits["00000000001000000000000000000000"], t5_2);
    info.eval->multiply_plain(ss[9], bits["00000000000100000000000000000000"], t5_3);
    info.eval->multiply_plain(ss[2], bits["00000000000001000000000000000000"], t5_4);
    info.eval->multiply_plain(ss[6], bits["00000000000000100000000000000000"], t5_5);
    info.eval->multiply_plain(ss[3], bits["00000000000000000000100000000000"], t5_6);
    info.eval->multiply_plain(ss[4], bits["00000000000000000000001000000000"], t5_7);
    info.eval->multiply_plain(ss[8], bits["00000000000000000000000000001000"], t5_8);
    info.eval->multiply_plain(vs[1], bits["00000000000000000000000000000010"], t5_9);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5, t5_6, t5_7, t5_8, t5_9}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -15, gk, ss[10]); // __s10 = __v2 >> 15
    info.eval->rotate_rows(vs[2], -13, gk, ss[11]); // __s11 = __v2 >> 13
    info.eval->rotate_rows(vs[2], -2, gk, ss[12]); // __s12 = __v2 >> 2
    
    // __t8 = blend(__s3@00010000000000000000000000000000, __s1@00000001000000000000000000000000, __s6@00000000000000000000010000000000, __t6@00000010000000010000000000000000)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(ss[3], bits["00010000000000000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[1], bits["00000001000000000000000000000000"], t8_2);
    info.eval->multiply_plain(ss[6], bits["00000000000000000000010000000000"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3, ts[6]}, ts[8]);
    
    
    // __t9 = blend(__s7@00010000000000000000000000000000, __s5@00000001000000000000000000000000, __s0@00000000000000000000010000000000, __t7@00000010000000010000000000000000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(ss[7], bits["00010000000000000000000000000000"], t9_1);
    info.eval->multiply_plain(ss[5], bits["00000001000000000000000000000000"], t9_2);
    info.eval->multiply_plain(ss[0], bits["00000000000000000000010000000000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3, ts[7]}, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[3]); // __v3 = __t8 + __t9
    info.eval->rotate_rows(vs[3], -13, gk, ss[13]); // __s13 = __v3 >> 13
    info.eval->rotate_rows(vs[3], -15, gk, ss[14]); // __s14 = __v3 >> 15
    
    // __t10 = blend(__v3@00000010000000000000000000000000, __s4@00000000000000010000000000000000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[3], bits["00000010000000000000000000000000"], t10_1);
    info.eval->multiply_plain(ss[4], bits["00000000000000010000000000000000"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    
    // __t11 = blend(__s0@00000010000000000000000000000000, __v3@00000000000000010000000000000000)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(ss[0], bits["00000010000000000000000000000000"], t11_1);
    info.eval->multiply_plain(vs[3], bits["00000000000000010000000000000000"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[4]); // __v4 = __t10 + __t11
    info.eval->rotate_rows(vs[4], -13, gk, ss[15]); // __s15 = __v4 >> 13
    info.eval->multiply(vs[2], ss[11], vs[5]); // __v5 = __v2 * __s11
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -1, gk, ss[16]); // __s16 = __v5 >> 1
    
    // __t12 = blend(__s12@00000000000000010000000010000000, __s7@00000000000000000001000000000000, __s10@00000000000000000000010000000000, __s14@00000000000000000000001000000000, __v2@00000000000000000000000000000010)
    ctxt t12_1, t12_2, t12_3, t12_4, t12_5;
    info.eval->multiply_plain(ss[12], bits["00000000000000010000000010000000"], t12_1);
    info.eval->multiply_plain(ss[7], bits["00000000000000000001000000000000"], t12_2);
    info.eval->multiply_plain(ss[10], bits["00000000000000000000010000000000"], t12_3);
    info.eval->multiply_plain(ss[14], bits["00000000000000000000001000000000"], t12_4);
    info.eval->multiply_plain(vs[2], bits["00000000000000000000000000000010"], t12_5);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4, t12_5}, ts[12]);
    
    
    // __t13 = blend(__v4@00000000000000010000000000000000, __v1@00000000000000000001000000000000, __v3@00000000000000000000010000000000, __s12@00000000000000000000001000000010, __s11@00000000000000000000000010000000)
    ctxt t13_1, t13_2, t13_3, t13_4, t13_5;
    info.eval->multiply_plain(vs[4], bits["00000000000000010000000000000000"], t13_1);
    info.eval->multiply_plain(vs[1], bits["00000000000000000001000000000000"], t13_2);
    info.eval->multiply_plain(vs[3], bits["00000000000000000000010000000000"], t13_3);
    info.eval->multiply_plain(ss[12], bits["00000000000000000000001000000010"], t13_4);
    info.eval->multiply_plain(ss[11], bits["00000000000000000000000010000000"], t13_5);
    info.eval->add_many({t13_1, t13_2, t13_3, t13_4, t13_5}, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[6]); // __v6 = __t12 + __t13
    info.eval->rotate_rows(vs[6], -1, gk, ss[17]); // __s17 = __v6 >> 1
    info.eval->add(vs[6], ss[15], vs[7]); // __v7 = __v6 + __s15
    info.eval->rotate_rows(vs[7], -11, gk, ss[18]); // __s18 = __v7 >> 11
    
    // __t14 = blend(__s12@00000000000000001000000000000000, __s16@00000000000000000000000010000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(ss[12], bits["00000000000000001000000000000000"], t14_1);
    info.eval->multiply_plain(ss[16], bits["00000000000000000000000010000000"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__s13@00000000000000001000000000000000, __v6@00000000000000000000000010000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(ss[13], bits["00000000000000001000000000000000"], t15_1);
    info.eval->multiply_plain(vs[6], bits["00000000000000000000000010000000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->add(ts[14], ts[15], vs[8]); // __v8 = __t14 + __t15
    
    // __t16 = blend(__v8@00000000000000001000000000000000, __v6@00000000000000000000001000000000, __s18@00000000000000000000000000000010)
    ctxt t16_1, t16_2, t16_3;
    info.eval->multiply_plain(vs[8], bits["00000000000000001000000000000000"], t16_1);
    info.eval->multiply_plain(vs[6], bits["00000000000000000000001000000000"], t16_2);
    info.eval->multiply_plain(ss[18], bits["00000000000000000000000000000010"], t16_3);
    info.eval->add_many({t16_1, t16_2, t16_3}, ts[16]);
    
    
    // __t17 = blend(__s17@00000000000000001000001000000000, __v6@00000000000000000000000000000010)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(ss[17], bits["00000000000000001000001000000000"], t17_1);
    info.eval->multiply_plain(vs[6], bits["00000000000000000000000000000010"], t17_2);
    info.eval->add(t17_1, t17_2, ts[17]);
    
    info.eval->multiply(ts[16], ts[17], vs[9]); // __v9 = __t16 * __t17
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->rotate_rows(vs[9], -8, gk, ss[19]); // __s19 = __v9 >> 8
    info.eval->multiply(ss[19], vs[8], vs[10]); // __v10 = __s19 * __v8
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->rotate_rows(vs[10], -6, gk, ss[20]); // __s20 = __v10 >> 6
    info.eval->add(vs[9], ss[19], vs[11]); // __v11 = __v9 + __s19
    info.eval->multiply(ss[20], vs[11], vs[12]); // __v12 = __s20 * __v11
    info.eval->relinearize_inplace(vs[12], rk);
    return vs[12];
}
    