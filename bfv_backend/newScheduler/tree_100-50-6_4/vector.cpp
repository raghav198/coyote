
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000000000000000100000000000", info);
    add_bitstring(bits, "00000000000100000000100000000000", info);
    add_bitstring(bits, "00000000001010000000000000000000", info);
    add_bitstring(bits, "00100010000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000000100000", info);
    add_bitstring(bits, "00000010001000000000000000000000", info);
    add_bitstring(bits, "00000100000000000000000000000000", info);
    add_bitstring(bits, "00000000010000000000000000000000", info);
    add_bitstring(bits, "00000000000001000000000000000000", info);
    add_bitstring(bits, "00000010000000000000000000000000", info);
    add_bitstring(bits, "00100000000010000000000000000000", info);
    add_bitstring(bits, "00000000000010000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000010000000", info);
    add_bitstring(bits, "00000000000000000000000000101000", info);
    add_bitstring(bits, "00000000001000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000010000000100", info);
    add_bitstring(bits, "00000000000100000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000000001000", info);
    add_bitstring(bits, "00000000000000000000000000000100", info);
    add_bitstring(bits, "00000000100000000000010000000000", info);
    add_bitstring(bits, "00000000100000000000000000000000", info);
    add_bitstring(bits, "00000001000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000000010000", info);
    add_bitstring(bits, "00001000000000000000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(21);
    ts[0] = encrypt_input("0001101111100111011101111111111111111011101011001111101011011100111", info);
    ts[1] = encrypt_input("000110111111001110110010110111111111011110111011100111111111011100101", info);
    ts[2] = encrypt_input("1111111110001111110111011100000000111011111100011001111110", info);
    ts[3] = encrypt_input("11111111100011111101110110000000011001001110001100111010", info);
    ts[6] = encrypt_input("0000000000011000000000000000000000", info);
    ts[7] = encrypt_input("0000000000011100000000000000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[11];
    ctxt ss[18];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -31, gk, ss[0]); // __s0 = __v0 >> 31
    info.eval->rotate_rows(vs[0], -25, gk, ss[1]); // __s1 = __v0 >> 25
    info.eval->rotate_rows(vs[0], -5, gk, ss[2]); // __s2 = __v0 >> 5
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -5, gk, ss[3]); // __s3 = __v1 >> 5
    info.eval->rotate_rows(vs[1], -31, gk, ss[4]); // __s4 = __v1 >> 31
    
    // __t4 = blend(__s0@00100000000010000000000000000000, __s3@00000010000000000000000000000000, __s4@00000000100000000000000000000000, __v0@00000000001000000000000000000000, __s2@00000000000000000000010000000100)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5;
    info.eval->multiply_plain(ss[0], bits["00100000000010000000000000000000"], t4_1);
    info.eval->multiply_plain(ss[3], bits["00000010000000000000000000000000"], t4_2);
    info.eval->multiply_plain(ss[4], bits["00000000100000000000000000000000"], t4_3);
    info.eval->multiply_plain(vs[0], bits["00000000001000000000000000000000"], t4_4);
    info.eval->multiply_plain(ss[2], bits["00000000000000000000010000000100"], t4_5);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5}, ts[4]);
    
    
    // __t5 = blend(__v1@00100010000000000000000000000000, __v0@00000000100000000000010000000000, __s1@00000000001010000000000000000000, __s4@00000000000000000000000000000100)
    ctxt t5_1, t5_2, t5_3, t5_4;
    info.eval->multiply_plain(vs[1], bits["00100010000000000000000000000000"], t5_1);
    info.eval->multiply_plain(vs[0], bits["00000000100000000000010000000000"], t5_2);
    info.eval->multiply_plain(ss[1], bits["00000000001010000000000000000000"], t5_3);
    info.eval->multiply_plain(ss[4], bits["00000000000000000000000000000100"], t5_4);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4}, ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[2]); // __v2 = __t4 + __t5
    info.eval->rotate_rows(vs[2], -4, gk, ss[5]); // __s5 = __v2 >> 4
    info.eval->rotate_rows(vs[2], -17, gk, ss[6]); // __s6 = __v2 >> 17
    info.eval->rotate_rows(vs[2], -12, gk, ss[7]); // __s7 = __v2 >> 12
    
    // __t8 = blend(__s3@00000100000000000000000000000000, __s1@00000001000000000000000000000000, __s0@00000000000000000000000000010000, __t6@00000000000100000000000000000000)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(ss[3], bits["00000100000000000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[1], bits["00000001000000000000000000000000"], t8_2);
    info.eval->multiply_plain(ss[0], bits["00000000000000000000000000010000"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3, ts[6]}, ts[8]);
    
    
    // __t9 = blend(__s1@00000100000000000000000000000000, __v1@00000001000000000000000000000000, __s3@00000000000000000000000000010000, __t7@00000000000100000000000000000000)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(ss[1], bits["00000100000000000000000000000000"], t9_1);
    info.eval->multiply_plain(vs[1], bits["00000001000000000000000000000000"], t9_2);
    info.eval->multiply_plain(ss[3], bits["00000000000000000000000000010000"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3, ts[7]}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -12, gk, ss[8]); // __s8 = __v3 >> 12
    
    // __t10 = blend(__s0@00001000000000000000000000000000, __v3@00000000000100000000000000000000, __s2@00000000000000000000100000000000, __s1@00000000000000000000000010000000, __v0@00000000000000000000000000100000, __s3@00000000000000000000000000001000)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5, t10_6;
    info.eval->multiply_plain(ss[0], bits["00001000000000000000000000000000"], t10_1);
    info.eval->multiply_plain(vs[3], bits["00000000000100000000000000000000"], t10_2);
    info.eval->multiply_plain(ss[2], bits["00000000000000000000100000000000"], t10_3);
    info.eval->multiply_plain(ss[1], bits["00000000000000000000000010000000"], t10_4);
    info.eval->multiply_plain(vs[0], bits["00000000000000000000000000100000"], t10_5);
    info.eval->multiply_plain(ss[3], bits["00000000000000000000000000001000"], t10_6);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5, t10_6}, ts[10]);
    
    
    // __t11 = blend(__v0@00001000000000000000000000000000, __v1@00000000000100000000100000000000, __s0@00000000000000000000000010000000, __s4@00000000000000000000000000101000)
    ctxt t11_1, t11_2, t11_3, t11_4;
    info.eval->multiply_plain(vs[0], bits["00001000000000000000000000000000"], t11_1);
    info.eval->multiply_plain(vs[1], bits["00000000000100000000100000000000"], t11_2);
    info.eval->multiply_plain(ss[0], bits["00000000000000000000000010000000"], t11_3);
    info.eval->multiply_plain(ss[4], bits["00000000000000000000000000101000"], t11_4);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[4]); // __v4 = __t10 * __t11
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -4, gk, ss[9]); // __s9 = __v4 >> 4
    info.eval->rotate_rows(vs[4], -17, gk, ss[10]); // __s10 = __v4 >> 17
    info.eval->rotate_rows(vs[4], -12, gk, ss[11]); // __s11 = __v4 >> 12
    
    // __t12 = blend(__s10@00000100000000000000000000000000, __s5@00000010001000000000000000000000, __s9@00000000100000000000000000000000, __v4@00000000000100000000000000000000, __v2@00000000000010000000000000000000)
    ctxt t12_1, t12_2, t12_3, t12_4, t12_5;
    info.eval->multiply_plain(ss[10], bits["00000100000000000000000000000000"], t12_1);
    info.eval->multiply_plain(ss[5], bits["00000010001000000000000000000000"], t12_2);
    info.eval->multiply_plain(ss[9], bits["00000000100000000000000000000000"], t12_3);
    info.eval->multiply_plain(vs[4], bits["00000000000100000000000000000000"], t12_4);
    info.eval->multiply_plain(vs[2], bits["00000000000010000000000000000000"], t12_5);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4, t12_5}, ts[12]);
    
    
    // __t13 = blend(__v3@00000100000000000000000000000000, __s6@00000010000000000000000000000000, __s11@00000000100000000000000000000000, __v2@00000000001000000000000000000000, __s10@00000000000100000000000000000000, __s5@00000000000010000000000000000000)
    ctxt t13_1, t13_2, t13_3, t13_4, t13_5, t13_6;
    info.eval->multiply_plain(vs[3], bits["00000100000000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[6], bits["00000010000000000000000000000000"], t13_2);
    info.eval->multiply_plain(ss[11], bits["00000000100000000000000000000000"], t13_3);
    info.eval->multiply_plain(vs[2], bits["00000000001000000000000000000000"], t13_4);
    info.eval->multiply_plain(ss[10], bits["00000000000100000000000000000000"], t13_5);
    info.eval->multiply_plain(ss[5], bits["00000000000010000000000000000000"], t13_6);
    info.eval->add_many({t13_1, t13_2, t13_3, t13_4, t13_5, t13_6}, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[5]); // __v5 = __t12 + __t13
    info.eval->rotate_rows(vs[5], -2, gk, ss[12]); // __s12 = __v5 >> 2
    info.eval->rotate_rows(vs[5], -1, gk, ss[13]); // __s13 = __v5 >> 1
    
    // __t14 = blend(__v3@00000001000000000000000000000000, __s10@00000000010000000000000000000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[3], bits["00000001000000000000000000000000"], t14_1);
    info.eval->multiply_plain(ss[10], bits["00000000010000000000000000000000"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__s8@00000001000000000000000000000000, __s7@00000000010000000000000000000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(ss[8], bits["00000001000000000000000000000000"], t15_1);
    info.eval->multiply_plain(ss[7], bits["00000000010000000000000000000000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[6]); // __v6 = __t14 * __t15
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -4, gk, ss[14]); // __s14 = __v6 >> 4
    
    // __t16 = blend(__v6@00000001000000000000000000000000, __s13@00000000000010000000000000000000)
    ctxt t16_1, t16_2;
    info.eval->multiply_plain(vs[6], bits["00000001000000000000000000000000"], t16_1);
    info.eval->multiply_plain(ss[13], bits["00000000000010000000000000000000"], t16_2);
    info.eval->add(t16_1, t16_2, ts[16]);
    
    info.eval->add(ts[16], ss[12], vs[7]); // __v7 = __t16 + __s12
    info.eval->rotate_rows(vs[7], -5, gk, ss[15]); // __s15 = __v7 >> 5
    
    // __t17 = blend(__v5@00000000100000000000000000000000, __s13@00000000000001000000000000000000)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(vs[5], bits["00000000100000000000000000000000"], t17_1);
    info.eval->multiply_plain(ss[13], bits["00000000000001000000000000000000"], t17_2);
    info.eval->add(t17_1, t17_2, ts[17]);
    
    
    // __t18 = blend(__s12@00000000100000000000000000000000, __s14@00000000000001000000000000000000)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(ss[12], bits["00000000100000000000000000000000"], t18_1);
    info.eval->multiply_plain(ss[14], bits["00000000000001000000000000000000"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    info.eval->multiply(ts[17], ts[18], vs[8]); // __v8 = __t17 * __t18
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->rotate_rows(vs[8], -5, gk, ss[16]); // __s16 = __v8 >> 5
    
    // __t19 = blend(__s15@00000000000010000000000000000000, __v8@00000000000001000000000000000000)
    ctxt t19_1, t19_2;
    info.eval->multiply_plain(ss[15], bits["00000000000010000000000000000000"], t19_1);
    info.eval->multiply_plain(vs[8], bits["00000000000001000000000000000000"], t19_2);
    info.eval->add(t19_1, t19_2, ts[19]);
    
    
    // __t20 = blend(__v7@00000000000010000000000000000000, __s16@00000000000001000000000000000000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[7], bits["00000000000010000000000000000000"], t20_1);
    info.eval->multiply_plain(ss[16], bits["00000000000001000000000000000000"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    info.eval->add(ts[19], ts[20], vs[9]); // __v9 = __t19 + __t20
    info.eval->rotate_rows(vs[9], -1, gk, ss[17]); // __s17 = __v9 >> 1
    info.eval->add(vs[9], ss[17], vs[10]); // __v10 = __v9 + __s17
    return vs[10];
}
    