
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000010000001000000000", info);
    add_bitstring(bits, "00000000000000010001000", info);
    add_bitstring(bits, "00000000000100000000000", info);
    add_bitstring(bits, "00000101001100000001000", info);
    add_bitstring(bits, "00100000000000000000000", info);
    add_bitstring(bits, "00000001000000000000000", info);
    add_bitstring(bits, "00000100000000000000000", info);
    add_bitstring(bits, "00000000000000000010000", info);
    add_bitstring(bits, "00000000000001000000000", info);
    add_bitstring(bits, "00000010000000000000000", info);
    add_bitstring(bits, "00000000000000000001000", info);
    add_bitstring(bits, "00000000100001000000000", info);
    add_bitstring(bits, "00000100000100110000000", info);
    add_bitstring(bits, "00000000001000010000000", info);
    add_bitstring(bits, "00000000100000000000000", info);
    add_bitstring(bits, "00000000000000110000000", info);
    add_bitstring(bits, "00000000101001100100000", info);
    add_bitstring(bits, "00000001000000000101000", info);
    add_bitstring(bits, "00000000001000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(23);
    ts[0] = encrypt_input("10111011110011001111010", info);
    ts[1] = encrypt_input("11111111111111011111111111111111111111111111111111111111101111111111111111111111111111111111111111111111111111111100111111111111111111111111111100111111111111111111111111111111111111111111111111111111110111111111111110", info);
    ts[2] = encrypt_input("011111111111111000111111111111110000011111111111111001111111111111111111111111111000011111111111111011111111111111", info);
    ts[3] = encrypt_input("01111111111111111111111111100111111111111100000111111111111100111111111111111111111111110000111111111111101111111111111", info);
    ts[5] = encrypt_input("000000001111111111111100000000000000", info);
    ts[6] = encrypt_input("00000111111111111101111111111111111111111111101111111111111111111111111100000111111111111111111111111111111111111111000", info);
    ts[10] = encrypt_input("000000001111111111111100000111111111111110011111111111111011111111111111000", info);
    ts[13] = encrypt_input("000000000000011111111111111000000000", info);
    ts[16] = encrypt_input("000000001111111111111100000000000000", info);
    ts[21] = encrypt_input("000000000001111111111111100000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[13];
    ctxt ss[15];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -10, gk, ss[0]); // __s0 = __v0 >> 10
    info.eval->rotate_rows(vs[0], -6, gk, ss[1]); // __s1 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -20, gk, ss[2]); // __s2 = __v0 >> 20
    info.eval->rotate_rows(vs[0], -13, gk, ss[3]); // __s3 = __v0 >> 13
    
    // __t4 = blend(__v0@00100000000000000000000, __t2@01000100000100110000101)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["00100000000000000000000"], t4_1);
    info.eval->add(t4_1, ts[2], ts[4]);
    
    info.eval->multiply(ts[4], ts[3], vs[1]); // __v1 = __t4 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -6, gk, ss[4]); // __s4 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -13, gk, ss[5]); // __s5 = __v1 >> 13
    info.eval->rotate_rows(vs[1], -20, gk, ss[6]); // __s6 = __v1 >> 20
    
    // __t7 = blend(__s2@00000100000000000000000, __v0@00000001000000000101000, __s0@00000000001000000000000, __s3@00000000000100000000000, __s1@00000000000000000010000, __t5@00000000100000000000000)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5;
    info.eval->multiply_plain(ss[2], bits["00000100000000000000000"], t7_1);
    info.eval->multiply_plain(vs[0], bits["00000001000000000101000"], t7_2);
    info.eval->multiply_plain(ss[0], bits["00000000001000000000000"], t7_3);
    info.eval->multiply_plain(ss[3], bits["00000000000100000000000"], t7_4);
    info.eval->multiply_plain(ss[1], bits["00000000000000000010000"], t7_5);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5, ts[5]}, ts[7]);
    
    info.eval->multiply(ts[7], ts[6], vs[2]); // __v2 = __t7 * __t6
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -20, gk, ss[7]); // __s7 = __v2 >> 20
    info.eval->add(vs[2], ss[4], vs[3]); // __v3 = __v2 + __s4
    
    // __t8 = blend(__v1@00000100000100110000000, __s4@00000001000000000000000, __s5@00000000001000000000000, __s6@00000000000000000001000)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(vs[1], bits["00000100000100110000000"], t8_1);
    info.eval->multiply_plain(ss[4], bits["00000001000000000000000"], t8_2);
    info.eval->multiply_plain(ss[5], bits["00000000001000000000000"], t8_3);
    info.eval->multiply_plain(ss[6], bits["00000000000000000001000"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__v2@00000101001100000001000, __s7@00000000000000110000000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[2], bits["00000101001100000001000"], t9_1);
    info.eval->multiply_plain(ss[7], bits["00000000000000110000000"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    info.eval->rotate_rows(vs[4], -3, gk, ss[8]); // __s8 = __v4 >> 3
    
    // __t11 = blend(__s1@00000000001000010000000, __s0@00000000000001000000000, __t10@00000000100000100101000)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(ss[1], bits["00000000001000010000000"], t11_1);
    info.eval->multiply_plain(ss[0], bits["00000000000001000000000"], t11_2);
    info.eval->add_many({t11_1, t11_2, ts[10]}, ts[11]);
    
    
    // __t12 = blend(__s8@00000000101001100100000, __v4@00000000000000010001000)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(ss[8], bits["00000000101001100100000"], t12_1);
    info.eval->multiply_plain(vs[4], bits["00000000000000010001000"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    info.eval->multiply(ts[11], ts[12], vs[5]); // __v5 = __t11 * __t12
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -19, gk, ss[9]); // __s9 = __v5 >> 19
    info.eval->add(ss[9], vs[5], vs[6]); // __v6 = __s9 + __v5
    info.eval->rotate_rows(vs[6], -21, gk, ss[10]); // __s10 = __v6 >> 21
    
    // __t14 = blend(__s3@00000000100000000000000, __t13@00000000000001000000000)
    ctxt t14_1;
    info.eval->multiply_plain(ss[3], bits["00000000100000000000000"], t14_1);
    info.eval->add(t14_1, ts[13], ts[14]);
    
    
    // __t15 = blend(__v3@00000000100000000000000, __v6@00000000000001000000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(vs[3], bits["00000000100000000000000"], t15_1);
    info.eval->multiply_plain(vs[6], bits["00000000000001000000000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[7]); // __v7 = __t14 * __t15
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -21, gk, ss[11]); // __s11 = __v7 >> 21
    info.eval->add(vs[5], vs[7], vs[8]); // __v8 = __v5 + __v7
    info.eval->rotate_rows(vs[8], -21, gk, ss[12]); // __s12 = __v8 >> 21
    
    // __t17 = blend(__v0@00000010000001000000000, __t16@00000000100000000000000)
    ctxt t17_1;
    info.eval->multiply_plain(vs[0], bits["00000010000001000000000"], t17_1);
    info.eval->add(t17_1, ts[16], ts[17]);
    
    
    // __t18 = blend(__s12@00000010000000000000000, __s10@00000000100001000000000)
    ctxt t18_1, t18_2;
    info.eval->multiply_plain(ss[12], bits["00000010000000000000000"], t18_1);
    info.eval->multiply_plain(ss[10], bits["00000000100001000000000"], t18_2);
    info.eval->add(t18_1, t18_2, ts[18]);
    
    info.eval->multiply(ts[17], ts[18], vs[9]); // __v9 = __t17 * __t18
    info.eval->relinearize_inplace(vs[9], rk);
    info.eval->rotate_rows(vs[9], -5, gk, ss[13]); // __s13 = __v9 >> 5
    
    // __t19 = blend(__s11@00000000000100000000000, __s13@00000000000001000000000)
    ctxt t19_1, t19_2;
    info.eval->multiply_plain(ss[11], bits["00000000000100000000000"], t19_1);
    info.eval->multiply_plain(ss[13], bits["00000000000001000000000"], t19_2);
    info.eval->add(t19_1, t19_2, ts[19]);
    
    
    // __t20 = blend(__s13@00000000000100000000000, __v9@00000000000001000000000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(ss[13], bits["00000000000100000000000"], t20_1);
    info.eval->multiply_plain(vs[9], bits["00000000000001000000000"], t20_2);
    info.eval->add(t20_1, t20_2, ts[20]);
    
    info.eval->add(ts[19], ts[20], vs[10]); // __v10 = __t19 + __t20
    
    // __t22 = blend(__s2@00000000000001000000000, __t21@00000000000100000000000)
    ctxt t22_1;
    info.eval->multiply_plain(ss[2], bits["00000000000001000000000"], t22_1);
    info.eval->add(t22_1, ts[21], ts[22]);
    
    info.eval->multiply(ts[22], vs[10], vs[11]); // __v11 = __t22 * __v10
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->rotate_rows(vs[11], -21, gk, ss[14]); // __s14 = __v11 >> 21
    info.eval->add(vs[11], ss[14], vs[12]); // __v12 = __v11 + __s14
    return vs[12];
}
    