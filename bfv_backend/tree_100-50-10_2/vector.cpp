
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000000001", info);
    add_bitstring(bits, "01000000000000", info);
    add_bitstring(bits, "00100000000000", info);
    add_bitstring(bits, "00000100000010", info);
    add_bitstring(bits, "00000010001000", info);
    add_bitstring(bits, "00100001000000", info);
    add_bitstring(bits, "00010000010000", info);
    add_bitstring(bits, "00000000010000", info);
    add_bitstring(bits, "00000000001000", info);
    add_bitstring(bits, "00000100000000", info);
    add_bitstring(bits, "00000000000010", info);
    add_bitstring(bits, "00000010000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(30);
    ts[0] = encrypt_input("111110111011100111001010111111", info);
    ts[1] = encrypt_input("11111111101110011100111011101", info);
    ts[2] = encrypt_input("00010001110111101011100", info);
    ts[3] = encrypt_input("0001100011101111011100", info);
    ts[4] = encrypt_input("0000000000001110", info);
    ts[5] = encrypt_input("0111011000011100001110", info);
    ts[8] = encrypt_input("0000000000101000", info);
    ts[9] = encrypt_input("0000011100000000", info);
    ts[12] = encrypt_input("011100000000001110", info);
    ts[15] = encrypt_input("0000001110000000", info);
    ts[16] = encrypt_input("0000011100000000", info);
    ts[19] = encrypt_input("0111000000000000", info);
    ts[22] = encrypt_input("0000011100000000", info);
    ts[23] = encrypt_input("0111000000000000", info);
    ts[24] = encrypt_input("0101000000000000", info);
    ts[25] = encrypt_input("0000011100000000", info);
    ts[26] = encrypt_input("0000011100000000", info);
    ts[27] = encrypt_input("01011000000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[17];
    ctxt ss[7];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -1, gk, ss[1]); // __s1 = __v1 >> 1
    
    // __t6 = blend(__s0@01000000000000, __v0@00100001000000, __v1@00010000010000, __t4@00000000000010)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(ss[0], bits["01000000000000"], t6_1);
    info.eval->multiply_plain(vs[0], bits["00100001000000"], t6_2);
    info.eval->multiply_plain(vs[1], bits["00010000010000"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__s0@00100000000000, __s1@00000000010000, __t5@01010001000010)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[0], bits["00100000000000"], t7_1);
    info.eval->multiply_plain(ss[1], bits["00000000010000"], t7_2);
    info.eval->add_many({t7_1, t7_2, ts[5]}, ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[2]); // __v2 = __t6 + __t7
    info.eval->rotate_rows(vs[2], -3, gk, ss[2]); // __s2 = __v2 >> 3
    
    // __t10 = blend(__s0@00000100000000, __v2@00000000000010, __v0@00000000000001, __t8@00000000001000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(ss[0], bits["00000100000000"], t10_1);
    info.eval->multiply_plain(vs[2], bits["00000000000010"], t10_2);
    info.eval->multiply_plain(vs[0], bits["00000000000001"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3, ts[8]}, ts[10]);
    
    
    // __t11 = blend(__v0@00000000001000, __s1@00000000000010, __s0@00000000000001, __t9@00000100000000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[0], bits["00000000001000"], t11_1);
    info.eval->multiply_plain(ss[1], bits["00000000000010"], t11_2);
    info.eval->multiply_plain(ss[0], bits["00000000000001"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3, ts[9]}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[3]); // __v3 = __t10 * __t11
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -11, gk, ss[3]); // __s3 = __v3 >> 11
    
    // __t13 = blend(__v2@01000000000000, __s2@00000100000010)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[2], bits["01000000000000"], t13_1);
    info.eval->multiply_plain(ss[2], bits["00000100000010"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    
    // __t14 = blend(__v3@00000100000000, __t12@01000000000010)
    ctxt t14_1;
    info.eval->multiply_plain(vs[3], bits["00000100000000"], t14_1);
    info.eval->add(t14_1, ts[12], ts[14]);
    
    info.eval->add(ts[13], ts[14], vs[4]); // __v4 = __t13 + __t14
    
    // __t17 = blend(__v4@00000100000000, __s3@00000000001000, __t15@00000010000000)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(vs[4], bits["00000100000000"], t17_1);
    info.eval->multiply_plain(ss[3], bits["00000000001000"], t17_2);
    info.eval->add_many({t17_1, t17_2, ts[15]}, ts[17]);
    
    
    // __t18 = blend(__s2@00000010001000, __t16@00000100000000)
    ctxt t18_1;
    info.eval->multiply_plain(ss[2], bits["00000010001000"], t18_1);
    info.eval->add(t18_1, ts[16], ts[18]);
    
    info.eval->multiply(ts[17], ts[18], vs[5]); // __v5 = __t17 * __t18
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t20 = blend(__v1@00000010000000, __v3@00000000001000, __t19@01000000000000)
    ctxt t20_1, t20_2;
    info.eval->multiply_plain(vs[1], bits["00000010000000"], t20_1);
    info.eval->multiply_plain(vs[3], bits["00000000001000"], t20_2);
    info.eval->add_many({t20_1, t20_2, ts[19]}, ts[20]);
    
    
    // __t21 = blend(__v4@01000000000000, __v5@00000010001000)
    ctxt t21_1, t21_2;
    info.eval->multiply_plain(vs[4], bits["01000000000000"], t21_1);
    info.eval->multiply_plain(vs[5], bits["00000010001000"], t21_2);
    info.eval->add(t21_1, t21_2, ts[21]);
    
    info.eval->multiply(ts[20], ts[21], vs[6]); // __v6 = __t20 * __t21
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -9, gk, ss[4]); // __s4 = __v6 >> 9
    info.eval->multiply(ss[4], ts[22], vs[7]); // __v7 = __s4 * __t22
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->add(vs[6], ts[23], vs[8]); // __v8 = __v6 + __t23
    info.eval->add(vs[8], ts[24], vs[9]); // __v9 = __v8 + __t24
    info.eval->multiply(vs[5], ts[25], vs[10]); // __v10 = __v5 * __t25
    info.eval->relinearize_inplace(vs[10], rk);
    info.eval->multiply(vs[7], vs[10], vs[11]); // __v11 = __v7 * __v10
    info.eval->relinearize_inplace(vs[11], rk);
    
    // __t28 = blend(__s4@01000000000000, __t26@00000100000000)
    ctxt t28_1;
    info.eval->multiply_plain(ss[4], bits["01000000000000"], t28_1);
    info.eval->add(t28_1, ts[26], ts[28]);
    
    
    // __t29 = blend(__v11@00000100000000, __t27@01000000000000)
    ctxt t29_1;
    info.eval->multiply_plain(vs[11], bits["00000100000000"], t29_1);
    info.eval->add(t29_1, ts[27], ts[29]);
    
    info.eval->multiply(ts[28], ts[29], vs[12]); // __v12 = __t28 * __t29
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -10, gk, ss[5]); // __s5 = __v12 >> 10
    info.eval->add(vs[9], vs[12], vs[13]); // __v13 = __v9 + __v12
    info.eval->multiply(vs[13], ss[5], vs[14]); // __v14 = __v13 * __s5
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->rotate_rows(vs[14], -11, gk, ss[6]); // __s6 = __v14 >> 11
    info.eval->multiply(vs[4], ss[6], vs[15]); // __v15 = __v4 * __s6
    info.eval->relinearize_inplace(vs[15], rk);
    info.eval->multiply(vs[15], vs[3], vs[16]); // __v16 = __v15 * __v3
    info.eval->relinearize_inplace(vs[16], rk);
    return vs[16];
}
    