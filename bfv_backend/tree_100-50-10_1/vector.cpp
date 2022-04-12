
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000000010000", info);
    add_bitstring(bits, "0100000000000", info);
    add_bitstring(bits, "0000000100000", info);
    add_bitstring(bits, "0000000101000", info);
    add_bitstring(bits, "0000000001000", info);
    add_bitstring(bits, "0000010000000", info);
    add_bitstring(bits, "0000000000001", info);
    add_bitstring(bits, "0000000000010", info);
    add_bitstring(bits, "0001100000000", info);
    add_bitstring(bits, "0000000100010", info);
    add_bitstring(bits, "0010000000000", info);
    add_bitstring(bits, "0001010000000", info);
    add_bitstring(bits, "0010000000100", info);
    add_bitstring(bits, "0000001100000", info);
    add_bitstring(bits, "0000001000000", info);
    add_bitstring(bits, "0000100000000", info);
    add_bitstring(bits, "0001000001000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(33);
    ts[0] = encrypt_input("001101111111111100111110", info);
    ts[1] = encrypt_input("0011101011111101111001111110", info);
    ts[2] = encrypt_input("111110100000011111100101", info);
    ts[3] = encrypt_input("1111110111000011111000111", info);
    ts[4] = encrypt_input("000000000111000", info);
    ts[5] = encrypt_input("0001110111000000111", info);
    ts[8] = encrypt_input("00000000111001110", info);
    ts[9] = encrypt_input("011111100001010011100", info);
    ts[12] = encrypt_input("000000000001110", info);
    ts[13] = encrypt_input("000011100000000", info);
    ts[16] = encrypt_input("011100000000000", info);
    ts[19] = encrypt_input("000000000001110", info);
    ts[20] = encrypt_input("000000111000000", info);
    ts[23] = encrypt_input("000001110000000", info);
    ts[26] = encrypt_input("011100000000000", info);
    ts[27] = encrypt_input("001110000000000", info);
    ts[30] = encrypt_input("001110000000000", info);
    ts[31] = encrypt_input("000000111000000", info);
    ts[32] = encrypt_input("001110000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    seal::GaloisKeys& gk = info.keys->gk;

    ctxt vs[16];
    ctxt ss[11];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -7, gk, ss[1]); // __s1 = __v0 >> 7
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -2, gk, ss[2]); // __s2 = __v1 >> 2
    
    // __t6 = blend(__s2@0001010000000, __s1@0000100000000, __v1@0000000000001, __t4@0000000001000)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(ss[2], bits["0001010000000"], t6_1);
    info.eval->multiply_plain(ss[1], bits["0000100000000"], t6_2);
    info.eval->multiply_plain(vs[1], bits["0000000000001"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__v0@0000100000000, __v1@0000000001000, __t5@0001010000001)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[0], bits["0000100000000"], t7_1);
    info.eval->multiply_plain(vs[1], bits["0000000001000"], t7_2);
    info.eval->add_many({t7_1, t7_2, ts[5]}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -12, gk, ss[3]); // __s3 = __v2 >> 12
    
    // __t10 = blend(__s1@0100000000000, __s2@0010000000100, __s0@0000000100000, __t8@0000000010010)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(ss[1], bits["0100000000000"], t10_1);
    info.eval->multiply_plain(ss[2], bits["0010000000100"], t10_2);
    info.eval->multiply_plain(ss[0], bits["0000000100000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3, ts[8]}, ts[10]);
    
    
    // __t11 = blend(__s0@0000000010000, __v0@0000000000010, __t9@0110000100100)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(ss[0], bits["0000000010000"], t11_1);
    info.eval->multiply_plain(vs[0], bits["0000000000010"], t11_2);
    info.eval->add_many({t11_1, t11_2, ts[9]}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[3]); // __v3 = __t10 + __t11
    info.eval->rotate_rows(vs[3], -12, gk, ss[4]); // __s4 = __v3 >> 12
    
    // __t14 = blend(__v3@0100000000000, __s3@0001100000000, __s4@0000000101000, __t12@0000000000010)
    ctxt t14_1, t14_2, t14_3;
    info.eval->multiply_plain(vs[3], bits["0100000000000"], t14_1);
    info.eval->multiply_plain(ss[3], bits["0001100000000"], t14_2);
    info.eval->multiply_plain(ss[4], bits["0000000101000"], t14_3);
    info.eval->add_many({t14_1, t14_2, t14_3, ts[12]}, ts[14]);
    
    
    // __t15 = blend(__s4@0100000000000, __v2@0001000001000, __v3@0000000100010, __t13@0000100000000)
    ctxt t15_1, t15_2, t15_3;
    info.eval->multiply_plain(ss[4], bits["0100000000000"], t15_1);
    info.eval->multiply_plain(vs[2], bits["0001000001000"], t15_2);
    info.eval->multiply_plain(vs[3], bits["0000000100010"], t15_3);
    info.eval->add_many({t15_1, t15_2, t15_3, ts[13]}, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[4]); // __v4 = __t14 * __t15
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -3, gk, ss[5]); // __s5 = __v4 >> 3
    
    // __t17 = blend(__v4@0100000000000, __v2@0000000000001)
    ctxt t17_1, t17_2;
    info.eval->multiply_plain(vs[4], bits["0100000000000"], t17_1);
    info.eval->multiply_plain(vs[2], bits["0000000000001"], t17_2);
    info.eval->add(t17_1, t17_2, ts[17]);
    
    
    // __t18 = blend(__s5@0000000000001, __t16@0100000000000)
    ctxt t18_1;
    info.eval->multiply_plain(ss[5], bits["0000000000001"], t18_1);
    info.eval->add(t18_1, ts[16], ts[18]);
    
    info.eval->add(ts[17], ts[18], vs[5]); // __v5 = __t17 + __t18
    info.eval->rotate_rows(vs[5], -7, gk, ss[6]); // __s6 = __v5 >> 7
    
    // __t21 = blend(__s5@0000001100000, __t19@0000000000010)
    ctxt t21_1;
    info.eval->multiply_plain(ss[5], bits["0000001100000"], t21_1);
    info.eval->add(t21_1, ts[19], ts[21]);
    
    
    // __t22 = blend(__v4@0000000100010, __t20@0000001000000)
    ctxt t22_1;
    info.eval->multiply_plain(vs[4], bits["0000000100010"], t22_1);
    info.eval->add(t22_1, ts[20], ts[22]);
    
    info.eval->multiply(ts[21], ts[22], vs[6]); // __v6 = __t21 * __t22
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -7, gk, ss[7]); // __s7 = __v6 >> 7
    info.eval->multiply(vs[6], ss[6], vs[7]); // __v7 = __v6 * __s6
    info.eval->relinearize_inplace(vs[7], rk);
    
    // __t24 = blend(__v5@0100000000000, __s7@0000010000000)
    ctxt t24_1, t24_2;
    info.eval->multiply_plain(vs[5], bits["0100000000000"], t24_1);
    info.eval->multiply_plain(ss[7], bits["0000010000000"], t24_2);
    info.eval->add(t24_1, t24_2, ts[24]);
    
    
    // __t25 = blend(__s7@0100000000000, __t23@0000010000000)
    ctxt t25_1;
    info.eval->multiply_plain(ss[7], bits["0100000000000"], t25_1);
    info.eval->add(t25_1, ts[23], ts[25]);
    
    info.eval->add(ts[24], ts[25], vs[8]); // __v8 = __t24 + __t25
    info.eval->rotate_rows(vs[8], -1, gk, ss[8]); // __s8 = __v8 >> 1
    info.eval->add(vs[8], ts[26], vs[9]); // __v9 = __v8 + __t26
    info.eval->rotate_rows(vs[9], -1, gk, ss[9]); // __s9 = __v9 >> 1
    
    // __t28 = blend(__s8@0000001000000, __t27@0010000000000)
    ctxt t28_1;
    info.eval->multiply_plain(ss[8], bits["0000001000000"], t28_1);
    info.eval->add(t28_1, ts[27], ts[28]);
    
    
    // __t29 = blend(__s9@0010000000000, __v7@0000001000000)
    ctxt t29_1, t29_2;
    info.eval->multiply_plain(ss[9], bits["0010000000000"], t29_1);
    info.eval->multiply_plain(vs[7], bits["0000001000000"], t29_2);
    info.eval->add(t29_1, t29_2, ts[29]);
    
    info.eval->add(ts[28], ts[29], vs[10]); // __v10 = __t28 + __t29
    info.eval->add(vs[10], ts[30], vs[11]); // __v11 = __v10 + __t30
    info.eval->multiply(vs[10], ts[31], vs[12]); // __v12 = __v10 * __t31
    info.eval->relinearize_inplace(vs[12], rk);
    info.eval->rotate_rows(vs[12], -9, gk, ss[10]); // __s10 = __v12 >> 9
    info.eval->multiply(ts[32], ss[10], vs[13]); // __v13 = __t32 * __s10
    info.eval->relinearize_inplace(vs[13], rk);
    info.eval->multiply(vs[13], vs[11], vs[14]); // __v14 = __v13 * __v11
    info.eval->relinearize_inplace(vs[14], rk);
    info.eval->multiply(vs[14], vs[0], vs[15]); // __v15 = __v14 * __v0
    info.eval->relinearize_inplace(vs[15], rk);
    return vs[15];
}
    