
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000010001000010011000000000", info);
    add_bitstring(bits, "01000000000000010000000000010000", info);
    add_bitstring(bits, "00000000000000011000000000100000", info);
    add_bitstring(bits, "00001000001000001000000000000000", info);
    add_bitstring(bits, "00000000000000001001100001000000", info);
    add_bitstring(bits, "00000000000000000100000000000000", info);
    add_bitstring(bits, "00000000000010000000000000000000", info);
    add_bitstring(bits, "00000000010000000000000000000000", info);
    add_bitstring(bits, "00000000000000000011110000000000", info);
    add_bitstring(bits, "00000000000100000000000000000000", info);
    add_bitstring(bits, "00000000000000110000000000100000", info);
    add_bitstring(bits, "00001000000000000000000000000000", info);
    add_bitstring(bits, "00000000000001000000001000000000", info);
    add_bitstring(bits, "00000000010001100000001001000000", info);
    add_bitstring(bits, "00000010000000000000000000000000", info);
    add_bitstring(bits, "00001000000000000100000000000000", info);
    add_bitstring(bits, "00000000001000000000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(16);
    ts[0] = encrypt_input("01100000111000000111011101001101110111000011000111", info);
    ts[1] = encrypt_input("011000001111110000010101110111011111101110000111000111", info);
    ts[2] = encrypt_input("01100000000111111111111110111000001111110111111011001010", info);
    ts[3] = encrypt_input("01110000000111111111101101011100000110111011100010100110", info);
    ts[4] = encrypt_input("11100011111000000001110111011100001110011100000", info);
    ts[5] = encrypt_input("111000111111000000001110101101100001110011100000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[9];
    ctxt ss[15];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -9, gk, ss[0]); // __s0 = __v0 >> 9
    info.eval->rotate_rows(vs[0], -27, gk, ss[1]); // __s1 = __v0 >> 27
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -9, gk, ss[2]); // __s2 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -27, gk, ss[3]); // __s3 = __v1 >> 27
    
    // __t6 = blend(__v0@01000000000000010000000000010000, __v1@00000000000001000000001000000000, __t4@10001100000000101010000100100000)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[0], bits["01000000000000010000000000010000"], t6_1);
    info.eval->multiply_plain(vs[1], bits["00000000000001000000001000000000"], t6_2);
    info.eval->add_many({t6_1, t6_2, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__v1@01000000000000010000000000010000, __v0@00000000000001000000001000000000, __t5@10001100000000101010000100100000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[1], bits["01000000000000010000000000010000"], t7_1);
    info.eval->multiply_plain(vs[0], bits["00000000000001000000001000000000"], t7_2);
    info.eval->add_many({t7_1, t7_2, ts[5]}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -9, gk, ss[4]); // __s4 = __v2 >> 9
    info.eval->rotate_rows(vs[2], -27, gk, ss[5]); // __s5 = __v2 >> 27
    
    // __t8 = blend(__s5@00000000010001000010011000000000, __s4@00000000001000000000000000000000, __s1@00000000000000110000000000100000, __s3@00000000000000001001100001000000)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(ss[5], bits["00000000010001000010011000000000"], t8_1);
    info.eval->multiply_plain(ss[4], bits["00000000001000000000000000000000"], t8_2);
    info.eval->multiply_plain(ss[1], bits["00000000000000110000000000100000"], t8_3);
    info.eval->multiply_plain(ss[3], bits["00000000000000001001100001000000"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__s4@00000000010001100000001001000000, __s5@00000000001000000000000000000000, __s0@00000000000000011000000000100000, __s2@00000000000000000011110000000000)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[4], bits["00000000010001100000001001000000"], t9_1);
    info.eval->multiply_plain(ss[5], bits["00000000001000000000000000000000"], t9_2);
    info.eval->multiply_plain(ss[0], bits["00000000000000011000000000100000"], t9_3);
    info.eval->multiply_plain(ss[2], bits["00000000000000000011110000000000"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -27, gk, ss[6]); // __s6 = __v3 >> 27
    info.eval->rotate_rows(vs[3], -23, gk, ss[7]); // __s7 = __v3 >> 23
    
    // __t10 = blend(__s6@00001000001000001000000000000000, __s5@00000000000000000100000000000000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(ss[6], bits["00001000001000001000000000000000"], t10_1);
    info.eval->multiply_plain(ss[5], bits["00000000000000000100000000000000"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    info.eval->multiply(ts[10], ss[7], vs[4]); // __v4 = __t10 * __s7
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -27, gk, ss[8]); // __s8 = __v4 >> 27
    
    // __t11 = blend(__s7@00000000010000000000000000000000, __v4@00000000001000000000000000000000, __s6@00000000000100000000000000000000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(ss[7], bits["00000000010000000000000000000000"], t11_1);
    info.eval->multiply_plain(vs[4], bits["00000000001000000000000000000000"], t11_2);
    info.eval->multiply_plain(ss[6], bits["00000000000100000000000000000000"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    
    // __t12 = blend(__s6@00000000010000000000000000000000, __v3@00000000001000000000000000000000, __s7@00000000000100000000000000000000)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(ss[6], bits["00000000010000000000000000000000"], t12_1);
    info.eval->multiply_plain(vs[3], bits["00000000001000000000000000000000"], t12_2);
    info.eval->multiply_plain(ss[7], bits["00000000000100000000000000000000"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    info.eval->multiply(ts[11], ts[12], vs[5]); // __v5 = __t11 * __t12
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -27, gk, ss[9]); // __s9 = __v5 >> 27
    info.eval->rotate_rows(vs[5], -2, gk, ss[10]); // __s10 = __v5 >> 2
    
    // __t13 = blend(__s9@00001000000000000000000000000000, __s8@00000000000100000000000000000000, __s6@00000000000000000100000000000000)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(ss[9], bits["00001000000000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[8], bits["00000000000100000000000000000000"], t13_2);
    info.eval->multiply_plain(ss[6], bits["00000000000000000100000000000000"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    
    // __t14 = blend(__v4@00001000000000000100000000000000, __v5@00000000000100000000000000000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[4], bits["00001000000000000100000000000000"], t14_1);
    info.eval->multiply_plain(vs[5], bits["00000000000100000000000000000000"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    info.eval->multiply(ts[13], ts[14], vs[6]); // __v6 = __t13 * __t14
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -2, gk, ss[11]); // __s11 = __v6 >> 2
    info.eval->rotate_rows(vs[6], -27, gk, ss[12]); // __s12 = __v6 >> 27
    
    // __t15 = blend(__s11@00000010000000000000000000000000, __s10@00000000000010000000000000000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(ss[11], bits["00000010000000000000000000000000"], t15_1);
    info.eval->multiply_plain(ss[10], bits["00000000000010000000000000000000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->multiply(ss[12], ts[15], vs[7]); // __v7 = __s12 * __t15
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -1, gk, ss[13]); // __s13 = __v7 >> 1
    info.eval->rotate_rows(vs[7], -27, gk, ss[14]); // __s14 = __v7 >> 27
    info.eval->multiply(ss[14], ss[13], vs[8]); // __v8 = __s14 * __s13
    info.eval->relinearize_inplace(vs[8], rk);
    return vs[8];
}
    