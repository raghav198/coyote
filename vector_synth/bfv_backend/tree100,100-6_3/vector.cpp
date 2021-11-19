
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000000000000001000000000000000000", info);
    add_bitstring(bits, "01000000000000000000000000000000000000", info);
    add_bitstring(bits, "00000000000001000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000001000100010000000000", info);
    add_bitstring(bits, "00000000000000000101000000000000000000", info);
    add_bitstring(bits, "00000000000100000100000000000000000000", info);
    add_bitstring(bits, "00000000000000000100000000000000000000", info);
    add_bitstring(bits, "00000001000000000000000000000000000000", info);
    add_bitstring(bits, "01000001010001000000000000000101000001", info);
    add_bitstring(bits, "00000011001000000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000010000000000000000", info);
    add_bitstring(bits, "00000000000100000000000000000000000000", info);
    add_bitstring(bits, "01000001010001000001000001010101000001", info);
    add_bitstring(bits, "00000000000000000000000100000000000000", info);
    add_bitstring(bits, "00000000000000000000010001000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(16);
    ts[0] = encrypt_input("0000001111110011111100000111110001111100011100000000000", info);
    ts[1] = encrypt_input("00000011110100111111000001111110011111100011100000000000", info);
    ts[2] = encrypt_input("0000001011110011011000001110011001111110000000000000", info);
    ts[3] = encrypt_input("000000111111001111110000011100111001111110000000000000", info);
    ts[4] = encrypt_input("111111000000111110001011110000011000001110111111111111110000111110", info);
    ts[5] = encrypt_input("1111110000001111110011111000001110000011001101111111111110000111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[10];
    ctxt ss[10];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -1, gk, ss[0]); // __s0 = __v0 >> 1
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -1, gk, ss[1]); // __s1 = __v1 >> 1
    
    // __t6 = blend(__v1@00000011001000000000000000000000000000, __v0@00000000000100000100000000000000000000, __t4@11000000110011000001000001011111000011)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(vs[1], bits["00000011001000000000000000000000000000"], t6_1);
    info.eval->multiply_plain(vs[0], bits["00000000000100000100000000000000000000"], t6_2);
    info.eval->add_many({t6_1, t6_2, ts[4]}, ts[6]);
    
    
    // __t7 = blend(__v0@00000011001000000000000000000000000000, __v1@00000000000100000100000000000000000000, __t5@11000000110011000001000001011111000011)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[0], bits["00000011001000000000000000000000000000"], t7_1);
    info.eval->multiply_plain(vs[1], bits["00000000000100000100000000000000000000"], t7_2);
    info.eval->add_many({t7_1, t7_2, ts[5]}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -1, gk, ss[2]); // __s2 = __v2 >> 1
    
    // __t8 = blend(__v2@01000001010001000001000001010101000001, __s2@00000000000100000000000000000000000000, __v0@00000000000000000000010000000000000000, __v1@00000000000000000000000100000000000000)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(vs[2], bits["01000001010001000001000001010101000001"], t8_1);
    info.eval->multiply_plain(ss[2], bits["00000000000100000000000000000000000000"], t8_2);
    info.eval->multiply_plain(vs[0], bits["00000000000000000000010000000000000000"], t8_3);
    info.eval->multiply_plain(vs[1], bits["00000000000000000000000100000000000000"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__s2@01000001010001000000000000000101000001, __v2@00000000000100000000000000000000000000, __s0@00000000000000000001000100010000000000, __s1@00000000000000000000010001000000000000)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[2], bits["01000001010001000000000000000101000001"], t9_1);
    info.eval->multiply_plain(vs[2], bits["00000000000100000000000000000000000000"], t9_2);
    info.eval->multiply_plain(ss[0], bits["00000000000000000001000100010000000000"], t9_3);
    info.eval->multiply_plain(ss[1], bits["00000000000000000000010001000000000000"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -30, gk, ss[3]); // __s3 = __v3 >> 30
    info.eval->rotate_rows(vs[3], -28, gk, ss[4]); // __s4 = __v3 >> 28
    info.eval->multiply(vs[3], ss[3], vs[4]); // __v4 = __v3 * __s3
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -28, gk, ss[5]); // __s5 = __v4 >> 28
    
    // __t10 = blend(__v4@01000000000000000000000000000000000000, __s3@00000000000001000000000000000000000000, __v2@00000000000000000100000000000000000000, __v3@00000000000000000001000000000000000000)
    ctxt t10_1, t10_2, t10_3, t10_4;
    info.eval->multiply_plain(vs[4], bits["01000000000000000000000000000000000000"], t10_1);
    info.eval->multiply_plain(ss[3], bits["00000000000001000000000000000000000000"], t10_2);
    info.eval->multiply_plain(vs[2], bits["00000000000000000100000000000000000000"], t10_3);
    info.eval->multiply_plain(vs[3], bits["00000000000000000001000000000000000000"], t10_4);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4}, ts[10]);
    
    
    // __t11 = blend(__s4@01000000000000000000000000000000000000, __v3@00000000000001000000000000000000000000, __s3@00000000000000000101000000000000000000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(ss[4], bits["01000000000000000000000000000000000000"], t11_1);
    info.eval->multiply_plain(vs[3], bits["00000000000001000000000000000000000000"], t11_2);
    info.eval->multiply_plain(ss[3], bits["00000000000000000101000000000000000000"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[5]); // __v5 = __t10 * __t11
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -6, gk, ss[6]); // __s6 = __v5 >> 6
    info.eval->rotate_rows(vs[5], -28, gk, ss[7]); // __s7 = __v5 >> 28
    
    // __t12 = blend(__v3@00000001000000000000000000000000000000, __v5@00000000000001000000000000000000000000)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(vs[3], bits["00000001000000000000000000000000000000"], t12_1);
    info.eval->multiply_plain(vs[5], bits["00000000000001000000000000000000000000"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    
    // __t13 = blend(__s7@00000001000000000000000000000000000000, __s5@00000000000001000000000000000000000000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(ss[7], bits["00000001000000000000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[5], bits["00000000000001000000000000000000000000"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[6]); // __v6 = __t12 * __t13
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -6, gk, ss[8]); // __s8 = __v6 >> 6
    
    // __t14 = blend(__v6@00000001000000000000000000000000000000, __v5@00000000000000000001000000000000000000)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[6], bits["00000001000000000000000000000000000000"], t14_1);
    info.eval->multiply_plain(vs[5], bits["00000000000000000001000000000000000000"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    
    // __t15 = blend(__s6@00000001000000000000000000000000000000, __s5@00000000000000000001000000000000000000)
    ctxt t15_1, t15_2;
    info.eval->multiply_plain(ss[6], bits["00000001000000000000000000000000000000"], t15_1);
    info.eval->multiply_plain(ss[5], bits["00000000000000000001000000000000000000"], t15_2);
    info.eval->add(t15_1, t15_2, ts[15]);
    
    info.eval->multiply(ts[14], ts[15], vs[7]); // __v7 = __t14 * __t15
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->rotate_rows(vs[7], -12, gk, ss[9]); // __s9 = __v7 >> 12
    info.eval->multiply(vs[7], ss[8], vs[8]); // __v8 = __v7 * __s8
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->multiply(ss[9], vs[8], vs[9]); // __v9 = __s9 * __v8
    info.eval->relinearize_inplace(vs[9], rk);
    return vs[9];
}
    