
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000100000000000000000000000000000000", info);
    add_bitstring(bits, "00010000000000000000000000000000000000", info);
    add_bitstring(bits, "00000000010000000000000000000000000000", info);
    add_bitstring(bits, "10000100000000000000000000000000000000", info);
    add_bitstring(bits, "11011110010000000000000000000000000000", info);
    add_bitstring(bits, "01000100000000000000000000000000000000", info);
    add_bitstring(bits, "00100000000000000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000000000000000001", info);
    add_bitstring(bits, "00001010010000000000000000000000000000", info);
    add_bitstring(bits, "00001000000000000000000000000000000000", info);
    add_bitstring(bits, "00000010000000000000000000000000000000", info);
    add_bitstring(bits, "10000000000000000000000000000000000000", info);
    add_bitstring(bits, "11001010000000000000000000000000000000", info);
    add_bitstring(bits, "01000010010000000000000000000000000000", info);
    add_bitstring(bits, "11001000000000000000000000000000000000", info);
    add_bitstring(bits, "00000100010000000000000000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(15);
    ts[0] = encrypt_input("00110110000011111011011011111000000111101111100000000000111100001111011011", info);
    ts[1] = encrypt_input("00111110000011111011011011111000000111111111100000000000111110001111011111", info);
    ts[2] = encrypt_input("1101011010011110110100110101111100000000011011000011011000000011010001111000011010", info);
    ts[3] = encrypt_input("1101011111011111111110111101111100000000011011000011011000000011011001111000011111", info);
    ts[4] = encrypt_input("00000110100000000000000001101100000000000000011110", info);
    ts[5] = encrypt_input("00000110110000000000000001111100000000000000011111", info);
    ts[6] = encrypt_input("001101000000011010011111011111001111101101100001101100110111111011110111110111100000011111", info);
    ts[7] = encrypt_input("001111100000011110011111011111001111101111100001111100111111111011111111110111110000011111", info);
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
    info.eval->rotate_rows(vs[0], -31, gk, ss[0]); // __s0 = __v0 >> 31
    info.eval->rotate_rows(vs[0], -21, gk, ss[1]); // __s1 = __v0 >> 21
    info.eval->rotate_rows(vs[0], -11, gk, ss[2]); // __s2 = __v0 >> 11
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -31, gk, ss[3]); // __s3 = __v1 >> 31
    info.eval->rotate_rows(vs[1], -21, gk, ss[4]); // __s4 = __v1 >> 21
    info.eval->rotate_rows(vs[1], -11, gk, ss[5]); // __s5 = __v1 >> 11
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -21, gk, ss[6]); // __s6 = __v2 >> 21
    info.eval->add(vs[1], vs[0], vs[3]); // __v3 = __v1 + __v0
    info.eval->add(vs[3], vs[2], vs[4]); // __v4 = __v3 + __v2
    info.eval->multiply(ts[6], ts[7], vs[5]); // __v5 = __t6 * __t7
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -31, gk, ss[7]); // __s7 = __v5 >> 31
    info.eval->rotate_rows(vs[5], -21, gk, ss[8]); // __s8 = __v5 >> 21
    info.eval->rotate_rows(vs[5], -11, gk, ss[9]); // __s9 = __v5 >> 11
    
    // __t8 = blend(__v5@00100000000000000000000000000000000000, __v4@00000000000000000000000000000000000001)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[5], bits["00100000000000000000000000000000000000"], t8_1);
    info.eval->multiply_plain(vs[4], bits["00000000000000000000000000000000000001"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__v0@00100000000000000000000000000000000000, __v5@00000000000000000000000000000000000001)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[0], bits["00100000000000000000000000000000000000"], t9_1);
    info.eval->multiply_plain(vs[5], bits["00000000000000000000000000000000000001"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[6]); // __v6 = __t8 + __t9
    
    // __t10 = blend(__v1@11001010000000000000000000000000000000, __v6@00100000000000000000000000000000000000, __s5@00010000000000000000000000000000000000, __v2@00000100000000000000000000000000000000, __v5@00000000010000000000000000000000000000)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5;
    info.eval->multiply_plain(vs[1], bits["11001010000000000000000000000000000000"], t10_1);
    info.eval->multiply_plain(vs[6], bits["00100000000000000000000000000000000000"], t10_2);
    info.eval->multiply_plain(ss[5], bits["00010000000000000000000000000000000000"], t10_3);
    info.eval->multiply_plain(vs[2], bits["00000100000000000000000000000000000000"], t10_4);
    info.eval->multiply_plain(vs[5], bits["00000000010000000000000000000000000000"], t10_5);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5}, ts[10]);
    
    
    // __t11 = blend(__s4@10000100000000000000000000000000000000, __s8@01000010010000000000000000000000000000, __s1@00100000000000000000000000000000000000, __s0@00010000000000000000000000000000000000, __s6@00001000000000000000000000000000000000)
    ctxt t11_1, t11_2, t11_3, t11_4, t11_5;
    info.eval->multiply_plain(ss[4], bits["10000100000000000000000000000000000000"], t11_1);
    info.eval->multiply_plain(ss[8], bits["01000010010000000000000000000000000000"], t11_2);
    info.eval->multiply_plain(ss[1], bits["00100000000000000000000000000000000000"], t11_3);
    info.eval->multiply_plain(ss[0], bits["00010000000000000000000000000000000000"], t11_4);
    info.eval->multiply_plain(ss[6], bits["00001000000000000000000000000000000000"], t11_5);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, t11_5}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[7]); // __v7 = __t10 + __t11
    
    // __t12 = blend(__s9@11001000000000000000000000000000000000, __v1@00010000000000000000000000000000000000, __s2@00000100010000000000000000000000000000, __s5@00000010000000000000000000000000000000)
    ctxt t12_1, t12_2, t12_3, t12_4;
    info.eval->multiply_plain(ss[9], bits["11001000000000000000000000000000000000"], t12_1);
    info.eval->multiply_plain(vs[1], bits["00010000000000000000000000000000000000"], t12_2);
    info.eval->multiply_plain(ss[2], bits["00000100010000000000000000000000000000"], t12_3);
    info.eval->multiply_plain(ss[5], bits["00000010000000000000000000000000000000"], t12_4);
    info.eval->add_many({t12_1, t12_2, t12_3, t12_4}, ts[12]);
    
    info.eval->add(vs[7], ts[12], vs[8]); // __v8 = __v7 + __t12
    
    // __t13 = blend(__v8@11011110010000000000000000000000000000, __v7@00100000000000000000000000000000000000)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[8], bits["11011110010000000000000000000000000000"], t13_1);
    info.eval->multiply_plain(vs[7], bits["00100000000000000000000000000000000000"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    
    // __t14 = blend(__s3@10000000000000000000000000000000000000, __s0@01000100000000000000000000000000000000, __s9@00100000000000000000000000000000000000, __s1@00010000000000000000000000000000000000, __s7@00001010010000000000000000000000000000)
    ctxt t14_1, t14_2, t14_3, t14_4, t14_5;
    info.eval->multiply_plain(ss[3], bits["10000000000000000000000000000000000000"], t14_1);
    info.eval->multiply_plain(ss[0], bits["01000100000000000000000000000000000000"], t14_2);
    info.eval->multiply_plain(ss[9], bits["00100000000000000000000000000000000000"], t14_3);
    info.eval->multiply_plain(ss[1], bits["00010000000000000000000000000000000000"], t14_4);
    info.eval->multiply_plain(ss[7], bits["00001010010000000000000000000000000000"], t14_5);
    info.eval->add_many({t14_1, t14_2, t14_3, t14_4, t14_5}, ts[14]);
    
    info.eval->add(ts[13], ts[14], vs[9]); // __v9 = __t13 + __t14
    return vs[9];
}
    