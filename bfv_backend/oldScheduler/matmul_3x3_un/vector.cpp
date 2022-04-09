
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "01001011100", info);
    add_bitstring(bits, "00000000100", info);
    add_bitstring(bits, "00001100000", info);
    add_bitstring(bits, "00000010000", info);
    add_bitstring(bits, "00100001000", info);
    add_bitstring(bits, "01000100000", info);
    add_bitstring(bits, "00010000000", info);
    add_bitstring(bits, "10100000000", info);
    add_bitstring(bits, "10000000000", info);
    add_bitstring(bits, "00011000000", info);
    add_bitstring(bits, "01000000000", info);
    add_bitstring(bits, "10010001100", info);
    add_bitstring(bits, "11000000000", info);
    add_bitstring(bits, "11100101000", info);
    add_bitstring(bits, "10101000000", info);
    add_bitstring(bits, "01010001000", info);
    add_bitstring(bits, "00001000000", info);
    add_bitstring(bits, "00100000000", info);
    add_bitstring(bits, "11010100000", info);
    add_bitstring(bits, "00000100000", info);
    add_bitstring(bits, "00000001000", info);
    add_bitstring(bits, "00101001000", info);
    add_bitstring(bits, "00001101000", info);
    add_bitstring(bits, "00101000000", info);
    add_bitstring(bits, "11000100000", info);
    add_bitstring(bits, "00010100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(15);
    ts[0] = encrypt_input("11111111111111111111111111111111111111111111111111111111101111111111111111111111111111111111111111101111111111111111101111111111111111111110111111111111111111111111111111111111101000", info);
    ts[1] = encrypt_input("11111111111111111111111111111111111111111111111111111111101111111111111111111111111111111111111111101111111111111111101111111111111111111110111111111111111111111111111111111111101000", info);
    ts[2] = encrypt_input("00111111111111111111101111111111111111101111111111111111111110111111111111111111111111111111111111101011111111111111111111111111111111111111111111111111111111101111111111111111111111", info);
    ts[3] = encrypt_input("00111111111111111111101111111111111111101111111111111111111110111111111111111111111111111111111111101011111111111111111111111111111111111111111111111111111111101111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[13];
    ctxt ss[10];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -4, gk, ss[1]); // __s1 = __v0 >> 4
    info.eval->rotate_rows(vs[0], -6, gk, ss[2]); // __s2 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -10, gk, ss[3]); // __s3 = __v0 >> 10
    info.eval->rotate_rows(vs[0], -8, gk, ss[4]); // __s4 = __v0 >> 8
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[5]); // __s5 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -4, gk, ss[6]); // __s6 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -9, gk, ss[7]); // __s7 = __v1 >> 9
    info.eval->rotate_rows(vs[1], -6, gk, ss[8]); // __s8 = __v1 >> 6
    info.eval->rotate_rows(vs[1], -3, gk, ss[9]); // __s9 = __v1 >> 3
    
    // __t4 = blend(__s4@11000000000, __v0@00100000000, __s3@00010000000, __s0@00001101000)
    ctxt t4_1, t4_2, t4_3, t4_4;
    info.eval->multiply_plain(ss[4], bits["11000000000"], t4_1);
    info.eval->multiply_plain(vs[0], bits["00100000000"], t4_2);
    info.eval->multiply_plain(ss[3], bits["00010000000"], t4_3);
    info.eval->multiply_plain(ss[0], bits["00001101000"], t4_4);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4}, ts[4]);
    
    
    // __t5 = blend(__s9@11000000000, __s7@00101000000, __s8@00010100000, __s5@00000001000)
    ctxt t5_1, t5_2, t5_3, t5_4;
    info.eval->multiply_plain(ss[9], bits["11000000000"], t5_1);
    info.eval->multiply_plain(ss[7], bits["00101000000"], t5_2);
    info.eval->multiply_plain(ss[8], bits["00010100000"], t5_3);
    info.eval->multiply_plain(ss[5], bits["00000001000"], t5_4);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__s3@10000000000, __s2@01010001000, __s0@00100000000, __s4@00001000000, __s1@00000100000)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5;
    info.eval->multiply_plain(ss[3], bits["10000000000"], t6_1);
    info.eval->multiply_plain(ss[2], bits["01010001000"], t6_2);
    info.eval->multiply_plain(ss[0], bits["00100000000"], t6_3);
    info.eval->multiply_plain(ss[4], bits["00001000000"], t6_4);
    info.eval->multiply_plain(ss[1], bits["00000100000"], t6_5);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5}, ts[6]);
    
    
    // __t7 = blend(__s8@10101000000, __s7@01000100000, __s5@00010000000, __s6@00000001000)
    ctxt t7_1, t7_2, t7_3, t7_4;
    info.eval->multiply_plain(ss[8], bits["10101000000"], t7_1);
    info.eval->multiply_plain(ss[7], bits["01000100000"], t7_2);
    info.eval->multiply_plain(ss[5], bits["00010000000"], t7_3);
    info.eval->multiply_plain(ss[6], bits["00000001000"], t7_4);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    
    // __t8 = blend(__s2@10100000000, __s1@01001011100, __s4@00010000000, __v0@00000100000)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(ss[2], bits["10100000000"], t8_1);
    info.eval->multiply_plain(ss[1], bits["01001011100"], t8_2);
    info.eval->multiply_plain(ss[4], bits["00010000000"], t8_3);
    info.eval->multiply_plain(vs[0], bits["00000100000"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__s7@10010001100, __s8@01000000000, __s9@00100000000, __s5@00001100000, __s6@00000010000)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5;
    info.eval->multiply_plain(ss[7], bits["10010001100"], t9_1);
    info.eval->multiply_plain(ss[8], bits["01000000000"], t9_2);
    info.eval->multiply_plain(ss[9], bits["00100000000"], t9_3);
    info.eval->multiply_plain(ss[5], bits["00001100000"], t9_4);
    info.eval->multiply_plain(ss[6], bits["00000010000"], t9_5);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t10 = blend(__v2@11010100000, __v4@00100001000, __v3@00001000000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[2], bits["11010100000"], t10_1);
    info.eval->multiply_plain(vs[4], bits["00100001000"], t10_2);
    info.eval->multiply_plain(vs[3], bits["00001000000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__v3@11100101000, __v4@00011000000)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(vs[3], bits["11100101000"], t11_1);
    info.eval->multiply_plain(vs[4], bits["00011000000"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[5]); // __v5 = __t10 + __t11
    
    // __t12 = blend(__v4@11000100000, __v2@00101001000, __v3@00010000000)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(vs[4], bits["11000100000"], t12_1);
    info.eval->multiply_plain(vs[2], bits["00101001000"], t12_2);
    info.eval->multiply_plain(vs[3], bits["00010000000"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    info.eval->add(ts[12], vs[5], vs[6]); // __v6 = __t12 + __v5
    info.eval->multiply(ss[3], ss[7], vs[7]); // __v7 = __s3 * __s7
    info.eval->relinearize_inplace(vs[7], rk);
    
    // __t13 = blend(__s2@00000010000, __s0@00000000100)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(ss[2], bits["00000010000"], t13_1);
    info.eval->multiply_plain(ss[0], bits["00000000100"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->multiply(ts[13], ss[5], vs[8]); // __v8 = __t13 * __s5
    info.eval->relinearize_inplace(vs[8], rk);
    
    // __t14 = blend(__v7@00000010000, __v4@00000000100)
    ctxt t14_1, t14_2;
    info.eval->multiply_plain(vs[7], bits["00000010000"], t14_1);
    info.eval->multiply_plain(vs[4], bits["00000000100"], t14_2);
    info.eval->add(t14_1, t14_2, ts[14]);
    
    info.eval->add(ts[14], vs[8], vs[9]); // __v9 = __t14 + __v8
    info.eval->add(vs[4], vs[9], vs[10]); // __v10 = __v4 + __v9
    info.eval->multiply(vs[0], ss[6], vs[11]); // __v11 = __v0 * __s6
    info.eval->relinearize_inplace(vs[11], rk);
    info.eval->add(vs[11], vs[9], vs[12]); // __v12 = __v11 + __v9
    return vs[12];
}
    