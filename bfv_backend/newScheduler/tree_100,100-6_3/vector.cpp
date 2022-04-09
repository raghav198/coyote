
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000000000000000000100000", info);
    add_bitstring(bits, "00001000001000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000000100", info);
    add_bitstring(bits, "00000000000000010000010000010", info);
    add_bitstring(bits, "00000001001000000000000000000", info);
    add_bitstring(bits, "00000000000000000100001000000", info);
    add_bitstring(bits, "10000000000100000000000010000", info);
    add_bitstring(bits, "00010000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000100000000", info);
    add_bitstring(bits, "00000000001100000000000000000", info);
    add_bitstring(bits, "00000000000000000000010000000", info);
    add_bitstring(bits, "00000000001000000000000000000", info);
    add_bitstring(bits, "00000001000000000100000010000", info);
    add_bitstring(bits, "00000000000000000000000000010", info);
    add_bitstring(bits, "00001000000000000000000000000", info);
    add_bitstring(bits, "00000000000000010000000000000", info);
    add_bitstring(bits, "00000000010000000000000000100", info);
    add_bitstring(bits, "00001000000000000000000000100", info);
    add_bitstring(bits, "00010000010000000000000000000", info);
    add_bitstring(bits, "00000000100000000000000000000", info);
    add_bitstring(bits, "00000000100000010000000000000", info);
    add_bitstring(bits, "00000000000000000000010000010", info);
    add_bitstring(bits, "00000000010000000000000000000", info);
    add_bitstring(bits, "10000000000000000000011100010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("1111111111111111111101111111111011111111101111111101111101111111111111111111101111111", info);
    ts[1] = encrypt_input("11111111111111111110111111111111101111111011101111011111111111111111111111111111111111", info);
    ts[2] = encrypt_input("000000001110000001110000000000100100", info);
    ts[3] = encrypt_input("00000000110000000111000000000011100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[8];
    ctxt ss[14];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -6, gk, ss[0]); // __s0 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -5, gk, ss[1]); // __s1 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -25, gk, ss[2]); // __s2 = __v0 >> 25
    info.eval->rotate_rows(vs[0], -3, gk, ss[3]); // __s3 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -2, gk, ss[4]); // __s4 = __v0 >> 2
    
    // __t4 = blend(__s2@10000000000100000000000010000, __v0@00000001001000000000000000000, __s3@00000000000000000100001000000, __s1@00000000000000000000010000000, __s0@00000000000000000000000100000, __s4@00000000000000000000000000010, __t2@00000000100000010000000000100)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5, t4_6;
    info.eval->multiply_plain(ss[2], bits["10000000000100000000000010000"], t4_1);
    info.eval->multiply_plain(vs[0], bits["00000001001000000000000000000"], t4_2);
    info.eval->multiply_plain(ss[3], bits["00000000000000000100001000000"], t4_3);
    info.eval->multiply_plain(ss[1], bits["00000000000000000000010000000"], t4_4);
    info.eval->multiply_plain(ss[0], bits["00000000000000000000000100000"], t4_5);
    info.eval->multiply_plain(ss[4], bits["00000000000000000000000000010"], t4_6);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, t4_6, ts[2]}, ts[4]);
    
    
    // __t5 = blend(__v0@10000000000000000000011100010, __s0@00000001000000000100000010000, __s1@00000000001100000000000000000, __t3@00000000100000010000000000100)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(vs[0], bits["10000000000000000000011100010"], t5_1);
    info.eval->multiply_plain(ss[0], bits["00000001000000000100000010000"], t5_2);
    info.eval->multiply_plain(ss[1], bits["00000000001100000000000000000"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3, ts[3]}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[1]); // __v1 = __t4 * __t5
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -4, gk, ss[5]); // __s5 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -2, gk, ss[6]); // __s6 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -23, gk, ss[7]); // __s7 = __v1 >> 23
    
    // __t6 = blend(__v0@00000000100000000000000000000, __s4@00000000000000010000000000000, __s0@00000000000000000000000000100)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(vs[0], bits["00000000100000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[4], bits["00000000000000010000000000000"], t6_2);
    info.eval->multiply_plain(ss[0], bits["00000000000000000000000000100"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    
    // __t7 = blend(__v1@00000000100000010000000000000, __s4@00000000000000000000000000100)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[1], bits["00000000100000010000000000000"], t7_1);
    info.eval->multiply_plain(ss[4], bits["00000000000000000000000000100"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[2]); // __v2 = __t6 * __t7
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -23, gk, ss[8]); // __s8 = __v2 >> 23
    
    // __t8 = blend(__s0@00000000100000000000000000000, __s3@00000000000000010000000000000, __v0@00000000000000000000000000100)
    ctxt t8_1, t8_2, t8_3;
    info.eval->multiply_plain(ss[0], bits["00000000100000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[3], bits["00000000000000010000000000000"], t8_2);
    info.eval->multiply_plain(vs[0], bits["00000000000000000000000000100"], t8_3);
    info.eval->add_many({t8_1, t8_2, t8_3}, ts[8]);
    
    
    // __t9 = blend(__s1@00000000100000000000000000000, __s0@00000000000000010000000000000, __v1@00000000000000000000000000100)
    ctxt t9_1, t9_2, t9_3;
    info.eval->multiply_plain(ss[1], bits["00000000100000000000000000000"], t9_1);
    info.eval->multiply_plain(ss[0], bits["00000000000000010000000000000"], t9_2);
    info.eval->multiply_plain(vs[1], bits["00000000000000000000000000100"], t9_3);
    info.eval->add_many({t9_1, t9_2, t9_3}, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[3]); // __v3 = __t8 * __t9
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -23, gk, ss[9]); // __s9 = __v3 >> 23
    
    // __t10 = blend(__s5@00001000000000000000000000100, __v2@00000000100000010000000000000, __s9@00000000010000000000000000000, __s8@00000000000000000000100000000, __v1@00000000000000000000010000010)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5;
    info.eval->multiply_plain(ss[5], bits["00001000000000000000000000100"], t10_1);
    info.eval->multiply_plain(vs[2], bits["00000000100000010000000000000"], t10_2);
    info.eval->multiply_plain(ss[9], bits["00000000010000000000000000000"], t10_3);
    info.eval->multiply_plain(ss[8], bits["00000000000000000000100000000"], t10_4);
    info.eval->multiply_plain(vs[1], bits["00000000000000000000010000010"], t10_5);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5}, ts[10]);
    
    
    // __t11 = blend(__s7@00001000000000000000000000000, __v3@00000000100000000000000000000, __s6@00000000010000000000000000100, __s5@00000000000000010000010000010, __s9@00000000000000000000100000000)
    ctxt t11_1, t11_2, t11_3, t11_4, t11_5;
    info.eval->multiply_plain(ss[7], bits["00001000000000000000000000000"], t11_1);
    info.eval->multiply_plain(vs[3], bits["00000000100000000000000000000"], t11_2);
    info.eval->multiply_plain(ss[6], bits["00000000010000000000000000100"], t11_3);
    info.eval->multiply_plain(ss[5], bits["00000000000000010000010000010"], t11_4);
    info.eval->multiply_plain(ss[9], bits["00000000000000000000100000000"], t11_5);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, t11_5}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[4]); // __v4 = __t10 * __t11
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -24, gk, ss[10]); // __s10 = __v4 >> 24
    info.eval->rotate_rows(vs[4], -12, gk, ss[11]); // __s11 = __v4 >> 12
    
    // __t12 = blend(__s11@00010000010000000000000000000, __v4@00001000000000000000000000000, __s10@00000000001000000000000000000)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(ss[11], bits["00010000010000000000000000000"], t12_1);
    info.eval->multiply_plain(vs[4], bits["00001000000000000000000000000"], t12_2);
    info.eval->multiply_plain(ss[10], bits["00000000001000000000000000000"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    
    // __t13 = blend(__s10@00010000000000000000000000000, __s11@00001000001000000000000000000, __v4@00000000010000000000000000000)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(ss[10], bits["00010000000000000000000000000"], t13_1);
    info.eval->multiply_plain(ss[11], bits["00001000001000000000000000000"], t13_2);
    info.eval->multiply_plain(vs[4], bits["00000000010000000000000000000"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[5]); // __v5 = __t12 * __t13
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -28, gk, ss[12]); // __s12 = __v5 >> 28
    info.eval->multiply(vs[5], ss[12], vs[6]); // __v6 = __v5 * __s12
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -23, gk, ss[13]); // __s13 = __v6 >> 23
    info.eval->multiply(vs[6], ss[13], vs[7]); // __v7 = __v6 * __s13
    info.eval->relinearize_inplace(vs[7], rk);
    return vs[7];
}
    