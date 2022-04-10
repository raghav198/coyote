
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "11000010000000000000000000000000", info);
    add_bitstring(bits, "00110000000000000000000000100000", info);
    add_bitstring(bits, "00000000000000000000000000000010", info);
    add_bitstring(bits, "00110000000000000001000000100000", info);
    add_bitstring(bits, "00000000000000001000000000000000", info);
    add_bitstring(bits, "00000000000000000000010000000000", info);
    add_bitstring(bits, "00001000001100001001000000000000", info);
    add_bitstring(bits, "00000000000100000000100000000000", info);
    add_bitstring(bits, "00000001000000001000000000100000", info);
    add_bitstring(bits, "00000001000001000000000000000000", info);
    add_bitstring(bits, "01000010000100000000000000000000", info);
    add_bitstring(bits, "10000001000001000100000000000000", info);
    add_bitstring(bits, "00000000000000000000100000000000", info);
    add_bitstring(bits, "00000000000000000000010000100010", info);
    add_bitstring(bits, "00000000000100001000100000000000", info);
    add_bitstring(bits, "00001000001000000000000000000000", info);
    add_bitstring(bits, "00000000000000000100000000000000", info);
    add_bitstring(bits, "00000001000000000000000000100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(11);
    ts[0] = encrypt_input("1111111111111111111101100111110110111111011111111110111111111111111111111111111101111111", info);
    ts[1] = encrypt_input("11011111111101111111011001011011111111110101101111111111111111111111111111111011111111111", info);
    ts[2] = encrypt_input("000000000000000000001110000000001110", info);
    ts[3] = encrypt_input("0000000000000000000010110000000001110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[12];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -27, gk, ss[1]); // __s1 = __v0 >> 27
    info.eval->rotate_rows(vs[0], -25, gk, ss[2]); // __s2 = __v0 >> 25
    info.eval->rotate_rows(vs[0], -20, gk, ss[3]); // __s3 = __v0 >> 20
    
    // __t4 = blend(__s1@11000010000000000000000000000000, __v0@00110000000000000000000000100000, __s3@00001000001100001001000000000000, __s2@00000001000001000000000000000000, __s0@00000000000000000100000000000000, __t2@00000000000000000000100000000010)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5;
    info.eval->multiply_plain(ss[1], bits["11000010000000000000000000000000"], t4_1);
    info.eval->multiply_plain(vs[0], bits["00110000000000000000000000100000"], t4_2);
    info.eval->multiply_plain(ss[3], bits["00001000001100001001000000000000"], t4_3);
    info.eval->multiply_plain(ss[2], bits["00000001000001000000000000000000"], t4_4);
    info.eval->multiply_plain(ss[0], bits["00000000000000000100000000000000"], t4_5);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5, ts[2]}, ts[4]);
    
    
    // __t5 = blend(__s3@10000001000001000100000000000000, __s2@01000010000100000000000000000000, __s0@00110000000000000001000000100000, __v0@00001000001000000000000000000000, __s1@00000000000000001000000000000000, __t3@00000000000000000000100000000010)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5;
    info.eval->multiply_plain(ss[3], bits["10000001000001000100000000000000"], t5_1);
    info.eval->multiply_plain(ss[2], bits["01000010000100000000000000000000"], t5_2);
    info.eval->multiply_plain(ss[0], bits["00110000000000000001000000100000"], t5_3);
    info.eval->multiply_plain(vs[0], bits["00001000001000000000000000000000"], t5_4);
    info.eval->multiply_plain(ss[1], bits["00000000000000001000000000000000"], t5_5);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5, ts[3]}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[1]); // __v1 = __t4 * __t5
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -7, gk, ss[4]); // __s4 = __v1 >> 7
    info.eval->rotate_rows(vs[1], -10, gk, ss[5]); // __s5 = __v1 >> 10
    info.eval->rotate_rows(vs[1], -15, gk, ss[6]); // __s6 = __v1 >> 15
    info.eval->rotate_rows(vs[1], -18, gk, ss[7]); // __s7 = __v1 >> 18
    
    // __t6 = blend(__s2@00000000000000000000100000000000, __v0@00000000000000000000000000000010)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(ss[2], bits["00000000000000000000100000000000"], t6_1);
    info.eval->multiply_plain(vs[0], bits["00000000000000000000000000000010"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    info.eval->multiply(ts[6], vs[1], vs[2]); // __v2 = __t6 * __v1
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -10, gk, ss[8]); // __s8 = __v2 >> 10
    
    // __t7 = blend(__s4@00000001000000000000000000100000, __s5@00000000000100001000100000000000, __v1@00000000000000000100000000000000, __s7@00000000000000000000010000000000, __s8@00000000000000000000000000000010)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5;
    info.eval->multiply_plain(ss[4], bits["00000001000000000000000000100000"], t7_1);
    info.eval->multiply_plain(ss[5], bits["00000000000100001000100000000000"], t7_2);
    info.eval->multiply_plain(vs[1], bits["00000000000000000100000000000000"], t7_3);
    info.eval->multiply_plain(ss[7], bits["00000000000000000000010000000000"], t7_4);
    info.eval->multiply_plain(ss[8], bits["00000000000000000000000000000010"], t7_5);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5}, ts[7]);
    
    
    // __t8 = blend(__v1@00000001000000001000000000100000, __s4@00000000000100000000100000000000, __s6@00000000000000000100000000000000, __s5@00000000000000000000010000000000, __v2@00000000000000000000000000000010)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5;
    info.eval->multiply_plain(vs[1], bits["00000001000000001000000000100000"], t8_1);
    info.eval->multiply_plain(ss[4], bits["00000000000100000000100000000000"], t8_2);
    info.eval->multiply_plain(ss[6], bits["00000000000000000100000000000000"], t8_3);
    info.eval->multiply_plain(ss[5], bits["00000000000000000000010000000000"], t8_4);
    info.eval->multiply_plain(vs[2], bits["00000000000000000000000000000010"], t8_5);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5}, ts[8]);
    
    info.eval->multiply(ts[7], ts[8], vs[3]); // __v3 = __t7 * __t8
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -10, gk, ss[9]); // __s9 = __v3 >> 10
    
    // __t9 = blend(__s9@00000000000000000100000000000000, __v3@00000000000000000000010000100010)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(ss[9], bits["00000000000000000100000000000000"], t9_1);
    info.eval->multiply_plain(vs[3], bits["00000000000000000000010000100010"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    
    // __t10 = blend(__v3@00000000000000000100000000000000, __s9@00000000000000000000010000100010)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[3], bits["00000000000000000100000000000000"], t10_1);
    info.eval->multiply_plain(ss[9], bits["00000000000000000000010000100010"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    info.eval->multiply(ts[9], ts[10], vs[4]); // __v4 = __t9 * __t10
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -23, gk, ss[10]); // __s10 = __v4 >> 23
    info.eval->multiply(ss[10], vs[4], vs[5]); // __v5 = __s10 * __v4
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -28, gk, ss[11]); // __s11 = __v5 >> 28
    info.eval->multiply(ss[11], vs[5], vs[6]); // __v6 = __s11 * __v5
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    