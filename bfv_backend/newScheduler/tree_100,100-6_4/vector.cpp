
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000001000010000000000000000000", info);
    add_bitstring(bits, "00000001100010000000000000000000", info);
    add_bitstring(bits, "00000000000011000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000010101100", info);
    add_bitstring(bits, "00000000000100000000000000000000", info);
    add_bitstring(bits, "00101000100010000000000000010000", info);
    add_bitstring(bits, "00000000001000000000000000100000", info);
    add_bitstring(bits, "00000010101000000000000000000000", info);
    add_bitstring(bits, "00000001100000000000000000000000", info);
    add_bitstring(bits, "00000110000000000000110000001100", info);
    add_bitstring(bits, "00000000000001000000000000000000", info);
    add_bitstring(bits, "00000000000000000000000000010000", info);
    add_bitstring(bits, "00000100010000000000000000000000", info);
    add_bitstring(bits, "00000001000000000000000010000000", info);
    add_bitstring(bits, "00000000000010000000000000000000", info);
    add_bitstring(bits, "00000001110000000000000000000000", info);
    add_bitstring(bits, "00000100001000000000000000000000", info);
    add_bitstring(bits, "00000010000100000000000000000000", info);
    add_bitstring(bits, "00101011100000000000110000000000", info);
    add_bitstring(bits, "00000100001010000000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(12);
    ts[0] = encrypt_input("111111111110111111111111111111111111111111111111111011111110111111111111101011110111111111111", info);
    ts[1] = encrypt_input("111111111110111111111111111111110111011011111111101111011111011110011111111111111011111101101", info);
    ts[2] = encrypt_input("0000000000011000000000000000000000", info);
    ts[3] = encrypt_input("0000000000011100000000000000000000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[11];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -5, gk, ss[0]); // __s0 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -31, gk, ss[1]); // __s1 = __v0 >> 31
    info.eval->rotate_rows(vs[0], -25, gk, ss[2]); // __s2 = __v0 >> 25
    
    // __t4 = blend(__s1@00101000100010000000000000010000, __s0@00000110000000000000110000001100, __s2@00000001000000000000000010000000, __v0@00000000001000000000000000100000, __t2@00000000000100000000000000000000)
    ctxt t4_1, t4_2, t4_3, t4_4;
    info.eval->multiply_plain(ss[1], bits["00101000100010000000000000010000"], t4_1);
    info.eval->multiply_plain(ss[0], bits["00000110000000000000110000001100"], t4_2);
    info.eval->multiply_plain(ss[2], bits["00000001000000000000000010000000"], t4_3);
    info.eval->multiply_plain(vs[0], bits["00000000001000000000000000100000"], t4_4);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, ts[2]}, ts[4]);
    
    
    // __t5 = blend(__v0@00101011100000000000110000000000, __s2@00000100001010000000000000000000, __s1@00000000000000000000000010101100, __s0@00000000000000000000000000010000, __t3@00000000000100000000000000000000)
    ctxt t5_1, t5_2, t5_3, t5_4;
    info.eval->multiply_plain(vs[0], bits["00101011100000000000110000000000"], t5_1);
    info.eval->multiply_plain(ss[2], bits["00000100001010000000000000000000"], t5_2);
    info.eval->multiply_plain(ss[1], bits["00000000000000000000000010101100"], t5_3);
    info.eval->multiply_plain(ss[0], bits["00000000000000000000000000010000"], t5_4);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, ts[3]}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[1]); // __v1 = __t4 * __t5
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -4, gk, ss[3]); // __s3 = __v1 >> 4
    info.eval->rotate_rows(vs[1], -17, gk, ss[4]); // __s4 = __v1 >> 17
    info.eval->rotate_rows(vs[1], -12, gk, ss[5]); // __s5 = __v1 >> 12
    info.eval->multiply(vs[1], vs[0], vs[2]); // __v2 = __v1 * __v0
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__s4@00000100010000000000000000000000, __s3@00000010101000000000000000000000, __v1@00000001000010000000000000000000, __v2@00000000000100000000000000000000)
    ctxt t6_1, t6_2, t6_3, t6_4;
    info.eval->multiply_plain(ss[4], bits["00000100010000000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[3], bits["00000010101000000000000000000000"], t6_2);
    info.eval->multiply_plain(vs[1], bits["00000001000010000000000000000000"], t6_3);
    info.eval->multiply_plain(vs[2], bits["00000000000100000000000000000000"], t6_4);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4}, ts[6]);
    
    
    // __t7 = blend(__v1@00000100001000000000000000000000, __s4@00000010000100000000000000000000, __s5@00000001110000000000000000000000, __s3@00000000000010000000000000000000)
    ctxt t7_1, t7_2, t7_3, t7_4;
    info.eval->multiply_plain(vs[1], bits["00000100001000000000000000000000"], t7_1);
    info.eval->multiply_plain(ss[4], bits["00000010000100000000000000000000"], t7_2);
    info.eval->multiply_plain(ss[5], bits["00000001110000000000000000000000"], t7_3);
    info.eval->multiply_plain(ss[3], bits["00000000000010000000000000000000"], t7_4);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -2, gk, ss[6]); // __s6 = __v3 >> 2
    info.eval->rotate_rows(vs[3], -4, gk, ss[7]); // __s7 = __v3 >> 4
    info.eval->rotate_rows(vs[3], -1, gk, ss[8]); // __s8 = __v3 >> 1
    
    // __t8 = blend(__v3@00000001100000000000000000000000, __s8@00000000000011000000000000000000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[3], bits["00000001100000000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[8], bits["00000000000011000000000000000000"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__s6@00000001100010000000000000000000, __s7@00000000000001000000000000000000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(ss[6], bits["00000001100010000000000000000000"], t9_1);
    info.eval->multiply_plain(ss[7], bits["00000000000001000000000000000000"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -5, gk, ss[9]); // __s9 = __v4 >> 5
    
    // __t10 = blend(__s9@00000000000010000000000000000000, __v4@00000000000001000000000000000000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(ss[9], bits["00000000000010000000000000000000"], t10_1);
    info.eval->multiply_plain(vs[4], bits["00000000000001000000000000000000"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    
    // __t11 = blend(__v4@00000000000010000000000000000000, __s9@00000000000001000000000000000000)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(vs[4], bits["00000000000010000000000000000000"], t11_1);
    info.eval->multiply_plain(ss[9], bits["00000000000001000000000000000000"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[5]); // __v5 = __t10 * __t11
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -1, gk, ss[10]); // __s10 = __v5 >> 1
    info.eval->multiply(vs[5], ss[10], vs[6]); // __v6 = __v5 * __s10
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    