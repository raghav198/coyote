
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000000000010000000000000000", info);
    add_bitstring(bits, "00000000000000101000000000000000", info);
    add_bitstring(bits, "00000000000001100000000000000000", info);
    add_bitstring(bits, "00000000000000000100000000000000", info);
    add_bitstring(bits, "01000000010000000000000000000000", info);
    add_bitstring(bits, "00010000000000000000000001010000", info);
    add_bitstring(bits, "00000000000100001000000000011000", info);
    add_bitstring(bits, "00000000000100000000000000000000", info);
    add_bitstring(bits, "00000000010000000010000000000100", info);
    add_bitstring(bits, "00000000000000000000000000000100", info);
    add_bitstring(bits, "00000000010000000000000000000000", info);
    add_bitstring(bits, "01000001000000000000000000000000", info);
    add_bitstring(bits, "00000001000100000000000001000000", info);
    add_bitstring(bits, "00000000000000000000000000011000", info);
    add_bitstring(bits, "00000000000000111000000000000000", info);
    add_bitstring(bits, "00010100000001000000000000000000", info);
    add_bitstring(bits, "00101000100000000000000010010001", info);
    add_bitstring(bits, "00100100000000001000000010000001", info);
    add_bitstring(bits, "00001000110100000000000000000000", info);
    add_bitstring(bits, "00000000000000000110000000000000", info);
    add_bitstring(bits, "00000000000000001000000000000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(10);
    ts[0] = encrypt_input("1111111111111010111101111111110110111101111110111111111011111111111101111111111111111111101111", info);
    ts[1] = encrypt_input("11111101111111101111111011111111111111111111001110111111110111111111111111110111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[6];
    ctxt ss[14];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -29, gk, ss[1]); // __s1 = __v0 >> 29
    info.eval->rotate_rows(vs[0], -25, gk, ss[2]); // __s2 = __v0 >> 25
    info.eval->rotate_rows(vs[0], -20, gk, ss[3]); // __s3 = __v0 >> 20
    
    // __t2 = blend(__s3@01000000010000000000000000000000, __v0@00101000100000000000000010010001, __s2@00010100000001000000000000000000, __s0@00000001000100000000000001000000, __s1@00000000000000101000000000000000)
    ctxt t2_1, t2_2, t2_3, t2_4, t2_5;
    info.eval->multiply_plain(ss[3], bits["01000000010000000000000000000000"], t2_1);
    info.eval->multiply_plain(vs[0], bits["00101000100000000000000010010001"], t2_2);
    info.eval->multiply_plain(ss[2], bits["00010100000001000000000000000000"], t2_3);
    info.eval->multiply_plain(ss[0], bits["00000001000100000000000001000000"], t2_4);
    info.eval->multiply_plain(ss[1], bits["00000000000000101000000000000000"], t2_5);
    info.eval->add_many({t2_1, t2_2, t2_3, t2_4, t2_5}, ts[2]);
    
    
    // __t3 = blend(__v0@01000001000000000000000000000000, __s0@00100100000000001000000010000001, __s1@00010000000000000000000001010000, __s2@00001000110100000000000000000000, __s3@00000000000001100000000000000000)
    ctxt t3_1, t3_2, t3_3, t3_4, t3_5;
    info.eval->multiply_plain(vs[0], bits["01000001000000000000000000000000"], t3_1);
    info.eval->multiply_plain(ss[0], bits["00100100000000001000000010000001"], t3_2);
    info.eval->multiply_plain(ss[1], bits["00010000000000000000000001010000"], t3_3);
    info.eval->multiply_plain(ss[2], bits["00001000110100000000000000000000"], t3_4);
    info.eval->multiply_plain(ss[3], bits["00000000000001100000000000000000"], t3_5);
    info.eval->add_many({t3_1, t3_2, t3_3, t3_4, t3_5}, ts[3]);
    
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -15, gk, ss[4]); // __s4 = __v1 >> 15
    info.eval->rotate_rows(vs[1], -23, gk, ss[5]); // __s5 = __v1 >> 23
    info.eval->rotate_rows(vs[1], -2, gk, ss[6]); // __s6 = __v1 >> 2
    info.eval->rotate_rows(vs[1], -3, gk, ss[7]); // __s7 = __v1 >> 3
    info.eval->rotate_rows(vs[1], -30, gk, ss[8]); // __s8 = __v1 >> 30
    
    // __t4 = blend(__s6@00000000010000000010000000000100, __v1@00000000000100000000000000000000, __s4@00000000000000001000000000000000, __s7@00000000000000000100000000000000, __s5@00000000000000000000000000011000)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5;
    info.eval->multiply_plain(ss[6], bits["00000000010000000010000000000100"], t4_1);
    info.eval->multiply_plain(vs[1], bits["00000000000100000000000000000000"], t4_2);
    info.eval->multiply_plain(ss[4], bits["00000000000000001000000000000000"], t4_3);
    info.eval->multiply_plain(ss[7], bits["00000000000000000100000000000000"], t4_4);
    info.eval->multiply_plain(ss[5], bits["00000000000000000000000000011000"], t4_5);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5}, ts[4]);
    
    
    // __t5 = blend(__v1@00000000010000000000000000000000, __s7@00000000000100001000000000011000, __s4@00000000000000000110000000000000, __s8@00000000000000000000000000000100)
    ctxt t5_1, t5_2, t5_3, t5_4;
    info.eval->multiply_plain(vs[1], bits["00000000010000000000000000000000"], t5_1);
    info.eval->multiply_plain(ss[7], bits["00000000000100001000000000011000"], t5_2);
    info.eval->multiply_plain(ss[4], bits["00000000000000000110000000000000"], t5_3);
    info.eval->multiply_plain(ss[8], bits["00000000000000000000000000000100"], t5_4);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -5, gk, ss[9]); // __s9 = __v2 >> 5
    info.eval->rotate_rows(vs[2], -31, gk, ss[10]); // __s10 = __v2 >> 31
    info.eval->rotate_rows(vs[2], -19, gk, ss[11]); // __s11 = __v2 >> 19
    
    // __t6 = blend(__s9@00000000000000101000000000000000, __s10@00000000000000010000000000000000, __v2@00000000000000000100000000000000)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(ss[9], bits["00000000000000101000000000000000"], t6_1);
    info.eval->multiply_plain(ss[10], bits["00000000000000010000000000000000"], t6_2);
    info.eval->multiply_plain(vs[2], bits["00000000000000000100000000000000"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    
    // __t7 = blend(__s11@00000000000000111000000000000000, __s10@00000000000000000100000000000000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[11], bits["00000000000000111000000000000000"], t7_1);
    info.eval->multiply_plain(ss[10], bits["00000000000000000100000000000000"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -1, gk, ss[12]); // __s12 = __v3 >> 1
    
    // __t8 = blend(__v3@00000000000000010000000000000000, __s12@00000000000000000100000000000000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[3], bits["00000000000000010000000000000000"], t8_1);
    info.eval->multiply_plain(ss[12], bits["00000000000000000100000000000000"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__s12@00000000000000010000000000000000, __v3@00000000000000000100000000000000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(ss[12], bits["00000000000000010000000000000000"], t9_1);
    info.eval->multiply_plain(vs[3], bits["00000000000000000100000000000000"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -30, gk, ss[13]); // __s13 = __v4 >> 30
    info.eval->multiply(ss[13], vs[4], vs[5]); // __v5 = __s13 * __v4
    info.eval->relinearize_inplace(vs[5], rk);
    return vs[5];
}
    