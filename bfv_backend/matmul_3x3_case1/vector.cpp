
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000000000000100000000", info);
    add_bitstring(bits, "00000000001000000100000000", info);
    add_bitstring(bits, "00000000000000000000100000", info);
    add_bitstring(bits, "11010000000000000100000000", info);
    add_bitstring(bits, "00000000010000000000000000", info);
    add_bitstring(bits, "00000010000000000000000000", info);
    add_bitstring(bits, "00000000000000000010000000", info);
    add_bitstring(bits, "00000000000000011000000000", info);
    add_bitstring(bits, "00100000010000000000000000", info);
    add_bitstring(bits, "00000000110000000011100000", info);
    add_bitstring(bits, "00000000001000010000100000", info);
    add_bitstring(bits, "00000000100011000000000001", info);
    add_bitstring(bits, "00000000000000000001100000", info);
    add_bitstring(bits, "00000000110001000000000000", info);
    add_bitstring(bits, "10000000000000000000000000", info);
    add_bitstring(bits, "00000000000000000000110001", info);
    add_bitstring(bits, "00000000001000000101000000", info);
    add_bitstring(bits, "00000000100000000100000000", info);
    add_bitstring(bits, "00000000001000100101000000", info);
    add_bitstring(bits, "00000000001000000000000000", info);
    add_bitstring(bits, "00000000000000001000010100", info);
    add_bitstring(bits, "00000000000100000010000000", info);
    add_bitstring(bits, "00000001000000000000000000", info);
    add_bitstring(bits, "01010010000000000000000000", info);
    add_bitstring(bits, "00000001000100000000000000", info);
    add_bitstring(bits, "00000000110000000000100000", info);
    add_bitstring(bits, "00100000000000000000000000", info);
    add_bitstring(bits, "00000000000100000000100000", info);
    add_bitstring(bits, "00000000100000000101000000", info);
    add_bitstring(bits, "00000000000100000000000000", info);
    add_bitstring(bits, "00000000000000100000000000", info);
    add_bitstring(bits, "00000001011000000000100000", info);
    add_bitstring(bits, "00000000000000000001000000", info);
    add_bitstring(bits, "00000000000010000000000100", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(12);
    ts[0] = encrypt_input("0000111111111111111111111111111111111111111111111111111111111111111111111111111111111111100111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111101111111111111111111111111111111111111111100", info);
    ts[1] = encrypt_input("0000111111111111111111111111111111111111111111111111111111111111111111111111111111111111100111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111111111111111111101111111111111111111111111111111111111111100", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[6];
    ctxt ss[15];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -7, gk, ss[0]); // __s0 = __v0 >> 7
    info.eval->rotate_rows(vs[0], -22, gk, ss[1]); // __s1 = __v0 >> 22
    info.eval->rotate_rows(vs[0], -6, gk, ss[2]); // __s2 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -2, gk, ss[3]); // __s3 = __v0 >> 2
    info.eval->rotate_rows(vs[0], -1, gk, ss[4]); // __s4 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -20, gk, ss[5]); // __s5 = __v0 >> 20
    info.eval->rotate_rows(vs[0], -25, gk, ss[6]); // __s6 = __v0 >> 25
    info.eval->rotate_rows(vs[0], -21, gk, ss[7]); // __s7 = __v0 >> 21
    info.eval->rotate_rows(vs[0], -12, gk, ss[8]); // __s8 = __v0 >> 12
    info.eval->rotate_rows(vs[0], -10, gk, ss[9]); // __s9 = __v0 >> 10
    
    // __t2 = blend(__s1@11010000000000000100000000, __s8@00100000010000000000000000, __s5@00000010000000000000000000, __s3@00000001000000000000000000, __s4@00000000100011000000000001, __s6@00000000001000010000100000, __s2@00000000000100000010000000, __s0@00000000000000100000000000, __v0@00000000000000001000010100, __s7@00000000000000000001000000)
    ctxt t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7, t2_8, t2_9, t2_10;
    info.eval->multiply_plain(ss[1], bits["11010000000000000100000000"], t2_1);
    info.eval->multiply_plain(ss[8], bits["00100000010000000000000000"], t2_2);
    info.eval->multiply_plain(ss[5], bits["00000010000000000000000000"], t2_3);
    info.eval->multiply_plain(ss[3], bits["00000001000000000000000000"], t2_4);
    info.eval->multiply_plain(ss[4], bits["00000000100011000000000001"], t2_5);
    info.eval->multiply_plain(ss[6], bits["00000000001000010000100000"], t2_6);
    info.eval->multiply_plain(ss[2], bits["00000000000100000010000000"], t2_7);
    info.eval->multiply_plain(ss[0], bits["00000000000000100000000000"], t2_8);
    info.eval->multiply_plain(vs[0], bits["00000000000000001000010100"], t2_9);
    info.eval->multiply_plain(ss[7], bits["00000000000000000001000000"], t2_10);
    info.eval->add_many({t2_1, t2_2, t2_3, t2_4, t2_5, t2_6, t2_7, t2_8, t2_9, t2_10}, ts[2]);
    
    
    // __t3 = blend(__s5@10000000000000000000000000, __s8@01010010000000000000000000, __s9@00100000000000000000000000, __s4@00000001000100000000000000, __s7@00000000110001000000000000, __v0@00000000001000100101000000, __s2@00000000000010000000000100, __s1@00000000000000011000000000, __s6@00000000000000000010000000, __s0@00000000000000000000110001)
    ctxt t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7, t3_8, t3_9, t3_10;
    info.eval->multiply_plain(ss[5], bits["10000000000000000000000000"], t3_1);
    info.eval->multiply_plain(ss[8], bits["01010010000000000000000000"], t3_2);
    info.eval->multiply_plain(ss[9], bits["00100000000000000000000000"], t3_3);
    info.eval->multiply_plain(ss[4], bits["00000001000100000000000000"], t3_4);
    info.eval->multiply_plain(ss[7], bits["00000000110001000000000000"], t3_5);
    info.eval->multiply_plain(vs[0], bits["00000000001000100101000000"], t3_6);
    info.eval->multiply_plain(ss[2], bits["00000000000010000000000100"], t3_7);
    info.eval->multiply_plain(ss[1], bits["00000000000000011000000000"], t3_8);
    info.eval->multiply_plain(ss[6], bits["00000000000000000010000000"], t3_9);
    info.eval->multiply_plain(ss[0], bits["00000000000000000000110001"], t3_10);
    info.eval->add_many({t3_1, t3_2, t3_3, t3_4, t3_5, t3_6, t3_7, t3_8, t3_9, t3_10}, ts[3]);
    
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -8, gk, ss[10]); // __s10 = __v1 >> 8
    info.eval->rotate_rows(vs[1], -1, gk, ss[11]); // __s11 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -22, gk, ss[12]); // __s12 = __v1 >> 22
    info.eval->rotate_rows(vs[1], -18, gk, ss[13]); // __s13 = __v1 >> 18
    
    // __t4 = blend(__s9@00000001000000000000000000, __s2@00000000001000000100000000, __s0@00000000000100000000000000, __s1@00000000000000000000100000)
    ctxt t4_1, t4_2, t4_3, t4_4;
    info.eval->multiply_plain(ss[9], bits["00000001000000000000000000"], t4_1);
    info.eval->multiply_plain(ss[2], bits["00000000001000000100000000"], t4_2);
    info.eval->multiply_plain(ss[0], bits["00000000000100000000000000"], t4_3);
    info.eval->multiply_plain(ss[1], bits["00000000000000000000100000"], t4_4);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4}, ts[4]);
    
    
    // __t5 = blend(__s5@00000001000000000000000000, __s7@00000000001000000000000000, __s4@00000000000100000000000000, __s3@00000000000000000100000000, __v0@00000000000000000000100000)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5;
    info.eval->multiply_plain(ss[5], bits["00000001000000000000000000"], t5_1);
    info.eval->multiply_plain(ss[7], bits["00000000001000000000000000"], t5_2);
    info.eval->multiply_plain(ss[4], bits["00000000000100000000000000"], t5_3);
    info.eval->multiply_plain(ss[3], bits["00000000000000000100000000"], t5_4);
    info.eval->multiply_plain(vs[0], bits["00000000000000000000100000"], t5_5);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    
    // __t6 = blend(__v1@00000001000000000000000000, __s10@00000000110000000011100000, __v2@00000000001000000100000000)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(vs[1], bits["00000001000000000000000000"], t6_1);
    info.eval->multiply_plain(ss[10], bits["00000000110000000011100000"], t6_2);
    info.eval->multiply_plain(vs[2], bits["00000000001000000100000000"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    
    // __t7 = blend(__v2@00000001000000000000000000, __v1@00000000110000000000100000, __s12@00000000001000000101000000, __s11@00000000000000000010000000)
    ctxt t7_1, t7_2, t7_3, t7_4;
    info.eval->multiply_plain(vs[2], bits["00000001000000000000000000"], t7_1);
    info.eval->multiply_plain(vs[1], bits["00000000110000000000100000"], t7_2);
    info.eval->multiply_plain(ss[12], bits["00000000001000000101000000"], t7_3);
    info.eval->multiply_plain(ss[11], bits["00000000000000000010000000"], t7_4);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4}, ts[7]);
    
    info.eval->add(ts[6], ts[7], vs[3]); // __v3 = __t6 + __t7
    info.eval->rotate_rows(vs[3], -2, gk, ss[14]); // __s14 = __v3 >> 2
    
    // __t8 = blend(__s11@00000001000000000000000000, __s12@00000000010000000000000000, __s10@00000000001000000000000000, __v2@00000000000100000000100000)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(ss[11], bits["00000001000000000000000000"], t8_1);
    info.eval->multiply_plain(ss[12], bits["00000000010000000000000000"], t8_2);
    info.eval->multiply_plain(ss[10], bits["00000000001000000000000000"], t8_3);
    info.eval->multiply_plain(vs[2], bits["00000000000100000000100000"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__v3@00000001011000000000100000, __s10@00000000000100000000000000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[3], bits["00000001011000000000100000"], t9_1);
    info.eval->multiply_plain(ss[10], bits["00000000000100000000000000"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    
    // __t10 = blend(__s13@00000000100000000100000000, __s12@00000000000100000000000000, __s11@00000000000000000001100000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(ss[13], bits["00000000100000000100000000"], t10_1);
    info.eval->multiply_plain(ss[12], bits["00000000000100000000000000"], t10_2);
    info.eval->multiply_plain(ss[11], bits["00000000000000000001100000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__v3@00000000100000000101000000, __v4@00000000000100000000000000, __s14@00000000000000000000100000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[3], bits["00000000100000000101000000"], t11_1);
    info.eval->multiply_plain(vs[4], bits["00000000000100000000000000"], t11_2);
    info.eval->multiply_plain(ss[14], bits["00000000000000000000100000"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[5]); // __v5 = __t10 + __t11
    return vs[5];
}
    