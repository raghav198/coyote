
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00000000000000101000", info);
    add_bitstring(bits, "00000100010000000000", info);
    add_bitstring(bits, "00000001101000000000", info);
    add_bitstring(bits, "00000100000000100000", info);
    add_bitstring(bits, "00010000001010000000", info);
    add_bitstring(bits, "00000101001000000000", info);
    add_bitstring(bits, "00000000010010000000", info);
    add_bitstring(bits, "00000000100000000000", info);
    add_bitstring(bits, "00000000001000000010", info);
    add_bitstring(bits, "00000000100010001000", info);
    add_bitstring(bits, "00000000000010001000", info);
    add_bitstring(bits, "00010001000000000000", info);
    add_bitstring(bits, "00000100000001000100", info);
    add_bitstring(bits, "10000000000100000100", info);
    add_bitstring(bits, "00000000010001000100", info);
    add_bitstring(bits, "00000000000101001000", info);
    add_bitstring(bits, "10000001010100001100", info);
    add_bitstring(bits, "00000100100000000000", info);
    add_bitstring(bits, "00010000101011010010", info);
    add_bitstring(bits, "00000000001000100000", info);
    add_bitstring(bits, "00000001010000001000", info);
    add_bitstring(bits, "10010000000000000000", info);
    add_bitstring(bits, "00000000000000000001", info);
    add_bitstring(bits, "00000000000000100010", info);
    add_bitstring(bits, "00000000100001010010", info);
    add_bitstring(bits, "00010000000000000000", info);
    add_bitstring(bits, "00000000000100010000", info);
    add_bitstring(bits, "10000000000000000000", info);
    add_bitstring(bits, "00000000000101100000", info);
    add_bitstring(bits, "00010001000100010000", info);
    add_bitstring(bits, "00000000000000010110", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("000001111111111111111111111111111100011111111111111111111111111110000111111111111111111111111111110001111111111111111111111111111100", info);
    ts[1] = encrypt_input("000001111111111111111111111111111100011111111111111111111111111110000111111111111111111111111111110001111111111111111111111111111100", info);
    ts[2] = encrypt_input("000000000000001111111111111111111111111111101111111111111111111111111111111111111111111111111111111111011111111111111111111111111110", info);
    ts[3] = encrypt_input("000000000000001111111111111111111111111111101111111111111111111111111111111111111111111111111111111111011111111111111111111111111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[10];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -18, gk, ss[0]); // __s0 = __v0 >> 18
    info.eval->rotate_rows(vs[0], -3, gk, ss[1]); // __s1 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -15, gk, ss[2]); // __s2 = __v0 >> 15
    info.eval->rotate_rows(vs[0], -1, gk, ss[3]); // __s3 = __v0 >> 1
    info.eval->rotate_rows(vs[0], -2, gk, ss[4]); // __s4 = __v0 >> 2
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -17, gk, ss[5]); // __s5 = __v1 >> 17
    info.eval->rotate_rows(vs[1], -11, gk, ss[6]); // __s6 = __v1 >> 11
    info.eval->rotate_rows(vs[1], -1, gk, ss[7]); // __s7 = __v1 >> 1
    info.eval->rotate_rows(vs[1], -15, gk, ss[8]); // __s8 = __v1 >> 15
    info.eval->rotate_rows(vs[1], -4, gk, ss[9]); // __s9 = __v1 >> 4
    
    // __t4 = blend(__s0@00010001000000000000, __v0@00000100010000000000, __s3@00000000001000100000, __s1@00000000000010001000, __s4@00000000000000000001)
    ctxt t4_1, t4_2, t4_3, t4_4, t4_5;
    info.eval->multiply_plain(ss[0], bits["00010001000000000000"], t4_1);
    info.eval->multiply_plain(vs[0], bits["00000100010000000000"], t4_2);
    info.eval->multiply_plain(ss[3], bits["00000000001000100000"], t4_3);
    info.eval->multiply_plain(ss[1], bits["00000000000010001000"], t4_4);
    info.eval->multiply_plain(ss[4], bits["00000000000000000001"], t4_5);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4, t4_5}, ts[4]);
    
    
    // __t5 = blend(__s9@00010000000000000000, __s6@00000101001000000000, __s8@00000000010010000000, __s5@00000000000000101000, __v1@00000000000000000001)
    ctxt t5_1, t5_2, t5_3, t5_4, t5_5;
    info.eval->multiply_plain(ss[9], bits["00010000000000000000"], t5_1);
    info.eval->multiply_plain(ss[6], bits["00000101001000000000"], t5_2);
    info.eval->multiply_plain(ss[8], bits["00000000010010000000"], t5_3);
    info.eval->multiply_plain(ss[5], bits["00000000000000101000"], t5_4);
    info.eval->multiply_plain(vs[1], bits["00000000000000000001"], t5_5);
    info.eval->add_many({t5_1, t5_2, t5_3, t5_4, t5_5}, ts[5]);
    
    info.eval->sub(ts[4], ts[5], vs[2]); // __v2 = __t4 - __t5
    
    // __t6 = blend(__s2@10000000000000000000, __v0@00000100000001000100, __s1@00000000100000000000, __s0@00000000000100010000, __s3@00000000000000100010, __s4@00000000000000000001)
    ctxt t6_1, t6_2, t6_3, t6_4, t6_5, t6_6;
    info.eval->multiply_plain(ss[2], bits["10000000000000000000"], t6_1);
    info.eval->multiply_plain(vs[0], bits["00000100000001000100"], t6_2);
    info.eval->multiply_plain(ss[1], bits["00000000100000000000"], t6_3);
    info.eval->multiply_plain(ss[0], bits["00000000000100010000"], t6_4);
    info.eval->multiply_plain(ss[3], bits["00000000000000100010"], t6_5);
    info.eval->multiply_plain(ss[4], bits["00000000000000000001"], t6_6);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4, t6_5, t6_6}, ts[6]);
    
    
    // __t7 = blend(__s9@10000000000000000000, __s6@00000100100000000000, __s5@00000000000101100000, __s7@00000000000000010110, __v1@00000000000000000001)
    ctxt t7_1, t7_2, t7_3, t7_4, t7_5;
    info.eval->multiply_plain(ss[9], bits["10000000000000000000"], t7_1);
    info.eval->multiply_plain(ss[6], bits["00000100100000000000"], t7_2);
    info.eval->multiply_plain(ss[5], bits["00000000000101100000"], t7_3);
    info.eval->multiply_plain(ss[7], bits["00000000000000010110"], t7_4);
    info.eval->multiply_plain(vs[1], bits["00000000000000000001"], t7_5);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4, t7_5}, ts[7]);
    
    info.eval->sub(ts[6], ts[7], vs[3]); // __v3 = __t6 - __t7
    
    // __t8 = blend(__v3@00000100000000100000, __v2@00000000000000000001)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[3], bits["00000100000000100000"], t8_1);
    info.eval->multiply_plain(vs[2], bits["00000000000000000001"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__v2@00000100000000100000, __v3@00000000000000000001)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[2], bits["00000100000000100000"], t9_1);
    info.eval->multiply_plain(vs[3], bits["00000000000000000001"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->multiply(ts[8], ts[9], vs[4]); // __v4 = __t8 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t10 = blend(__s2@10000000000000000000, __s0@00010001000100010000, __s1@00000000100010001000, __v0@00000000010001000100, __s3@00000000001000000010)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5;
    info.eval->multiply_plain(ss[2], bits["10000000000000000000"], t10_1);
    info.eval->multiply_plain(ss[0], bits["00010001000100010000"], t10_2);
    info.eval->multiply_plain(ss[1], bits["00000000100010001000"], t10_3);
    info.eval->multiply_plain(vs[0], bits["00000000010001000100"], t10_4);
    info.eval->multiply_plain(ss[3], bits["00000000001000000010"], t10_5);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5}, ts[10]);
    
    
    // __t11 = blend(__s9@10010000000000000000, __s6@00000001101000000000, __s8@00000000010010000000, __s5@00000000000101001000, __s7@00000000000000010110)
    ctxt t11_1, t11_2, t11_3, t11_4, t11_5;
    info.eval->multiply_plain(ss[9], bits["10010000000000000000"], t11_1);
    info.eval->multiply_plain(ss[6], bits["00000001101000000000"], t11_2);
    info.eval->multiply_plain(ss[8], bits["00000000010010000000"], t11_3);
    info.eval->multiply_plain(ss[5], bits["00000000000101001000"], t11_4);
    info.eval->multiply_plain(ss[7], bits["00000000000000010110"], t11_5);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, t11_5}, ts[11]);
    
    info.eval->sub(ts[10], ts[11], vs[5]); // __v5 = __t10 - __t11
    
    // __t12 = blend(__v5@10000001010100001100, __v2@00010000001010000000, __v3@00000000100001010010)
    ctxt t12_1, t12_2, t12_3;
    info.eval->multiply_plain(vs[5], bits["10000001010100001100"], t12_1);
    info.eval->multiply_plain(vs[2], bits["00010000001010000000"], t12_2);
    info.eval->multiply_plain(vs[3], bits["00000000100001010010"], t12_3);
    info.eval->add_many({t12_1, t12_2, t12_3}, ts[12]);
    
    
    // __t13 = blend(__v3@10000000000100000100, __v5@00010000101011010010, __v2@00000001010000001000)
    ctxt t13_1, t13_2, t13_3;
    info.eval->multiply_plain(vs[3], bits["10000000000100000100"], t13_1);
    info.eval->multiply_plain(vs[5], bits["00010000101011010010"], t13_2);
    info.eval->multiply_plain(vs[2], bits["00000001010000001000"], t13_3);
    info.eval->add_many({t13_1, t13_2, t13_3}, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[6]); // __v6 = __t12 * __t13
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    