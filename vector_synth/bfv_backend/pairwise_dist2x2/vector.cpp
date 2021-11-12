
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00100001", info);
    add_bitstring(bits, "00010000", info);
    add_bitstring(bits, "00100000", info);
    add_bitstring(bits, "11101010", info);
    add_bitstring(bits, "00010101", info);
    add_bitstring(bits, "01000000", info);
    add_bitstring(bits, "00000001", info);
    add_bitstring(bits, "00010010", info);
    add_bitstring(bits, "00000100", info);
    add_bitstring(bits, "10000000", info);
    add_bitstring(bits, "00001000", info);
    add_bitstring(bits, "00000110", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("001100000111", info);
    ts[1] = encrypt_input("001100000111", info);
    ts[2] = encrypt_input("000001101110", info);
    ts[3] = encrypt_input("000001101110", info);
    ts[4] = encrypt_input("111000110000", info);
    ts[5] = encrypt_input("111000110000", info);
    ts[6] = encrypt_input("000011100110", info);
    ts[7] = encrypt_input("000011100110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[11];
    ctxt ss[13];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -6, gk, ss[0]); // __s0 = __v0 >> 6
    info.eval->rotate_rows(vs[0], -2, gk, ss[1]); // __s1 = __v0 >> 2
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -7, gk, ss[2]); // __s2 = __v1 >> 7
    info.eval->rotate_rows(vs[1], -5, gk, ss[3]); // __s3 = __v1 >> 5
    vs[2] = ts[4]; // vector load instr
    info.eval->rotate_rows(vs[2], -1, gk, ss[4]); // __s4 = __v2 >> 1
    info.eval->rotate_rows(vs[2], -3, gk, ss[5]); // __s5 = __v2 >> 3
    info.eval->rotate_rows(vs[2], -6, gk, ss[6]); // __s6 = __v2 >> 6
    vs[3] = ts[6]; // vector load instr
    info.eval->rotate_rows(vs[3], -7, gk, ss[7]); // __s7 = __v3 >> 7
    info.eval->rotate_rows(vs[3], -6, gk, ss[8]); // __s8 = __v3 >> 6
    
    // __t8 = blend(__s0@10000000, __s1@01000000, __v0@00100001, __s3@00010000, __s2@00001000, __v1@00000110)
    ctxt t8_1, t8_2, t8_3, t8_4, t8_5, t8_6;
    info.eval->multiply_plain(ss[0], bits["10000000"], t8_1);
    info.eval->multiply_plain(ss[1], bits["01000000"], t8_2);
    info.eval->multiply_plain(vs[0], bits["00100001"], t8_3);
    info.eval->multiply_plain(ss[3], bits["00010000"], t8_4);
    info.eval->multiply_plain(ss[2], bits["00001000"], t8_5);
    info.eval->multiply_plain(vs[1], bits["00000110"], t8_6);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4, t8_5, t8_6}, ts[8]);
    
    
    // __t9 = blend(__v2@10000000, __s4@01000000, __s6@00100000, __s7@00010010, __v3@00001000, __s8@00000100, __s5@00000001)
    ctxt t9_1, t9_2, t9_3, t9_4, t9_5, t9_6, t9_7;
    info.eval->multiply_plain(vs[2], bits["10000000"], t9_1);
    info.eval->multiply_plain(ss[4], bits["01000000"], t9_2);
    info.eval->multiply_plain(ss[6], bits["00100000"], t9_3);
    info.eval->multiply_plain(ss[7], bits["00010010"], t9_4);
    info.eval->multiply_plain(vs[3], bits["00001000"], t9_5);
    info.eval->multiply_plain(ss[8], bits["00000100"], t9_6);
    info.eval->multiply_plain(ss[5], bits["00000001"], t9_7);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4, t9_5, t9_6, t9_7}, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    
    // __t10 = blend(__s0@10000000, __s1@01000000, __v0@00100001, __s3@00010000, __s2@00001000, __v1@00000110)
    ctxt t10_1, t10_2, t10_3, t10_4, t10_5, t10_6;
    info.eval->multiply_plain(ss[0], bits["10000000"], t10_1);
    info.eval->multiply_plain(ss[1], bits["01000000"], t10_2);
    info.eval->multiply_plain(vs[0], bits["00100001"], t10_3);
    info.eval->multiply_plain(ss[3], bits["00010000"], t10_4);
    info.eval->multiply_plain(ss[2], bits["00001000"], t10_5);
    info.eval->multiply_plain(vs[1], bits["00000110"], t10_6);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4, t10_5, t10_6}, ts[10]);
    
    
    // __t11 = blend(__v2@10000000, __s4@01000000, __s6@00100000, __s7@00010010, __v3@00001000, __s8@00000100, __s5@00000001)
    ctxt t11_1, t11_2, t11_3, t11_4, t11_5, t11_6, t11_7;
    info.eval->multiply_plain(vs[2], bits["10000000"], t11_1);
    info.eval->multiply_plain(ss[4], bits["01000000"], t11_2);
    info.eval->multiply_plain(ss[6], bits["00100000"], t11_3);
    info.eval->multiply_plain(ss[7], bits["00010010"], t11_4);
    info.eval->multiply_plain(vs[3], bits["00001000"], t11_5);
    info.eval->multiply_plain(ss[8], bits["00000100"], t11_6);
    info.eval->multiply_plain(ss[5], bits["00000001"], t11_7);
    info.eval->add_many({t11_1, t11_2, t11_3, t11_4, t11_5, t11_6, t11_7}, ts[11]);
    
    info.eval->add(ts[10], ts[11], vs[5]); // __v5 = __t10 + __t11
    
    // __t12 = blend(__v5@11101010, __v4@00010101)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(vs[5], bits["11101010"], t12_1);
    info.eval->multiply_plain(vs[4], bits["00010101"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    
    // __t13 = blend(__v4@11101010, __v5@00010101)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[4], bits["11101010"], t13_1);
    info.eval->multiply_plain(vs[5], bits["00010101"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->multiply(ts[12], ts[13], vs[6]); // __v6 = __t12 * __t13
    info.eval->relinearize_inplace(vs[6], rk);
    info.eval->rotate_rows(vs[6], -6, gk, ss[9]); // __s9 = __v6 >> 6
    info.eval->rotate_rows(vs[6], -4, gk, ss[10]); // __s10 = __v6 >> 4
    info.eval->rotate_rows(vs[6], -5, gk, ss[11]); // __s11 = __v6 >> 5
    info.eval->rotate_rows(vs[6], -1, gk, ss[12]); // __s12 = __v6 >> 1
    info.eval->sub(vs[6], ss[10], vs[7]); // __v7 = __v6 - __s10
    info.eval->sub(vs[6], ss[9], vs[8]); // __v8 = __v6 - __s9
    info.eval->sub(vs[6], ss[12], vs[9]); // __v9 = __v6 - __s12
    info.eval->sub(vs[6], ss[11], vs[10]); // __v10 = __v6 - __s11
    return vs[10];
}
    