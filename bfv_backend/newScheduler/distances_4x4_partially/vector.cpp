
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0001000100000010001000", info);
    add_bitstring(bits, "1000100000010001000000", info);
    add_bitstring(bits, "0000010001000000100000", info);
    add_bitstring(bits, "0000000000000001001011", info);
    add_bitstring(bits, "0000001000100000010001", info);
    add_bitstring(bits, "1001011000000000000000", info);
    add_bitstring(bits, "0000000000000000000010", info);
    add_bitstring(bits, "0000000000000000010000", info);
    add_bitstring(bits, "0000000000010010110000", info);
    add_bitstring(bits, "0001010100110001100001", info);
    add_bitstring(bits, "0001010100110001110001", info);
    add_bitstring(bits, "0000100101100000000000", info);
    add_bitstring(bits, "0000001000100000000001", info);
    add_bitstring(bits, "1000101001000010001000", info);
    add_bitstring(bits, "0000010001000000100010", info);
    add_bitstring(bits, "0000000000010010100000", info);
    add_bitstring(bits, "0000000000000001001001", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(12);
    ts[0] = encrypt_input("11111111111111111111111111111000111111111111111111111111111110000001111111111111111111111111111000011111111111111111111111111111000000", info);
    ts[1] = encrypt_input("11111111111111111111111111111000111111111111111111111111111110000001111111111111111111111111111000011111111111111111111111111111000000", info);
    ts[2] = encrypt_input("00000000000000011111111111111111111111111111001111111111111111111111111111101111111111111111111111111111011111111111111111111111111111", info);
    ts[3] = encrypt_input("00000000000000011111111111111111111111111111001111111111111111111111111111101111111111111111111111111111011111111111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[6];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -3, gk, ss[0]); // __s0 = __v0 >> 3
    info.eval->rotate_rows(vs[0], -5, gk, ss[1]); // __s1 = __v0 >> 5
    info.eval->rotate_rows(vs[0], -6, gk, ss[2]); // __s2 = __v0 >> 6
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -18, gk, ss[3]); // __s3 = __v1 >> 18
    info.eval->rotate_rows(vs[1], -11, gk, ss[4]); // __s4 = __v1 >> 11
    info.eval->rotate_rows(vs[1], -7, gk, ss[5]); // __s5 = __v1 >> 7
    
    // __t4 = blend(__s2@0000000000000000010000, __s1@0000000000000000000010)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(ss[2], bits["0000000000000000010000"], t4_1);
    info.eval->multiply_plain(ss[1], bits["0000000000000000000010"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__s3@0000000000000000010000, __v1@0000000000000000000010)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(ss[3], bits["0000000000000000010000"], t5_1);
    info.eval->multiply_plain(vs[1], bits["0000000000000000000010"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->sub(ts[4], ts[5], vs[2]); // __v2 = __t4 - __t5
    
    // __t6 = blend(__v0@1000100000010001000000, __s0@0001000100000010001000, __s1@0000010001000000100010, __s2@0000001000100000000001)
    ctxt t6_1, t6_2, t6_3, t6_4;
    info.eval->multiply_plain(vs[0], bits["1000100000010001000000"], t6_1);
    info.eval->multiply_plain(ss[0], bits["0001000100000010001000"], t6_2);
    info.eval->multiply_plain(ss[1], bits["0000010001000000100010"], t6_3);
    info.eval->multiply_plain(ss[2], bits["0000001000100000000001"], t6_4);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4}, ts[6]);
    
    
    // __t7 = blend(__s5@1001011000000000000000, __s4@0000100101100000000000, __s3@0000000000010010100000, __v1@0000000000000001001011)
    ctxt t7_1, t7_2, t7_3, t7_4;
    info.eval->multiply_plain(ss[5], bits["1001011000000000000000"], t7_1);
    info.eval->multiply_plain(ss[4], bits["0000100101100000000000"], t7_2);
    info.eval->multiply_plain(ss[3], bits["0000000000010010100000"], t7_3);
    info.eval->multiply_plain(vs[1], bits["0000000000000001001011"], t7_4);
    info.eval->add_many({t7_1, t7_2, t7_3, t7_4}, ts[7]);
    
    info.eval->sub(ts[6], ts[7], vs[3]); // __v3 = __t6 - __t7
    info.eval->multiply(vs[2], vs[3], vs[4]); // __v4 = __v2 * __v3
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t8 = blend(__v0@1000100000010001000000, __s0@0001000100000010001000, __s1@0000010001000000100000, __s2@0000001000100000010001)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(vs[0], bits["1000100000010001000000"], t8_1);
    info.eval->multiply_plain(ss[0], bits["0001000100000010001000"], t8_2);
    info.eval->multiply_plain(ss[1], bits["0000010001000000100000"], t8_3);
    info.eval->multiply_plain(ss[2], bits["0000001000100000010001"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__s5@1001011000000000000000, __s4@0000100101100000000000, __s3@0000000000010010110000, __v1@0000000000000001001001)
    ctxt t9_1, t9_2, t9_3, t9_4;
    info.eval->multiply_plain(ss[5], bits["1001011000000000000000"], t9_1);
    info.eval->multiply_plain(ss[4], bits["0000100101100000000000"], t9_2);
    info.eval->multiply_plain(ss[3], bits["0000000000010010110000"], t9_3);
    info.eval->multiply_plain(vs[1], bits["0000000000000001001001"], t9_4);
    info.eval->add_many({t9_1, t9_2, t9_3, t9_4}, ts[9]);
    
    info.eval->sub(ts[8], ts[9], vs[5]); // __v5 = __t8 - __t9
    
    // __t10 = blend(__v3@1000101001000010001000, __v5@0001010100110001110001)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(vs[3], bits["1000101001000010001000"], t10_1);
    info.eval->multiply_plain(vs[5], bits["0001010100110001110001"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    
    // __t11 = blend(__v5@1000101001000010001000, __v3@0001010100110001100001, __v2@0000000000000000010000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[5], bits["1000101001000010001000"], t11_1);
    info.eval->multiply_plain(vs[3], bits["0001010100110001100001"], t11_2);
    info.eval->multiply_plain(vs[2], bits["0000000000000000010000"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[6]); // __v6 = __t10 * __t11
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    