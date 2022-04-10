
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0100000000000100000000001000", info);
    add_bitstring(bits, "0001100000000001100001000000", info);
    add_bitstring(bits, "1000000000001000000000010000", info);
    add_bitstring(bits, "1000000000001000001000010000", info);
    add_bitstring(bits, "0001100000000001000000100000", info);
    add_bitstring(bits, "0000000000000000000100000000", info);
    add_bitstring(bits, "0001000000000001000000000010", info);
    add_bitstring(bits, "0000000000000000001100000000", info);
    add_bitstring(bits, "1100000000001100001100011011", info);
    add_bitstring(bits, "1100100000001100101001000011", info);
    add_bitstring(bits, "1100100000001100000000000011", info);
    add_bitstring(bits, "0000100000000000000000100001", info);
    add_bitstring(bits, "0000000000000000100001100000", info);
    add_bitstring(bits, "0001000000000001000000011000", info);
    add_bitstring(bits, "0000000000000000001000000000", info);
    add_bitstring(bits, "0000000000000000101001000000", info);
    add_bitstring(bits, "0000000000000000100000100000", info);
    add_bitstring(bits, "0001000000000001000001000010", info);
    add_bitstring(bits, "0100000000000100000100001000", info);
    add_bitstring(bits, "0001000000000001000100011000", info);
    add_bitstring(bits, "0000000000000000000001000000", info);
    add_bitstring(bits, "0000100000000000100000000001", info);
    add_bitstring(bits, "1100000000001100000000011011", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(12);
    ts[0] = encrypt_input("0001111111111111111111111111000000000001111111111111111111111110000001111111111111111111111111000011111111111111111111111110", info);
    ts[1] = encrypt_input("0001111111111111111111111111000000000001111111111111111111111110000001111111111111111111111111000011111111111111111111111110", info);
    ts[2] = encrypt_input("1111111111111111111111111111111111111111111111111111111111111111111111111101111111111111111111111111000000001111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111001111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110011111111111111111111111101111111111111111111111111011111111111111111111111111111111111111111111111111", info);
    ts[3] = encrypt_input("1111111111111111111111111111111111111111111111111111111111111111111111111101111111111111111111111111000000001111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111001111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110011111111111111111111111101111111111111111111111111011111111111111111111111111111111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[4];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -25, gk, ss[0]); // __s0 = __v0 >> 25
    info.eval->rotate_rows(vs[0], -26, gk, ss[1]); // __s1 = __v0 >> 26
    info.eval->rotate_rows(vs[0], -1, gk, ss[2]); // __s2 = __v0 >> 1
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[3]); // __s3 = __v1 >> 1
    
    // __t4 = blend(__s0@1000000000001000000000010000, __s1@0100000000000100000000001000, __v0@0001000000000001000000000010, __s2@0000100000000000000000100001)
    ctxt t4_1, t4_2, t4_3, t4_4;
    info.eval->multiply_plain(ss[0], bits["1000000000001000000000010000"], t4_1);
    info.eval->multiply_plain(ss[1], bits["0100000000000100000000001000"], t4_2);
    info.eval->multiply_plain(vs[0], bits["0001000000000001000000000010"], t4_3);
    info.eval->multiply_plain(ss[2], bits["0000100000000000000000100001"], t4_4);
    info.eval->add_many({t4_1, t4_2, t4_3, t4_4}, ts[4]);
    
    
    // __t5 = blend(__v1@1100000000001100000000011011, __s3@0001100000000001000000100000)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(vs[1], bits["1100000000001100000000011011"], t5_1);
    info.eval->multiply_plain(ss[3], bits["0001100000000001000000100000"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->sub(ts[4], ts[5], vs[2]); // __v2 = __t4 - __t5
    
    // __t6 = blend(__s2@0000000000000000100000100000, __s0@0000000000000000001000000000, __s1@0000000000000000000100000000, __v0@0000000000000000000001000000)
    ctxt t6_1, t6_2, t6_3, t6_4;
    info.eval->multiply_plain(ss[2], bits["0000000000000000100000100000"], t6_1);
    info.eval->multiply_plain(ss[0], bits["0000000000000000001000000000"], t6_2);
    info.eval->multiply_plain(ss[1], bits["0000000000000000000100000000"], t6_3);
    info.eval->multiply_plain(vs[0], bits["0000000000000000000001000000"], t6_4);
    info.eval->add_many({t6_1, t6_2, t6_3, t6_4}, ts[6]);
    
    
    // __t7 = blend(__s3@0000000000000000100001100000, __v1@0000000000000000001100000000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[3], bits["0000000000000000100001100000"], t7_1);
    info.eval->multiply_plain(vs[1], bits["0000000000000000001100000000"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->sub(ts[6], ts[7], vs[3]); // __v3 = __t6 - __t7
    info.eval->multiply(vs[3], vs[2], vs[4]); // __v4 = __v3 * __v2
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t8 = blend(__s0@1000000000001000001000010000, __s1@0100000000000100000100001000, __v0@0001000000000001000001000010, __s2@0000100000000000100000000001)
    ctxt t8_1, t8_2, t8_3, t8_4;
    info.eval->multiply_plain(ss[0], bits["1000000000001000001000010000"], t8_1);
    info.eval->multiply_plain(ss[1], bits["0100000000000100000100001000"], t8_2);
    info.eval->multiply_plain(vs[0], bits["0001000000000001000001000010"], t8_3);
    info.eval->multiply_plain(ss[2], bits["0000100000000000100000000001"], t8_4);
    info.eval->add_many({t8_1, t8_2, t8_3, t8_4}, ts[8]);
    
    
    // __t9 = blend(__v1@1100000000001100001100011011, __s3@0001100000000001100001000000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(vs[1], bits["1100000000001100001100011011"], t9_1);
    info.eval->multiply_plain(ss[3], bits["0001100000000001100001000000"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->sub(ts[8], ts[9], vs[5]); // __v5 = __t8 - __t9
    
    // __t10 = blend(__v5@1100100000001100101001000011, __v2@0001000000000001000000011000, __v3@0000000000000000000100000000)
    ctxt t10_1, t10_2, t10_3;
    info.eval->multiply_plain(vs[5], bits["1100100000001100101001000011"], t10_1);
    info.eval->multiply_plain(vs[2], bits["0001000000000001000000011000"], t10_2);
    info.eval->multiply_plain(vs[3], bits["0000000000000000000100000000"], t10_3);
    info.eval->add_many({t10_1, t10_2, t10_3}, ts[10]);
    
    
    // __t11 = blend(__v2@1100100000001100000000000011, __v5@0001000000000001000100011000, __v3@0000000000000000101001000000)
    ctxt t11_1, t11_2, t11_3;
    info.eval->multiply_plain(vs[2], bits["1100100000001100000000000011"], t11_1);
    info.eval->multiply_plain(vs[5], bits["0001000000000001000100011000"], t11_2);
    info.eval->multiply_plain(vs[3], bits["0000000000000000101001000000"], t11_3);
    info.eval->add_many({t11_1, t11_2, t11_3}, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[6]); // __v6 = __t10 * __t11
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    