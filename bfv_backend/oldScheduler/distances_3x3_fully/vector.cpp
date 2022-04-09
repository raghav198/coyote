
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000000000100001", info);
    add_bitstring(bits, "0000000010100001", info);
    add_bitstring(bits, "0000101000010000", info);
    add_bitstring(bits, "1010001000010001", info);
    add_bitstring(bits, "1010000000000000", info);
    add_bitstring(bits, "0000100000100000", info);
    add_bitstring(bits, "1010000100000000", info);
    add_bitstring(bits, "0000000010000000", info);
    add_bitstring(bits, "0000000100000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(9);
    ts[0] = encrypt_input("0000000011111111111111111111111100111111111111111111111111100001111111111111111111111111", info);
    ts[1] = encrypt_input("0000000011111111111111111111111100111111111111111111111111100001111111111111111111111111", info);
    ts[2] = encrypt_input("1111111111111111111111110011111111111111111111111110111111111111111111111111101111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111011111111111111111111111110001111111111111111111111110", info);
    ts[3] = encrypt_input("1111111111111111111111110011111111111111111111111110111111111111111111111111101111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111011111111111111111111111110001111111111111111111111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[2];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -8, gk, ss[0]); // __s0 = __v0 >> 8
    info.eval->rotate_rows(vs[0], -12, gk, ss[1]); // __s1 = __v0 >> 12
    vs[1] = ts[2]; // vector load instr
    
    // __t4 = blend(__s0@0000000100000000, __v0@0000000010000000)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(ss[0], bits["0000000100000000"], t4_1);
    info.eval->multiply_plain(vs[0], bits["0000000010000000"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    info.eval->sub(ts[4], vs[1], vs[2]); // __v2 = __t4 - __v1
    
    // __t5 = blend(__s0@1010000100000000, __s1@0000101000010000, __v0@0000000010100001)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(ss[0], bits["1010000100000000"], t5_1);
    info.eval->multiply_plain(ss[1], bits["0000101000010000"], t5_2);
    info.eval->multiply_plain(vs[0], bits["0000000010100001"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);
    
    info.eval->sub(ts[5], vs[1], vs[3]); // __v3 = __t5 - __v1
    info.eval->multiply(vs[3], vs[2], vs[4]); // __v4 = __v3 * __v2
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t6 = blend(__s0@1010000000000000, __s1@0000101000010000, __v0@0000000000100001)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(ss[0], bits["1010000000000000"], t6_1);
    info.eval->multiply_plain(ss[1], bits["0000101000010000"], t6_2);
    info.eval->multiply_plain(vs[0], bits["0000000000100001"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    info.eval->sub(ts[6], vs[1], vs[5]); // __v5 = __t6 - __v1
    
    // __t7 = blend(__v5@1010001000010001, __v3@0000100000100000)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(vs[5], bits["1010001000010001"], t7_1);
    info.eval->multiply_plain(vs[3], bits["0000100000100000"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    
    // __t8 = blend(__v3@1010001000010001, __v5@0000100000100000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(vs[3], bits["1010001000010001"], t8_1);
    info.eval->multiply_plain(vs[5], bits["0000100000100000"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    info.eval->multiply(ts[7], ts[8], vs[6]); // __v6 = __t7 * __t8
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    