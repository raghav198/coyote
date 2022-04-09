
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0000100", info);
    add_bitstring(bits, "1010000", info);
    add_bitstring(bits, "0000001", info);
    add_bitstring(bits, "0101011", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(8);
    ts[0] = encrypt_input("01111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111", info);
    ts[1] = encrypt_input("01111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111", info);
    ts[2] = encrypt_input("0101111", info);
    ts[3] = encrypt_input("1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111110", info);
    ts[4] = encrypt_input("1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[10];
    ctxt ss[4];

    vs[0] = ts[0]; // vector load instr
    info.eval->add(ts[2], vs[0], vs[1]); // __v1 = __t2 + __v0
    info.eval->rotate_rows(vs[1], -6, gk, ss[0]); // __s0 = __v1 >> 6
    vs[2] = ts[3]; // vector load instr
    
    // __t5 = blend(__s0@1010000, __v0@0101011)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(ss[0], bits["1010000"], t5_1);
    info.eval->multiply_plain(vs[0], bits["0101011"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->multiply(ts[5], vs[2], vs[3]); // __v3 = __t5 * __v2
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -6, gk, ss[1]); // __s1 = __v3 >> 6
    info.eval->add(ss[1], vs[3], vs[4]); // __v4 = __s1 + __v3
    info.eval->rotate_rows(vs[4], -4, gk, ss[2]); // __s2 = __v4 >> 4
    
    // __t6 = blend(__s0@0000100, __v1@0000001)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(ss[0], bits["0000100"], t6_1);
    info.eval->multiply_plain(vs[1], bits["0000001"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    info.eval->multiply(ts[6], ss[2], vs[5]); // __v5 = __t6 * __s2
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t7 = blend(__s1@0000100, __v3@0000001)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[1], bits["0000100"], t7_1);
    info.eval->multiply_plain(vs[3], bits["0000001"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->add(ts[7], vs[5], vs[6]); // __v6 = __t7 + __v5
    info.eval->rotate_rows(vs[6], -5, gk, ss[3]); // __s3 = __v6 >> 5
    info.eval->multiply(vs[1], vs[6], vs[7]); // __v7 = __v1 * __v6
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->multiply(vs[0], ss[3], vs[8]); // __v8 = __v0 * __s3
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->add(vs[8], vs[7], vs[9]); // __v9 = __v8 + __v7
    return vs[9];
}
    