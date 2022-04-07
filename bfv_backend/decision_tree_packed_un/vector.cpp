
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000001000", info);
    add_bitstring(bits, "000001111", info);
    add_bitstring(bits, "001010000", info);
    add_bitstring(bits, "000000101", info);
    add_bitstring(bits, "000001010", info);
    add_bitstring(bits, "000100000", info);
    add_bitstring(bits, "100000000", info);
    add_bitstring(bits, "100001010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(11);
    ts[0] = encrypt_input("111111111111111111111111111100000111111111111111111111111111110111111111111111111111111111110", info);
    ts[1] = encrypt_input("111111111111111111111111111100000111111111111111111111111111110111111111111111111111111111110", info);
    ts[2] = encrypt_input("011111111111111111111111111111011111111111111111111111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111111", info);
    ts[3] = encrypt_input("011111111111111111111111111111011111111111111111111111111111011111111111111111111111111111111111111111111111111111111111111111111111111111111111111011111111111111111111111111111", info);
    ts[4] = encrypt_input("101011010", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[10];
    ctxt ss[8];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -6, gk, ss[0]); // __s0 = __v0 >> 6
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -1, gk, ss[1]); // __s1 = __v1 >> 1
    
    // __t5 = blend(__v0@100001010, __s0@001010000)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(vs[0], bits["100001010"], t5_1);
    info.eval->multiply_plain(ss[0], bits["001010000"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[2]); // __v2 = __t4 + __t5
    info.eval->rotate_rows(vs[2], -1, gk, ss[2]); // __s2 = __v2 >> 1
    
    // __t6 = blend(__s0@001010000, __v0@000001010, __s2@000000101)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(ss[0], bits["001010000"], t6_1);
    info.eval->multiply_plain(vs[0], bits["000001010"], t6_2);
    info.eval->multiply_plain(ss[2], bits["000000101"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    
    // __t7 = blend(__s1@001010000, __v1@000001111)
    ctxt t7_1, t7_2;
    info.eval->multiply_plain(ss[1], bits["001010000"], t7_1);
    info.eval->multiply_plain(vs[1], bits["000001111"], t7_2);
    info.eval->add(t7_1, t7_2, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->rotate_rows(vs[3], -7, gk, ss[3]); // __s3 = __v3 >> 7
    info.eval->rotate_rows(vs[3], -8, gk, ss[4]); // __s4 = __v3 >> 8
    info.eval->rotate_rows(vs[3], -4, gk, ss[5]); // __s5 = __v3 >> 4
    
    // __t8 = blend(__s4@000100000, __v3@000001000)
    ctxt t8_1, t8_2;
    info.eval->multiply_plain(ss[4], bits["000100000"], t8_1);
    info.eval->multiply_plain(vs[3], bits["000001000"], t8_2);
    info.eval->add(t8_1, t8_2, ts[8]);
    
    
    // __t9 = blend(__s5@000100000, __s4@000001000)
    ctxt t9_1, t9_2;
    info.eval->multiply_plain(ss[5], bits["000100000"], t9_1);
    info.eval->multiply_plain(ss[4], bits["000001000"], t9_2);
    info.eval->add(t9_1, t9_2, ts[9]);
    
    info.eval->add(ts[8], ts[9], vs[4]); // __v4 = __t8 + __t9
    info.eval->multiply(ss[2], vs[4], vs[5]); // __v5 = __s2 * __v4
    info.eval->relinearize_inplace(vs[5], rk);
    info.eval->rotate_rows(vs[5], -6, gk, ss[6]); // __s6 = __v5 >> 6
    
    // __t10 = blend(__s6@100000000, __v5@000001000)
    ctxt t10_1, t10_2;
    info.eval->multiply_plain(ss[6], bits["100000000"], t10_1);
    info.eval->multiply_plain(vs[5], bits["000001000"], t10_2);
    info.eval->add(t10_1, t10_2, ts[10]);
    
    info.eval->add(ss[3], ts[10], vs[6]); // __v6 = __s3 + __t10
    info.eval->rotate_rows(vs[6], -4, gk, ss[7]); // __s7 = __v6 >> 4
    info.eval->multiply(vs[2], vs[6], vs[7]); // __v7 = __v2 * __v6
    info.eval->relinearize_inplace(vs[7], rk);
    info.eval->multiply(vs[0], ss[7], vs[8]); // __v8 = __v0 * __s7
    info.eval->relinearize_inplace(vs[8], rk);
    info.eval->add(vs[8], vs[7], vs[9]); // __v9 = __v8 + __v7
    return vs[9];
}
    