
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "000000100", info);
    add_bitstring(bits, "000001000", info);
    add_bitstring(bits, "000010000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(7);
    ts[0] = encrypt_input("111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", info);
    ts[1] = encrypt_input("111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111", info);
    ts[2] = encrypt_input("111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111110111111111111111111111111111111111111111111", info);
    ts[3] = encrypt_input("111111111111111111110111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111110111111111111111111111111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[6];
    ctxt ss[3];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    info.eval->multiply(vs[0], vs[1], vs[2]); // __v2 = __v0 * __v1
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -4, gk, ss[0]); // __s0 = __v2 >> 4
    info.eval->rotate_rows(vs[2], -1, gk, ss[1]); // __s1 = __v2 >> 1
    info.eval->rotate_rows(vs[2], -6, gk, ss[2]); // __s2 = __v2 >> 6
    
    // __t4 = blend(__s2@000010000, __s0@000001000, __s1@000000100)
    ctxt t4_1, t4_2, t4_3;
    info.eval->multiply_plain(ss[2], bits["000010000"], t4_1);
    info.eval->multiply_plain(ss[0], bits["000001000"], t4_2);
    info.eval->multiply_plain(ss[1], bits["000000100"], t4_3);
    info.eval->add_many({t4_1, t4_2, t4_3}, ts[4]);
    
    
    // __t5 = blend(__s1@000010000, __s2@000001000, __s0@000000100)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(ss[1], bits["000010000"], t5_1);
    info.eval->multiply_plain(ss[2], bits["000001000"], t5_2);
    info.eval->multiply_plain(ss[0], bits["000000100"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[3]); // __v3 = __t4 + __t5
    info.eval->add(ss[1], vs[3], vs[4]); // __v4 = __s1 + __v3
    
    // __t6 = blend(__s0@000010000, __v2@000000100)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(ss[0], bits["000010000"], t6_1);
    info.eval->multiply_plain(vs[2], bits["000000100"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    info.eval->add(ts[6], vs[3], vs[5]); // __v5 = __t6 + __v3
    return vs[5];
}
    