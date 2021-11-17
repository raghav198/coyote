
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00101000", info);
    add_bitstring(bits, "00000101", info);
    add_bitstring(bits, "00001111", info);
    add_bitstring(bits, "11110000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(7);
    ts[0] = encrypt_input("1111111110111111111011011110101101111010", info);
    ts[2] = encrypt_input("000011111110111111011010", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[4];
    ctxt ss[3];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -4, gk, ss[0]); // __s0 = __v1 >> 4
    
    // __t4 = blend(__s0@11110000, __v1@00001111)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(ss[0], bits["11110000"], t4_1);
    info.eval->multiply_plain(vs[1], bits["00001111"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    info.eval->multiply(vs[0], ts[4], vs[2]); // __v2 = __v0 * __t4
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -2, gk, ss[1]); // __s1 = __v2 >> 2
    info.eval->rotate_rows(vs[2], -1, gk, ss[2]); // __s2 = __v2 >> 1
    
    // __t5 = blend(__s2@00101000, __v2@00000101)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(ss[2], bits["00101000"], t5_1);
    info.eval->multiply_plain(vs[2], bits["00000101"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    
    // __t6 = blend(__s1@00101000, __s2@00000101)
    ctxt t6_1, t6_2;
    info.eval->multiply_plain(ss[1], bits["00101000"], t6_1);
    info.eval->multiply_plain(ss[2], bits["00000101"], t6_2);
    info.eval->add(t6_1, t6_2, ts[6]);
    
    info.eval->add(ts[5], ts[6], vs[3]); // __v3 = __t5 + __t6
    return vs[3];
}
    