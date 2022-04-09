
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "11110000", info);
    add_bitstring(bits, "00001111", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(5);
    ts[0] = encrypt_input("111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111110111111111111111111111111011111111111111111111111111010111111111111111111111111011111111111111111111111111010", info);
    ts[1] = encrypt_input("111111111111111111111111111111111111111111111111111110111111111111111111111111111111111111111111111111111110111111111111111111111111011111111111111111111111111010111111111111111111111111011111111111111111111111111010", info);
    ts[2] = encrypt_input("1111111111111111111111110111111111111111111111111110101111111111111111111111111111111111111111111111111111100000", info);
    ts[3] = encrypt_input("1111111111111111111111110111111111111111111111111110101111111111111111111111111111111111111111111111111111100000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[4];
    ctxt ss[2];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -4, gk, ss[0]); // __s0 = __v1 >> 4
    
    // __t4 = blend(__v1@11110000, __s0@00001111)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[1], bits["11110000"], t4_1);
    info.eval->multiply_plain(ss[0], bits["00001111"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    info.eval->multiply(vs[0], ts[4], vs[2]); // __v2 = __v0 * __t4
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -7, gk, ss[1]); // __s1 = __v2 >> 7
    info.eval->add(ss[1], vs[2], vs[3]); // __v3 = __s1 + __v2
    return vs[3];
}
    