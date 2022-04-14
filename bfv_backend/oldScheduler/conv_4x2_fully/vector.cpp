
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "010000", info);
    add_bitstring(bits, "101000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(6);
    ts[0] = encrypt_input("111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111", info);
    ts[1] = encrypt_input("111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111", info);
    ts[2] = encrypt_input("111111111111111111110111111111111111111111111111111111111111110111111111111111111111111111111111111111110111111111111111111111", info);
    ts[3] = encrypt_input("111111111111111111110111111111111111111111111111111111111111110111111111111111111111111111111111111111110111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[4];
    ctxt ss[1];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    info.eval->multiply(vs[0], vs[1], vs[2]); // __v2 = __v0 * __v1
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -3, gk, ss[0]); // __s0 = __v2 >> 3
    
    // __t4 = blend(__v2@101000, __s0@010000)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[2], bits["101000"], t4_1);
    info.eval->multiply_plain(ss[0], bits["010000"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__s0@101000, __v2@010000)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(ss[0], bits["101000"], t5_1);
    info.eval->multiply_plain(vs[2], bits["010000"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[3]); // __v3 = __t4 + __t5
    return vs[3];
}
    