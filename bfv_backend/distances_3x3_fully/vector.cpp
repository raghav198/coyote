
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "1010001000010001", info);
    add_bitstring(bits, "0000100000100000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(5);
    ts[0] = encrypt_input("0000000011111111111111111111111100111111111111111111111111100001111111111111111111111111", info);
    ts[2] = encrypt_input("1111111111111111111111110011111111111111111111111110111111111111111111111111101111111111111111111111111111111111111111111111111111111111111111111111111110111111111111111111111111011111111111111111111111110001111111111111111111111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[3];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    info.eval->sub(vs[0], vs[1], vs[2]); // __v2 = __v0 - __v1
    info.eval->rotate_rows(vs[2], -8, gk, ss[0]); // __s0 = __v2 >> 8
    info.eval->rotate_rows(vs[2], -4, gk, ss[2]); // __s2 = __v2 >> 4
    info.eval->multiply(vs[2], vs[2], vs[4]); // __v4 = __v2 * __v2
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t4 = blend(__v2@1010001000010001, __v2@0000100000100000)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[2], bits["1010001000010001"], t4_1);
    info.eval->multiply_plain(vs[2], bits["0000100000100000"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    info.eval->multiply(ts[4], ts[4], vs[6]); // __v6 = __t4 * __t4
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    