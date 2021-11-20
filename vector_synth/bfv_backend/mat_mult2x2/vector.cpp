
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0101", info);
    add_bitstring(bits, "1010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(6);
    ts[0] = encrypt_input("11011111101111111010", info);
    ts[1] = encrypt_input("11111110101111111010", info);
    ts[2] = encrypt_input("11010111111111011011", info);
    ts[3] = encrypt_input("11011111101101111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[3];
    ctxt ss[0];

    info.eval->multiply(ts[0], ts[1], vs[0]); // __v0 = __t0 * __t1
    info.eval->relinearize_inplace(vs[0], rk);
    info.eval->multiply(ts[2], ts[3], vs[1]); // __v1 = __t2 * __t3
    info.eval->relinearize_inplace(vs[1], rk);
    
    // __t4 = blend(__v1@1010, __v0@0101)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[1], bits["1010"], t4_1);
    info.eval->multiply_plain(vs[0], bits["0101"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__v0@1010, __v1@0101)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(vs[0], bits["1010"], t5_1);
    info.eval->multiply_plain(vs[1], bits["0101"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->add(ts[4], ts[5], vs[2]); // __v2 = __t4 + __t5
    return vs[2];
}
    