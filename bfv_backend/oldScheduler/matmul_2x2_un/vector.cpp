
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "00110011", info);
    add_bitstring(bits, "11001100", info);
    add_bitstring(bits, "01010101", info);
    add_bitstring(bits, "10101010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(6);
    ts[0] = encrypt_input("111111111111111111111111111111111111111000111111111111111110111111111111111111101000", info);
    ts[1] = encrypt_input("111111111111111111111111111111111111111000111111111111111110111111111111111111101000", info);
    ts[2] = encrypt_input("011111111111111111111011111111111111111011011111111111111111110011111111111111111010", info);
    ts[3] = encrypt_input("011111111111111111111011111111111111111011011111111111111111110011111111111111111010", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[4];
    ctxt ss[3];

    vs[0] = ts[0]; // vector load instr
    info.eval->rotate_rows(vs[0], -2, gk, ss[0]); // __s0 = __v0 >> 2
    vs[1] = ts[2]; // vector load instr
    info.eval->rotate_rows(vs[1], -7, gk, ss[1]); // __s1 = __v1 >> 7
    
    // __t4 = blend(__v0@11001100, __s0@00110011)
    ctxt t4_1, t4_2;
    info.eval->multiply_plain(vs[0], bits["11001100"], t4_1);
    info.eval->multiply_plain(ss[0], bits["00110011"], t4_2);
    info.eval->add(t4_1, t4_2, ts[4]);
    
    
    // __t5 = blend(__s1@10101010, __v1@01010101)
    ctxt t5_1, t5_2;
    info.eval->multiply_plain(ss[1], bits["10101010"], t5_1);
    info.eval->multiply_plain(vs[1], bits["01010101"], t5_2);
    info.eval->add(t5_1, t5_2, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[2]); // __v2 = __t4 * __t5
    info.eval->relinearize_inplace(vs[2], rk);
    info.eval->rotate_rows(vs[2], -4, gk, ss[2]); // __s2 = __v2 >> 4
    info.eval->add(vs[2], ss[2], vs[3]); // __v3 = __v2 + __s2
    return vs[3];
}
    