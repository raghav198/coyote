
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "100000000000001010011101000", info);
    add_bitstring(bits, "010000000000100000100010000", info);
    add_bitstring(bits, "000001010010000000000000000", info);
    add_bitstring(bits, "100001010010001010011101000", info);
    add_bitstring(bits, "000000000000100000000010000", info);
    add_bitstring(bits, "010000000000000000100000000", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(6);
    ts[0] = encrypt_input("000000000111111111111111111111111111111111111111111111111110000000001111111111111111111111110001111111111111111111111111000", info);
    ts[2] = encrypt_input("111111111111111111111111111111111111111111111111111111111111111111111111110000011111111111111111111111101111111111111111111111111111111111111111111111111100111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111100111111111111111111111111011111111111111111111111100111111111111111111111111101111111111111111111111111011111111111111111111111111111111111111111111111111", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[6];

    vs[0] = ts[0]; // vector load instr
    vs[1] = ts[2]; // vector load instr
    info.eval->sub(vs[0], vs[1], vs[2]); // __v2 = __v0 - __v1
    info.eval->rotate_rows(vs[2], -9, gk, ss[0]); // __s0 = __v2 >> 9
    info.eval->rotate_rows(vs[2], -4, gk, ss[1]); // __s1 = __v2 >> 4
    info.eval->rotate_rows(vs[2], -23, gk, ss[2]); // __s2 = __v2 >> 23
    info.eval->rotate_rows(vs[2], -25, gk, ss[3]); // __s3 = __v2 >> 25
    info.eval->rotate_rows(vs[2], -3, gk, ss[4]); // __s4 = __v2 >> 3
    info.eval->rotate_rows(vs[2], -2, gk, ss[5]); // __s5 = __v2 >> 2
    info.eval->multiply(vs[2], vs[2], vs[4]); // __v4 = __v2 * __v2
    info.eval->relinearize_inplace(vs[4], rk);
    
    // __t4 = blend(__v2@100000000000001010011101000, __v2@010000000000100000100010000, __v2@000001010010000000000000000)
    ctxt t4_1, t4_2, t4_3;
    info.eval->multiply_plain(vs[2], bits["100000000000001010011101000"], t4_1);
    info.eval->multiply_plain(vs[2], bits["010000000000100000100010000"], t4_2);
    info.eval->multiply_plain(vs[2], bits["000001010010000000000000000"], t4_3);
    info.eval->add_many({t4_1, t4_2, t4_3}, ts[4]);
    
    
    // __t5 = blend(__v2@100001010010001010011101000, __v2@010000000000000000100000000, __v2@000000000000100000000010000)
    ctxt t5_1, t5_2, t5_3;
    info.eval->multiply_plain(vs[2], bits["100001010010001010011101000"], t5_1);
    info.eval->multiply_plain(vs[2], bits["010000000000000000100000000"], t5_2);
    info.eval->multiply_plain(vs[2], bits["000000000000100000000010000"], t5_3);
    info.eval->add_many({t5_1, t5_2, t5_3}, ts[5]);
    
    info.eval->multiply(ts[4], ts[5], vs[6]); // __v6 = __t4 * __t5
    info.eval->relinearize_inplace(vs[6], rk);
    return vs[6];
}
    