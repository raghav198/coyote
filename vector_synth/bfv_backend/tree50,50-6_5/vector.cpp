
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "001", info);
    add_bitstring(bits, "100", info);
    add_bitstring(bits, "010", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(12);
    ts[0] = encrypt_input("10011010", info);
    ts[1] = encrypt_input("1111110", info);
    ts[2] = encrypt_input("111111111", info);
    ts[3] = encrypt_input("1110111", info);
    ts[5] = encrypt_input("0011", info);
    ts[6] = encrypt_input("101100", info);
    ts[9] = encrypt_input("00101", info);
    ts[10] = encrypt_input("11100", info);
    ts[11] = encrypt_input("1000", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[9];
    ctxt ss[2];

    info.eval->add(ts[0], ts[1], vs[0]); // __v0 = __t0 + __t1
    
    // __t4 = blend(__v0@010, __t3@101)
    ctxt t4_1;
    info.eval->multiply_plain(vs[0], bits["010"], t4_1);
    info.eval->add(t4_1, ts[3], ts[4]);
    
    info.eval->multiply(ts[2], ts[4], vs[1]); // __v1 = __t2 * __t4
    info.eval->relinearize_inplace(vs[1], rk);
    info.eval->rotate_rows(vs[1], -2, gk, ss[0]); // __s0 = __v1 >> 2
    info.eval->add(vs[1], vs[0], vs[2]); // __v2 = __v1 + __v0
    
    // __t7 = blend(__v2@100, __t5@001)
    ctxt t7_1;
    info.eval->multiply_plain(vs[2], bits["100"], t7_1);
    info.eval->add(t7_1, ts[5], ts[7]);
    
    
    // __t8 = blend(__v1@001, __t6@100)
    ctxt t8_1;
    info.eval->multiply_plain(vs[1], bits["001"], t8_1);
    info.eval->add(t8_1, ts[6], ts[8]);
    
    info.eval->add(ts[7], ts[8], vs[3]); // __v3 = __t7 + __t8
    info.eval->multiply(vs[3], ts[9], vs[4]); // __v4 = __v3 * __t9
    info.eval->relinearize_inplace(vs[4], rk);
    info.eval->rotate_rows(vs[4], -1, gk, ss[1]); // __s1 = __v4 >> 1
    info.eval->add(ts[10], vs[3], vs[5]); // __v5 = __t10 + __v3
    info.eval->add(ss[1], ss[0], vs[6]); // __v6 = __s1 + __s0
    info.eval->add(vs[6], vs[5], vs[7]); // __v7 = __v6 + __v5
    info.eval->add(vs[7], ts[11], vs[8]); // __v8 = __v7 + __t11
    return vs[8];
}
    