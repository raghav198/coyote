
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{
    std::map<std::string, ptxt> bits;
    add_bitstring(bits, "0010", info);
    add_bitstring(bits, "0111", info);
    add_bitstring(bits, "1000", info);
    add_bitstring(bits, "0101", info);
    add_bitstring(bits, "0001", info);
    add_bitstring(bits, "0100", info);
    add_bitstring(bits, "1011", info);
    return bits;
}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{
    std::vector<ctxt> ts(14);
    ts[0] = encrypt_input("110111111110", info);
    ts[1] = encrypt_input("111110111110", info);
    ts[2] = encrypt_input("110111111110", info);
    ts[3] = encrypt_input("111110111110", info);
    ts[4] = encrypt_input("110111111110", info);
    ts[5] = encrypt_input("111110111110", info);
    ts[8] = encrypt_input("110111111110", info);
    ts[9] = encrypt_input("111110111110", info);
    return ts;
}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[7];
    ctxt ss[0];

    info.eval->sub(ts[0], ts[1], vs[0]); // __v0 = __t0 - __t1
    info.eval->sub(ts[2], ts[3], vs[1]); // __v1 = __t2 - __t3
    info.eval->sub(ts[4], ts[5], vs[2]); // __v2 = __t4 - __t5
    
    // __t6 = blend(__v0@1000, __v1@0101, __v2@0010)
    ctxt t6_1, t6_2, t6_3;
    info.eval->multiply_plain(vs[0], bits["1000"], t6_1);
    info.eval->multiply_plain(vs[1], bits["0101"], t6_2);
    info.eval->multiply_plain(vs[2], bits["0010"], t6_3);
    info.eval->add_many({t6_1, t6_2, t6_3}, ts[6]);
    
    
    // __t7 = blend(__v2@1000, __v0@0101, __v1@0010)
    ctxt t7_1, t7_2, t7_3;
    info.eval->multiply_plain(vs[2], bits["1000"], t7_1);
    info.eval->multiply_plain(vs[0], bits["0101"], t7_2);
    info.eval->multiply_plain(vs[1], bits["0010"], t7_3);
    info.eval->add_many({t7_1, t7_2, t7_3}, ts[7]);
    
    info.eval->multiply(ts[6], ts[7], vs[3]); // __v3 = __t6 * __t7
    info.eval->relinearize_inplace(vs[3], rk);
    info.eval->sub(ts[8], ts[9], vs[4]); // __v4 = __t8 - __t9
    
    // __t10 = blend(__v1@1000, __v4@0100, __v0@0010, __v2@0001)
    ctxt t10_1, t10_2, t10_3, t10_4;
    info.eval->multiply_plain(vs[1], bits["1000"], t10_1);
    info.eval->multiply_plain(vs[4], bits["0100"], t10_2);
    info.eval->multiply_plain(vs[0], bits["0010"], t10_3);
    info.eval->multiply_plain(vs[2], bits["0001"], t10_4);
    info.eval->add_many({t10_1, t10_2, t10_3, t10_4}, ts[10]);
    
    
    // __t11 = blend(__v4@1011, __v2@0100)
    ctxt t11_1, t11_2;
    info.eval->multiply_plain(vs[4], bits["1011"], t11_1);
    info.eval->multiply_plain(vs[2], bits["0100"], t11_2);
    info.eval->add(t11_1, t11_2, ts[11]);
    
    info.eval->multiply(ts[10], ts[11], vs[5]); // __v5 = __t10 * __t11
    info.eval->relinearize_inplace(vs[5], rk);
    
    // __t12 = blend(__v5@1000, __v3@0111)
    ctxt t12_1, t12_2;
    info.eval->multiply_plain(vs[5], bits["1000"], t12_1);
    info.eval->multiply_plain(vs[3], bits["0111"], t12_2);
    info.eval->add(t12_1, t12_2, ts[12]);
    
    
    // __t13 = blend(__v3@1000, __v5@0111)
    ctxt t13_1, t13_2;
    info.eval->multiply_plain(vs[3], bits["1000"], t13_1);
    info.eval->multiply_plain(vs[5], bits["0111"], t13_2);
    info.eval->add(t13_1, t13_2, ts[13]);
    
    info.eval->add(ts[12], ts[13], vs[6]); // __v6 = __t12 + __t13
    return vs[6];
}
    