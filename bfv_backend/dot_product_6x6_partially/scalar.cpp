
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 23;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"dot_product_6x6_partially(v1):5", "dot_product_6x6_partially(v1):1", "dot_product_6x6_partially(v2):4", "dot_product_6x6_partially(v2):0", "dot_product_6x6_partially(v1):2", "dot_product_6x6_partially(v1):0", "dot_product_6x6_partially(v1):3", "dot_product_6x6_partially(v2):5", "dot_product_6x6_partially(v2):3", "dot_product_6x6_partially(v2):1", "dot_product_6x6_partially(v2):2", "dot_product_6x6_partially(v1):4"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["dot_product_6x6_partially(v1):0"];
    regs[1] = locs["dot_product_6x6_partially(v2):0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["dot_product_6x6_partially(v1):1"];
    regs[4] = locs["dot_product_6x6_partially(v2):1"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    regs[6] = locs["dot_product_6x6_partially(v1):2"];
    regs[7] = locs["dot_product_6x6_partially(v2):2"];
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[5], regs[8], regs[9]);
    info.eval->add(regs[2], regs[9], regs[10]);
    regs[11] = locs["dot_product_6x6_partially(v1):3"];
    regs[12] = locs["dot_product_6x6_partially(v2):3"];
    info.eval->multiply(regs[11], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    regs[14] = locs["dot_product_6x6_partially(v1):4"];
    regs[15] = locs["dot_product_6x6_partially(v2):4"];
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    regs[17] = locs["dot_product_6x6_partially(v1):5"];
    regs[18] = locs["dot_product_6x6_partially(v2):5"];
    info.eval->multiply(regs[17], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[16], regs[19], regs[20]);
    info.eval->add(regs[13], regs[20], regs[21]);
    info.eval->add(regs[10], regs[21], regs[22]);
    std::vector<ctxt> answer;
    answer.push_back(regs[22]);
    return answer;
}
    