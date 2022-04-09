
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 39;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"dot_product_10x10_partially(v2):6", "dot_product_10x10_partially(v2):0", "dot_product_10x10_partially(v2):5", "dot_product_10x10_partially(v1):0", "dot_product_10x10_partially(v2):7", "dot_product_10x10_partially(v1):8", "dot_product_10x10_partially(v1):5", "dot_product_10x10_partially(v1):1", "dot_product_10x10_partially(v1):6", "dot_product_10x10_partially(v2):8", "dot_product_10x10_partially(v2):9", "dot_product_10x10_partially(v2):2", "dot_product_10x10_partially(v2):4", "dot_product_10x10_partially(v1):2", "dot_product_10x10_partially(v1):9", "dot_product_10x10_partially(v2):1", "dot_product_10x10_partially(v1):7", "dot_product_10x10_partially(v2):3", "dot_product_10x10_partially(v1):4", "dot_product_10x10_partially(v1):3"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["dot_product_10x10_partially(v1):0"];
    regs[1] = locs["dot_product_10x10_partially(v2):0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["dot_product_10x10_partially(v1):1"];
    regs[4] = locs["dot_product_10x10_partially(v2):1"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    regs[7] = locs["dot_product_10x10_partially(v1):2"];
    regs[8] = locs["dot_product_10x10_partially(v2):2"];
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    regs[10] = locs["dot_product_10x10_partially(v1):3"];
    regs[11] = locs["dot_product_10x10_partially(v2):3"];
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    regs[13] = locs["dot_product_10x10_partially(v1):4"];
    regs[14] = locs["dot_product_10x10_partially(v2):4"];
    info.eval->multiply(regs[13], regs[14], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(regs[12], regs[15], regs[16]);
    info.eval->add(regs[9], regs[16], regs[17]);
    info.eval->add(regs[6], regs[17], regs[18]);
    regs[19] = locs["dot_product_10x10_partially(v1):5"];
    regs[20] = locs["dot_product_10x10_partially(v2):5"];
    info.eval->multiply(regs[19], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    regs[22] = locs["dot_product_10x10_partially(v1):6"];
    regs[23] = locs["dot_product_10x10_partially(v2):6"];
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->add(regs[21], regs[24], regs[25]);
    regs[26] = locs["dot_product_10x10_partially(v1):7"];
    regs[27] = locs["dot_product_10x10_partially(v2):7"];
    info.eval->multiply(regs[26], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    regs[29] = locs["dot_product_10x10_partially(v1):8"];
    regs[30] = locs["dot_product_10x10_partially(v2):8"];
    info.eval->multiply(regs[29], regs[30], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    regs[32] = locs["dot_product_10x10_partially(v1):9"];
    regs[33] = locs["dot_product_10x10_partially(v2):9"];
    info.eval->multiply(regs[32], regs[33], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->add(regs[31], regs[34], regs[35]);
    info.eval->add(regs[28], regs[35], regs[36]);
    info.eval->add(regs[25], regs[36], regs[37]);
    info.eval->add(regs[18], regs[37], regs[38]);
    std::vector<ctxt> answer;
    answer.push_back(regs[38]);
    return answer;
}
    