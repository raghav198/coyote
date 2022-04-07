
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 11;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"dot_product_3x3_un(v2):1", "dot_product_3x3_un(v1):0", "dot_product_3x3_un(v1):1", "dot_product_3x3_un(v2):2", "dot_product_3x3_un(v2):0", "dot_product_3x3_un(v1):2"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["dot_product_3x3_un(v1):0"];
    regs[1] = locs["dot_product_3x3_un(v2):0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["dot_product_3x3_un(v1):1"];
    regs[4] = locs["dot_product_3x3_un(v2):1"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    regs[6] = locs["dot_product_3x3_un(v1):2"];
    regs[7] = locs["dot_product_3x3_un(v2):2"];
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[5], regs[8], regs[9]);
    info.eval->add(regs[2], regs[9], regs[10]);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    return answer;
}
    