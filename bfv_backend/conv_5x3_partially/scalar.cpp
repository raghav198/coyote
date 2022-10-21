
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 29;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"conv_5x3_partially(sig):0", "conv_5x3_partially(sig):4", "conv_5x3_partially(sig):3", "conv_5x3_partially(sig):2", "conv_5x3_partially(ker):1", "conv_5x3_partially(ker):0", "conv_5x3_partially(ker):2", "conv_5x3_partially(sig):1"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["conv_5x3_partially(sig):0"];
    regs[1] = locs["conv_5x3_partially(ker):0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["conv_5x3_partially(sig):1"];
    regs[4] = locs["conv_5x3_partially(ker):1"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    regs[6] = locs["conv_5x3_partially(sig):2"];
    regs[7] = locs["conv_5x3_partially(ker):2"];
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[5], regs[8], regs[9]);
    info.eval->add(regs[2], regs[9], regs[10]);
    regs[11] = locs["conv_5x3_partially(ker):0"];
    info.eval->multiply(regs[3], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    regs[13] = locs["conv_5x3_partially(ker):1"];
    info.eval->multiply(regs[6], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    regs[15] = locs["conv_5x3_partially(sig):3"];
    regs[16] = locs["conv_5x3_partially(ker):2"];
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->add(regs[14], regs[17], regs[18]);
    info.eval->add(regs[12], regs[18], regs[19]);
    regs[20] = locs["conv_5x3_partially(ker):0"];
    info.eval->multiply(regs[6], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    regs[22] = locs["conv_5x3_partially(ker):1"];
    info.eval->multiply(regs[15], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    regs[24] = locs["conv_5x3_partially(sig):4"];
    regs[25] = locs["conv_5x3_partially(ker):2"];
    info.eval->multiply(regs[24], regs[25], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(regs[23], regs[26], regs[27]);
    info.eval->add(regs[21], regs[27], regs[28]);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    answer.push_back(regs[19]);
    answer.push_back(regs[28]);
    return answer;
}
    