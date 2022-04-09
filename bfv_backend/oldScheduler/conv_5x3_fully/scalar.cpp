
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 33;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"conv_5x3_fully(sig):0", "conv_5x3_fully(sig):4", "conv_5x3_fully(sig):1", "conv_5x3_fully(ker):2", "conv_5x3_fully(ker):0", "conv_5x3_fully(ker):1", "conv_5x3_fully(sig):2", "conv_5x3_fully(sig):3"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["conv_5x3_fully(sig):0"];
    regs[1] = locs["conv_5x3_fully(ker):0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["conv_5x3_fully(sig):1"];
    regs[4] = locs["conv_5x3_fully(ker):1"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    regs[6] = locs["conv_5x3_fully(sig):2"];
    regs[7] = locs["conv_5x3_fully(ker):2"];
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[5], regs[8], regs[9]);
    info.eval->add(regs[2], regs[9], regs[10]);
    regs[11] = locs["conv_5x3_fully(sig):1"];
    regs[12] = locs["conv_5x3_fully(ker):0"];
    info.eval->multiply(regs[11], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    regs[14] = locs["conv_5x3_fully(sig):2"];
    regs[15] = locs["conv_5x3_fully(ker):1"];
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    regs[17] = locs["conv_5x3_fully(sig):3"];
    regs[18] = locs["conv_5x3_fully(ker):2"];
    info.eval->multiply(regs[17], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[16], regs[19], regs[20]);
    info.eval->add(regs[13], regs[20], regs[21]);
    regs[22] = locs["conv_5x3_fully(sig):2"];
    regs[23] = locs["conv_5x3_fully(ker):0"];
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    regs[25] = locs["conv_5x3_fully(sig):3"];
    regs[26] = locs["conv_5x3_fully(ker):1"];
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    regs[28] = locs["conv_5x3_fully(sig):4"];
    regs[29] = locs["conv_5x3_fully(ker):2"];
    info.eval->multiply(regs[28], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->add(regs[27], regs[30], regs[31]);
    info.eval->add(regs[24], regs[31], regs[32]);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    answer.push_back(regs[21]);
    answer.push_back(regs[32]);
    return answer;
}
    