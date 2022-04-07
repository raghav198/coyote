
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 23;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"conv_5x3_un(ker):2", "conv_5x3_un(sig):3", "conv_5x3_un(sig):4", "conv_5x3_un(ker):0", "conv_5x3_un(sig):1", "conv_5x3_un(sig):0", "conv_5x3_un(ker):1", "conv_5x3_un(sig):2"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["conv_5x3_un(sig):0"];
    regs[1] = locs["conv_5x3_un(ker):0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["conv_5x3_un(sig):1"];
    regs[4] = locs["conv_5x3_un(ker):1"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    regs[6] = locs["conv_5x3_un(sig):2"];
    regs[7] = locs["conv_5x3_un(ker):2"];
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[5], regs[8], regs[9]);
    info.eval->add(regs[2], regs[9], regs[10]);
    info.eval->multiply(regs[3], regs[1], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->multiply(regs[6], regs[4], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    regs[13] = locs["conv_5x3_un(sig):3"];
    info.eval->multiply(regs[13], regs[7], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->add(regs[12], regs[14], regs[15]);
    info.eval->add(regs[11], regs[15], regs[16]);
    info.eval->multiply(regs[6], regs[1], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(regs[13], regs[4], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    regs[19] = locs["conv_5x3_un(sig):4"];
    info.eval->multiply(regs[19], regs[7], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->add(regs[18], regs[20], regs[21]);
    info.eval->add(regs[17], regs[21], regs[22]);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    answer.push_back(regs[16]);
    answer.push_back(regs[22]);
    return answer;
}
    