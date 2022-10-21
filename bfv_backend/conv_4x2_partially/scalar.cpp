
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 19;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"conv_4x2_partially(ker):0", "conv_4x2_partially(sig):3", "conv_4x2_partially(sig):2", "conv_4x2_partially(sig):1", "conv_4x2_partially(ker):1", "conv_4x2_partially(sig):0"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["conv_4x2_partially(sig):0"];
    regs[1] = locs["conv_4x2_partially(ker):0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["conv_4x2_partially(sig):1"];
    regs[4] = locs["conv_4x2_partially(ker):1"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    regs[7] = locs["conv_4x2_partially(ker):0"];
    info.eval->multiply(regs[3], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    regs[9] = locs["conv_4x2_partially(sig):2"];
    regs[10] = locs["conv_4x2_partially(ker):1"];
    info.eval->multiply(regs[9], regs[10], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->add(regs[8], regs[11], regs[12]);
    regs[13] = locs["conv_4x2_partially(ker):0"];
    info.eval->multiply(regs[9], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    regs[15] = locs["conv_4x2_partially(sig):3"];
    regs[16] = locs["conv_4x2_partially(ker):1"];
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->add(regs[14], regs[17], regs[18]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    answer.push_back(regs[12]);
    answer.push_back(regs[18]);
    return answer;
}
    