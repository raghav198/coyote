
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 21;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"conv_4x2_fully(sig):1", "conv_4x2_fully(ker):1", "conv_4x2_fully(ker):0", "conv_4x2_fully(sig):0", "conv_4x2_fully(sig):2", "conv_4x2_fully(sig):3"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["conv_4x2_fully(sig):0"];
    regs[1] = locs["conv_4x2_fully(ker):0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["conv_4x2_fully(sig):1"];
    regs[4] = locs["conv_4x2_fully(ker):1"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    regs[7] = locs["conv_4x2_fully(sig):1"];
    regs[8] = locs["conv_4x2_fully(ker):0"];
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    regs[10] = locs["conv_4x2_fully(sig):2"];
    regs[11] = locs["conv_4x2_fully(ker):1"];
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(regs[9], regs[12], regs[13]);
    regs[14] = locs["conv_4x2_fully(sig):2"];
    regs[15] = locs["conv_4x2_fully(ker):0"];
    info.eval->multiply(regs[14], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    regs[17] = locs["conv_4x2_fully(sig):3"];
    regs[18] = locs["conv_4x2_fully(ker):1"];
    info.eval->multiply(regs[17], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[16], regs[19], regs[20]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    answer.push_back(regs[13]);
    answer.push_back(regs[20]);
    return answer;
}
    