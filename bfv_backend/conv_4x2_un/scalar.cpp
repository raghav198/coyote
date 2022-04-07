
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 15;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"conv_4x2_un(ker):1", "conv_4x2_un(sig):2", "conv_4x2_un(sig):3", "conv_4x2_un(sig):0", "conv_4x2_un(ker):0", "conv_4x2_un(sig):1"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["conv_4x2_un(sig):0"];
    regs[1] = locs["conv_4x2_un(ker):0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["conv_4x2_un(sig):1"];
    regs[4] = locs["conv_4x2_un(ker):1"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    info.eval->multiply(regs[3], regs[1], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    regs[8] = locs["conv_4x2_un(sig):2"];
    info.eval->multiply(regs[8], regs[4], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(regs[7], regs[9], regs[10]);
    info.eval->multiply(regs[8], regs[1], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    regs[12] = locs["conv_4x2_un(sig):3"];
    info.eval->multiply(regs[12], regs[4], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->add(regs[11], regs[13], regs[14]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    answer.push_back(regs[10]);
    answer.push_back(regs[14]);
    return answer;
}
    