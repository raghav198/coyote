
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 3;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"184", "30", "916", "1003"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["916"], locs["30"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(regs[0], locs["1003"], regs[1]);
    info.eval->multiply(regs[1], locs["184"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[2]);
    return answer;
}
    