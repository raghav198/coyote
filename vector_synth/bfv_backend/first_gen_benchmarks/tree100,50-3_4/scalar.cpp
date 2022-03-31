
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 7;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"586", "317", "424", "828", "561", "343", "211", "318"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["561"], locs["211"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["424"], locs["317"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->add(locs["586"], locs["828"], regs[3]);
    info.eval->multiply(locs["343"], locs["318"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[3], regs[4], regs[5]);
    info.eval->add(regs[2], regs[5], regs[6]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    return answer;
}
    