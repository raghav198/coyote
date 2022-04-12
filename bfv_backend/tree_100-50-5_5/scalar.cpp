
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 7;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"743", "330", "593", "949", "613", "346", "220", "797"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["220"], locs["613"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(regs[0], locs["330"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(regs[1], locs["797"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(regs[2], locs["346"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["949"], locs["743"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(regs[4], locs["593"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(regs[3], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    return answer;
}
    