
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 7;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"438", "698", "699", "792", "766", "1012", "876", "740"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["1012"], locs["740"], regs[0]);
    info.eval->add(locs["438"], locs["792"], regs[1]);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(locs["699"], locs["766"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["876"], locs["698"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[3], regs[4], regs[5]);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    return answer;
}
    