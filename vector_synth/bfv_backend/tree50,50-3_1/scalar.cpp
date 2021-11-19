
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 7;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"898", "342", "172", "400", "623", "309", "661", "1013"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["898"], locs["400"], regs[0]);
    info.eval->add(locs["1013"], locs["309"], regs[1]);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->add(locs["623"], locs["172"], regs[3]);
    info.eval->multiply(locs["661"], locs["342"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    std::vector<ctxt> answer;
    answer.push_back(regs[6]);
    return answer;
}
    