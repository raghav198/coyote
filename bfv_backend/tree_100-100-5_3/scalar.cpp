
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 4;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"780", "797", "49", "982", "601"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["982"], locs["780"], regs[0]);
    info.eval->add(locs["797"], locs["601"], regs[1]);
    info.eval->multiply(regs[1], locs["49"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(regs[0], regs[2], regs[3]);
    std::vector<ctxt> answer;
    answer.push_back(regs[3]);
    return answer;
}
    