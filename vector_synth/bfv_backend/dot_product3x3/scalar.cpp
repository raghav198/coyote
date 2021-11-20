
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 5;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:2", "a:0", "a:2", "b:0", "a:1", "b:1"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["a:0"], locs["b:0"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["a:1"], locs["b:1"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(locs["a:2"], locs["b:2"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(regs[1], regs[2], regs[3]);
    info.eval->add(regs[0], regs[3], regs[4]);
    std::vector<ctxt> answer;
    answer.push_back(regs[4]);
    return answer;
}
    