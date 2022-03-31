
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 10;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"448", "53", "225", "318", "798", "801", "136", "682", "652", "323", "883"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["136"], locs["323"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["801"], locs["448"], regs[1]);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->add(locs["318"], locs["883"], regs[3]);
    info.eval->multiply(regs[3], locs["53"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[2], regs[4], regs[5]);
    info.eval->multiply(locs["225"], locs["798"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(regs[5], regs[6], regs[7]);
    info.eval->add(locs["652"], regs[7], regs[8]);
    info.eval->add(regs[8], locs["682"], regs[9]);
    std::vector<ctxt> answer;
    answer.push_back(regs[9]);
    return answer;
}
    