
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 11;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"505", "883", "380", "755", "381", "121", "210", "869", "617", "85", "720", "805"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["883"], locs["720"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["85"], locs["380"], regs[1]);
    info.eval->multiply(regs[1], locs["381"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(locs["755"], regs[2], regs[3]);
    info.eval->add(regs[0], regs[3], regs[4]);
    info.eval->multiply(locs["617"], locs["121"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(locs["210"], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["805"], locs["869"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[4], regs[8], regs[9]);
    info.eval->multiply(regs[9], locs["505"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    return answer;
}
    