
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 11;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"790", "880", "217", "838", "291", "432", "346", "895", "413", "305", "132", "491"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys& rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["432"], locs["132"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(regs[0], locs["413"], regs[1]);
    info.eval->multiply(locs["838"], locs["305"], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(regs[2], locs["217"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(regs[1], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(locs["346"], locs["790"], regs[5]);
    info.eval->multiply(locs["895"], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["291"], locs["491"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(regs[8], locs["880"], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(regs[4], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    return answer;
}
    