
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 17;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"597", "558", "538", "792", "702", "213", "475", "2", "170", "644", "739", "948", "331", "575", "966", "563", "631", "131"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["644"], locs["631"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["131"], locs["538"], regs[1]);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->add(locs["966"], locs["475"], regs[3]);
    info.eval->add(regs[2], regs[3], regs[4]);
    info.eval->add(locs["563"], regs[4], regs[5]);
    info.eval->add(locs["739"], locs["170"], regs[6]);
    info.eval->add(locs["597"], regs[6], regs[7]);
    info.eval->add(locs["558"], locs["792"], regs[8]);
    info.eval->add(locs["702"], locs["948"], regs[9]);
    info.eval->multiply(regs[8], regs[9], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(locs["331"], locs["213"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->multiply(locs["2"], locs["575"], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->multiply(regs[11], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->add(regs[10], regs[13], regs[14]);
    info.eval->multiply(regs[7], regs[14], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(regs[5], regs[15], regs[16]);
    std::vector<ctxt> answer;
    answer.push_back(regs[16]);
    return answer;
}
    