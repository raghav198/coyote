
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 31;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"406", "670", "124", "662", "993", "611", "418", "175", "407", "501", "892", "680", "126", "945", "226", "11", "436", "180", "490", "543", "170", "733", "991", "996", "940", "802", "700", "428", "84", "447", "581"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["670"], locs["436"], regs[0]);
    info.eval->add(regs[0], locs["406"], regs[1]);
    info.eval->add(locs["447"], regs[1], regs[2]);
    info.eval->add(locs["581"], locs["84"], regs[3]);
    info.eval->multiply(locs["802"], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(locs["407"], regs[4], regs[5]);
    info.eval->multiply(locs["700"], locs["180"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["543"], locs["124"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[8], locs["170"], regs[9]);
    info.eval->add(regs[5], regs[9], regs[10]);
    info.eval->add(regs[10], locs["892"], regs[11]);
    info.eval->add(regs[11], locs["175"], regs[12]);
    info.eval->add(regs[2], regs[12], regs[13]);
    info.eval->add(locs["680"], locs["945"], regs[14]);
    info.eval->multiply(regs[14], locs["126"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(regs[15], locs["940"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(locs["733"], locs["991"], regs[17]);
    info.eval->multiply(locs["996"], locs["993"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(regs[17], regs[18], regs[19]);
    info.eval->add(locs["226"], locs["428"], regs[20]);
    info.eval->multiply(regs[20], locs["662"], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->add(regs[19], regs[21], regs[22]);
    info.eval->add(regs[16], regs[22], regs[23]);
    info.eval->add(locs["11"], regs[23], regs[24]);
    info.eval->add(regs[24], locs["124"], regs[25]);
    info.eval->add(locs["490"], regs[25], regs[26]);
    info.eval->multiply(regs[13], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->multiply(regs[27], locs["418"], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->add(locs["501"], locs["611"], regs[29]);
    info.eval->multiply(regs[28], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[30]);
    return answer;
}
    