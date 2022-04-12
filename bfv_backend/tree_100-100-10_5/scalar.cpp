
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 33;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"359", "440", "98", "613", "879", "746", "582", "256", "846", "523", "520", "268", "738", "616", "931", "321", "841", "182", "847", "944", "743", "1008", "585", "93", "578", "569", "318", "916", "806", "574", "621", "269"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["93"], locs["182"], regs[0]);
    info.eval->add(locs["931"], regs[0], regs[1]);
    info.eval->add(locs["879"], locs["621"], regs[2]);
    info.eval->add(locs["269"], locs["738"], regs[3]);
    info.eval->multiply(regs[2], regs[3], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->add(regs[4], locs["916"], regs[5]);
    info.eval->multiply(regs[5], locs["318"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(locs["440"], regs[6], regs[7]);
    info.eval->add(regs[7], locs["746"], regs[8]);
    info.eval->add(regs[1], regs[8], regs[9]);
    info.eval->add(locs["1008"], locs["574"], regs[10]);
    info.eval->add(locs["846"], locs["569"], regs[11]);
    info.eval->add(locs["269"], regs[11], regs[12]);
    info.eval->add(locs["98"], locs["321"], regs[13]);
    info.eval->add(regs[13], locs["841"], regs[14]);
    info.eval->add(locs["1008"], regs[14], regs[15]);
    info.eval->multiply(regs[12], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[10], regs[16], regs[17]);
    info.eval->multiply(regs[9], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(regs[18], locs["268"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->multiply(locs["256"], locs["523"], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->multiply(locs["578"], locs["847"], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->multiply(locs["616"], regs[21], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(locs["944"], locs["359"], regs[23]);
    info.eval->add(regs[23], locs["613"], regs[24]);
    info.eval->multiply(regs[22], regs[24], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(locs["585"], regs[25], regs[26]);
    info.eval->multiply(locs["520"], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[27], locs["806"], regs[28]);
    info.eval->multiply(locs["743"], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->multiply(regs[20], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->multiply(regs[30], locs["582"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->multiply(regs[19], regs[31], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[32]);
    return answer;
}
    