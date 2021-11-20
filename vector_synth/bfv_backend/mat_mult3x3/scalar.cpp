
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 45;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"a:1,0", "b:0,1", "a:0,1", "a:1,1", "a:2,2", "a:2,0", "a:1,2", "a:0,2", "a:2,1", "b:0,0", "b:2,0", "a:0,0", "b:1,0", "b:1,2", "b:1,1", "b:0,2", "b:2,1", "b:2,2"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["a:0,0"], locs["b:0,0"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["a:0,1"], locs["b:1,0"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->multiply(locs["a:0,2"], locs["b:2,0"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(regs[2], regs[3], regs[4]);
    info.eval->multiply(locs["a:0,0"], locs["b:0,1"], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(locs["a:0,1"], locs["b:1,1"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(regs[5], regs[6], regs[7]);
    info.eval->multiply(locs["a:0,2"], locs["b:2,1"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[7], regs[8], regs[9]);
    info.eval->multiply(locs["a:0,0"], locs["b:0,2"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(locs["a:0,1"], locs["b:1,2"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->add(regs[10], regs[11], regs[12]);
    info.eval->multiply(locs["a:0,2"], locs["b:2,2"], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->add(regs[12], regs[13], regs[14]);
    info.eval->multiply(locs["a:1,0"], locs["b:0,0"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(locs["a:1,1"], locs["b:1,0"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[15], regs[16], regs[17]);
    info.eval->multiply(locs["a:1,2"], locs["b:2,0"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(regs[17], regs[18], regs[19]);
    info.eval->multiply(locs["a:1,0"], locs["b:0,1"], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->multiply(locs["a:1,1"], locs["b:1,1"], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->add(regs[20], regs[21], regs[22]);
    info.eval->multiply(locs["a:1,2"], locs["b:2,1"], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->add(regs[22], regs[23], regs[24]);
    info.eval->multiply(locs["a:1,0"], locs["b:0,2"], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->multiply(locs["a:1,1"], locs["b:1,2"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->add(regs[25], regs[26], regs[27]);
    info.eval->multiply(locs["a:1,2"], locs["b:2,2"], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->add(regs[27], regs[28], regs[29]);
    info.eval->multiply(locs["a:2,0"], locs["b:0,0"], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->multiply(locs["a:2,1"], locs["b:1,0"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->add(regs[30], regs[31], regs[32]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,0"], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(regs[32], regs[33], regs[34]);
    info.eval->multiply(locs["a:2,0"], locs["b:0,1"], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->multiply(locs["a:2,1"], locs["b:1,1"], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->add(regs[35], regs[36], regs[37]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,1"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(regs[37], regs[38], regs[39]);
    info.eval->multiply(locs["a:2,0"], locs["b:0,2"], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->multiply(locs["a:2,1"], locs["b:1,2"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->add(regs[40], regs[41], regs[42]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,2"], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[42], regs[43], regs[44]);
    std::vector<ctxt> answer;
    answer.push_back(regs[4]);
    answer.push_back(regs[9]);
    answer.push_back(regs[14]);
    answer.push_back(regs[19]);
    answer.push_back(regs[24]);
    answer.push_back(regs[29]);
    answer.push_back(regs[34]);
    answer.push_back(regs[39]);
    answer.push_back(regs[44]);
    return answer;
}
    