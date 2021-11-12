
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 57;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:0,1", "b:1,0", "a:1,2", "a:2,1", "b:0,0", "b:1,1", "b:2,2", "a:1,0", "b:2,0", "a:1,1", "b:0,2", "a:2,0", "b:2,1", "a:2,2", "a:0,2", "b:1,2", "a:0,1", "a:0,0"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["a:0,0"];
    regs[1] = locs["b:0,0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["a:0,1"];
    regs[4] = locs["b:1,0"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    regs[7] = locs["a:0,2"];
    info.eval->multiply(regs[7], locs["b:2,0"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[6], regs[8], regs[9]);
    regs[10] = locs["b:0,1"];
    info.eval->multiply(regs[0], regs[10], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    regs[12] = locs["b:1,1"];
    info.eval->multiply(regs[3], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->add(regs[11], regs[13], regs[14]);
    info.eval->multiply(regs[7], locs["b:2,1"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(regs[14], regs[15], regs[16]);
    regs[17] = locs["b:0,2"];
    info.eval->multiply(regs[0], regs[17], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    regs[19] = locs["b:1,2"];
    info.eval->multiply(regs[3], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->add(regs[18], regs[20], regs[21]);
    info.eval->multiply(regs[7], locs["b:2,2"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(regs[21], regs[22], regs[23]);
    regs[24] = locs["a:1,0"];
    info.eval->multiply(regs[24], regs[1], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    regs[26] = locs["a:1,1"];
    info.eval->multiply(regs[26], regs[4], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[25], regs[27], regs[28]);
    regs[29] = locs["a:1,2"];
    info.eval->multiply(regs[29], locs["b:2,0"], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->add(regs[28], regs[30], regs[31]);
    info.eval->multiply(regs[24], regs[10], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->multiply(regs[26], regs[12], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(regs[32], regs[33], regs[34]);
    info.eval->multiply(regs[29], locs["b:2,1"], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->add(regs[34], regs[35], regs[36]);
    info.eval->multiply(regs[24], regs[17], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->multiply(regs[26], regs[19], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(regs[37], regs[38], regs[39]);
    info.eval->multiply(regs[29], locs["b:2,2"], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->add(regs[39], regs[40], regs[41]);
    info.eval->multiply(locs["a:2,0"], regs[1], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->multiply(locs["a:2,1"], regs[4], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[42], regs[43], regs[44]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,0"], regs[45]);
    info.eval->relinearize_inplace(regs[45], rk);
    info.eval->add(regs[44], regs[45], regs[46]);
    info.eval->multiply(locs["a:2,0"], regs[10], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->multiply(locs["a:2,1"], regs[12], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->add(regs[47], regs[48], regs[49]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,1"], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->add(regs[49], regs[50], regs[51]);
    info.eval->multiply(locs["a:2,0"], regs[17], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->multiply(locs["a:2,1"], regs[19], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->add(regs[52], regs[53], regs[54]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,2"], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->add(regs[54], regs[55], regs[56]);
    std::vector<ctxt> answer;
    answer.push_back(regs[9]);
    answer.push_back(regs[16]);
    answer.push_back(regs[23]);
    answer.push_back(regs[31]);
    answer.push_back(regs[36]);
    answer.push_back(regs[41]);
    answer.push_back(regs[46]);
    answer.push_back(regs[51]);
    answer.push_back(regs[56]);
    return answer;
}
    