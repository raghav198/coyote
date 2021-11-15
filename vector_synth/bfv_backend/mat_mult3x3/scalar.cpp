
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"a:0,2", "a:0,1", "b:2,0", "b:1,0", "b:0,0", "b:2,1", "a:2,0", "b:1,2", "a:1,1", "b:0,2", "b:0,1", "b:1,1", "b:2,2", "a:1,2", "a:2,2", "a:2,1", "a:1,0", "a:0,0"};
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
    regs[8] = locs["b:2,0"];
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(regs[6], regs[9], regs[10]);
    regs[11] = locs["b:0,1"];
    info.eval->multiply(regs[0], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    regs[13] = locs["b:1,1"];
    info.eval->multiply(regs[3], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->add(regs[12], regs[14], regs[15]);
    regs[16] = locs["b:2,1"];
    info.eval->multiply(regs[7], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->add(regs[15], regs[17], regs[18]);
    regs[19] = locs["b:0,2"];
    info.eval->multiply(regs[0], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    regs[21] = locs["b:1,2"];
    info.eval->multiply(regs[3], regs[21], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(regs[20], regs[22], regs[23]);
    regs[24] = locs["b:2,2"];
    info.eval->multiply(regs[7], regs[24], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(regs[23], regs[25], regs[26]);
    regs[27] = locs["a:1,0"];
    info.eval->multiply(regs[27], regs[1], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    regs[29] = locs["a:1,1"];
    info.eval->multiply(regs[29], regs[4], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->add(regs[28], regs[30], regs[31]);
    regs[32] = locs["a:1,2"];
    info.eval->multiply(regs[32], regs[8], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(regs[31], regs[33], regs[34]);
    info.eval->multiply(regs[27], regs[11], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->multiply(regs[29], regs[13], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->add(regs[35], regs[36], regs[37]);
    info.eval->multiply(regs[32], regs[16], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(regs[37], regs[38], regs[39]);
    info.eval->multiply(regs[27], regs[19], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->multiply(regs[29], regs[21], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->add(regs[40], regs[41], regs[42]);
    info.eval->multiply(regs[32], regs[24], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[42], regs[43], regs[44]);
    regs[45] = locs["a:2,0"];
    info.eval->multiply(regs[45], regs[1], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    regs[47] = locs["a:2,1"];
    info.eval->multiply(regs[47], regs[4], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->add(regs[46], regs[48], regs[49]);
    regs[50] = locs["a:2,2"];
    info.eval->multiply(regs[50], regs[8], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->add(regs[49], regs[51], regs[52]);
    info.eval->multiply(regs[45], regs[11], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->multiply(regs[47], regs[13], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->add(regs[53], regs[54], regs[55]);
    info.eval->multiply(regs[50], regs[16], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->add(regs[55], regs[56], regs[57]);
    info.eval->multiply(regs[45], regs[19], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->multiply(regs[47], regs[21], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->add(regs[58], regs[59], regs[60]);
    info.eval->multiply(regs[50], regs[24], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    info.eval->add(regs[60], regs[61], regs[62]);
    std::vector<ctxt> answer;
    answer.push_back(regs[10]);
    answer.push_back(regs[18]);
    answer.push_back(regs[26]);
    answer.push_back(regs[34]);
    answer.push_back(regs[39]);
    answer.push_back(regs[44]);
    answer.push_back(regs[52]);
    answer.push_back(regs[57]);
    answer.push_back(regs[62]);
    return answer;
}
    