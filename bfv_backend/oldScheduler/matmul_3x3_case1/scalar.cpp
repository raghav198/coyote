
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"matmul_3x3_case1(c):11", "matmul_3x3_case1(c):6", "matmul_3x3_case1(c):7", "matmul_3x3_case1(c):16", "matmul_3x3_case1(c):4", "matmul_3x3_case1(c):12", "matmul_3x3_case1(c):14", "matmul_3x3_case1(c):5", "matmul_3x3_case1(c):9", "matmul_3x3_case1(c):13", "matmul_3x3_case1(c):3", "matmul_3x3_case1(c):8", "matmul_3x3_case1(c):15", "matmul_3x3_case1(c):1", "matmul_3x3_case1(c):17", "matmul_3x3_case1(c):0", "matmul_3x3_case1(c):2", "matmul_3x3_case1(c):10"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["matmul_3x3_case1(c):0"];
    regs[1] = locs["matmul_3x3_case1(c):9"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["matmul_3x3_case1(c):1"];
    regs[4] = locs["matmul_3x3_case1(c):12"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    regs[6] = locs["matmul_3x3_case1(c):2"];
    regs[7] = locs["matmul_3x3_case1(c):15"];
    info.eval->multiply(regs[6], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[5], regs[8], regs[9]);
    info.eval->add(regs[2], regs[9], regs[10]);
    regs[11] = locs["matmul_3x3_case1(c):10"];
    info.eval->multiply(regs[0], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    regs[13] = locs["matmul_3x3_case1(c):13"];
    info.eval->multiply(regs[3], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    regs[15] = locs["matmul_3x3_case1(c):16"];
    info.eval->multiply(regs[6], regs[15], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[14], regs[16], regs[17]);
    info.eval->add(regs[12], regs[17], regs[18]);
    regs[19] = locs["matmul_3x3_case1(c):11"];
    info.eval->multiply(regs[0], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    regs[21] = locs["matmul_3x3_case1(c):14"];
    info.eval->multiply(regs[3], regs[21], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    regs[23] = locs["matmul_3x3_case1(c):17"];
    info.eval->multiply(regs[6], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->add(regs[22], regs[24], regs[25]);
    info.eval->add(regs[20], regs[25], regs[26]);
    regs[27] = locs["matmul_3x3_case1(c):3"];
    info.eval->multiply(regs[27], regs[1], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    regs[29] = locs["matmul_3x3_case1(c):4"];
    info.eval->multiply(regs[29], regs[4], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    regs[31] = locs["matmul_3x3_case1(c):5"];
    info.eval->multiply(regs[31], regs[7], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->add(regs[30], regs[32], regs[33]);
    info.eval->add(regs[28], regs[33], regs[34]);
    info.eval->multiply(regs[27], regs[11], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->multiply(regs[29], regs[13], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->multiply(regs[31], regs[15], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->add(regs[36], regs[37], regs[38]);
    info.eval->add(regs[35], regs[38], regs[39]);
    info.eval->multiply(regs[27], regs[19], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->multiply(regs[29], regs[21], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->multiply(regs[31], regs[23], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->add(regs[41], regs[42], regs[43]);
    info.eval->add(regs[40], regs[43], regs[44]);
    regs[45] = locs["matmul_3x3_case1(c):6"];
    info.eval->multiply(regs[45], regs[1], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    regs[47] = locs["matmul_3x3_case1(c):7"];
    info.eval->multiply(regs[47], regs[4], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    regs[49] = locs["matmul_3x3_case1(c):8"];
    info.eval->multiply(regs[49], regs[7], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->add(regs[48], regs[50], regs[51]);
    info.eval->add(regs[46], regs[51], regs[52]);
    info.eval->multiply(regs[45], regs[11], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->multiply(regs[47], regs[13], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->multiply(regs[49], regs[15], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->add(regs[54], regs[55], regs[56]);
    info.eval->add(regs[53], regs[56], regs[57]);
    info.eval->multiply(regs[45], regs[19], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->multiply(regs[47], regs[21], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->multiply(regs[49], regs[23], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    info.eval->add(regs[59], regs[60], regs[61]);
    info.eval->add(regs[58], regs[61], regs[62]);
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
    