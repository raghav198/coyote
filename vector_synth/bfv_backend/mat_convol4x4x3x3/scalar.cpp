
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 120;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"a:2,0", "b:0,1", "a:3,3", "a:3,2", "b:1,0", "a:0,1", "a:1,0", "a:2,1", "a:2,3", "b:2,2", "a:0,0", "b:2,0", "a:2,2", "a:3,0", "b:0,0", "b:2,1", "a:1,2", "a:1,3", "b:1,1", "a:3,1", "b:0,2", "b:1,2", "a:0,2", "a:1,1", "a:0,3"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    regs[0] = locs["b:0,0"];
    regs[1] = locs["a:0,0"];
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    regs[3] = locs["b:0,1"];
    regs[4] = locs["a:0,1"];
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    regs[7] = locs["b:0,2"];
    regs[8] = locs["a:0,2"];
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(regs[6], regs[9], regs[10]);
    regs[11] = locs["b:1,0"];
    regs[12] = locs["a:1,0"];
    info.eval->multiply(regs[11], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->add(regs[10], regs[13], regs[14]);
    regs[15] = locs["b:1,1"];
    regs[16] = locs["a:1,1"];
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->add(regs[14], regs[17], regs[18]);
    regs[19] = locs["b:1,2"];
    regs[20] = locs["a:1,2"];
    info.eval->multiply(regs[19], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->add(regs[18], regs[21], regs[22]);
    regs[23] = locs["b:2,0"];
    regs[24] = locs["a:2,0"];
    info.eval->multiply(regs[23], regs[24], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(regs[22], regs[25], regs[26]);
    regs[27] = locs["b:2,1"];
    regs[28] = locs["a:2,1"];
    info.eval->multiply(regs[27], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->add(regs[26], regs[29], regs[30]);
    regs[31] = locs["b:2,2"];
    regs[32] = locs["a:2,2"];
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(regs[30], regs[33], regs[34]);
    regs[35] = locs["b:0,0"];
    info.eval->multiply(regs[35], regs[4], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    regs[37] = locs["b:0,1"];
    info.eval->multiply(regs[37], regs[8], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->add(regs[36], regs[38], regs[39]);
    regs[40] = locs["b:0,2"];
    regs[41] = locs["a:0,3"];
    info.eval->multiply(regs[40], regs[41], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->add(regs[39], regs[42], regs[43]);
    regs[44] = locs["b:1,0"];
    info.eval->multiply(regs[44], regs[16], regs[45]);
    info.eval->relinearize_inplace(regs[45], rk);
    info.eval->add(regs[43], regs[45], regs[46]);
    regs[47] = locs["b:1,1"];
    info.eval->multiply(regs[47], regs[20], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->add(regs[46], regs[48], regs[49]);
    regs[50] = locs["b:1,2"];
    regs[51] = locs["a:1,3"];
    info.eval->multiply(regs[50], regs[51], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->add(regs[49], regs[52], regs[53]);
    regs[54] = locs["b:2,0"];
    info.eval->multiply(regs[54], regs[28], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->add(regs[53], regs[55], regs[56]);
    regs[57] = locs["b:2,1"];
    info.eval->multiply(regs[57], regs[32], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->add(regs[56], regs[58], regs[59]);
    regs[60] = locs["b:2,2"];
    regs[61] = locs["a:2,3"];
    info.eval->multiply(regs[60], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    info.eval->add(regs[59], regs[62], regs[63]);
    regs[64] = locs["b:0,0"];
    info.eval->multiply(regs[64], regs[12], regs[65]);
    info.eval->relinearize_inplace(regs[65], rk);
    regs[66] = locs["b:0,1"];
    info.eval->multiply(regs[66], regs[16], regs[67]);
    info.eval->relinearize_inplace(regs[67], rk);
    info.eval->add(regs[65], regs[67], regs[68]);
    regs[69] = locs["b:0,2"];
    info.eval->multiply(regs[69], regs[20], regs[70]);
    info.eval->relinearize_inplace(regs[70], rk);
    info.eval->add(regs[68], regs[70], regs[71]);
    regs[72] = locs["b:1,0"];
    info.eval->multiply(regs[72], regs[24], regs[73]);
    info.eval->relinearize_inplace(regs[73], rk);
    info.eval->add(regs[71], regs[73], regs[74]);
    regs[75] = locs["b:1,1"];
    info.eval->multiply(regs[75], regs[28], regs[76]);
    info.eval->relinearize_inplace(regs[76], rk);
    info.eval->add(regs[74], regs[76], regs[77]);
    regs[78] = locs["b:1,2"];
    info.eval->multiply(regs[78], regs[32], regs[79]);
    info.eval->relinearize_inplace(regs[79], rk);
    info.eval->add(regs[77], regs[79], regs[80]);
    regs[81] = locs["b:2,0"];
    regs[82] = locs["a:3,0"];
    info.eval->multiply(regs[81], regs[82], regs[83]);
    info.eval->relinearize_inplace(regs[83], rk);
    info.eval->add(regs[80], regs[83], regs[84]);
    regs[85] = locs["b:2,1"];
    regs[86] = locs["a:3,1"];
    info.eval->multiply(regs[85], regs[86], regs[87]);
    info.eval->relinearize_inplace(regs[87], rk);
    info.eval->add(regs[84], regs[87], regs[88]);
    regs[89] = locs["b:2,2"];
    regs[90] = locs["a:3,2"];
    info.eval->multiply(regs[89], regs[90], regs[91]);
    info.eval->relinearize_inplace(regs[91], rk);
    info.eval->add(regs[88], regs[91], regs[92]);
    regs[93] = locs["b:0,0"];
    info.eval->multiply(regs[93], regs[16], regs[94]);
    info.eval->relinearize_inplace(regs[94], rk);
    regs[95] = locs["b:0,1"];
    info.eval->multiply(regs[95], regs[20], regs[96]);
    info.eval->relinearize_inplace(regs[96], rk);
    info.eval->add(regs[94], regs[96], regs[97]);
    regs[98] = locs["b:0,2"];
    info.eval->multiply(regs[98], regs[51], regs[99]);
    info.eval->relinearize_inplace(regs[99], rk);
    info.eval->add(regs[97], regs[99], regs[100]);
    regs[101] = locs["b:1,0"];
    info.eval->multiply(regs[101], regs[28], regs[102]);
    info.eval->relinearize_inplace(regs[102], rk);
    info.eval->add(regs[100], regs[102], regs[103]);
    regs[104] = locs["b:1,1"];
    info.eval->multiply(regs[104], regs[32], regs[105]);
    info.eval->relinearize_inplace(regs[105], rk);
    info.eval->add(regs[103], regs[105], regs[106]);
    regs[107] = locs["b:1,2"];
    info.eval->multiply(regs[107], regs[61], regs[108]);
    info.eval->relinearize_inplace(regs[108], rk);
    info.eval->add(regs[106], regs[108], regs[109]);
    regs[110] = locs["b:2,0"];
    info.eval->multiply(regs[110], regs[86], regs[111]);
    info.eval->relinearize_inplace(regs[111], rk);
    info.eval->add(regs[109], regs[111], regs[112]);
    regs[113] = locs["b:2,1"];
    info.eval->multiply(regs[113], regs[90], regs[114]);
    info.eval->relinearize_inplace(regs[114], rk);
    info.eval->add(regs[112], regs[114], regs[115]);
    regs[116] = locs["b:2,2"];
    regs[117] = locs["a:3,3"];
    info.eval->multiply(regs[116], regs[117], regs[118]);
    info.eval->relinearize_inplace(regs[118], rk);
    info.eval->add(regs[115], regs[118], regs[119]);
    std::vector<ctxt> answer;
    answer.push_back(regs[34]);
    answer.push_back(regs[63]);
    answer.push_back(regs[92]);
    answer.push_back(regs[119]);
    return answer;
}
    