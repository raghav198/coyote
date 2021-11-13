
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 146;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"b:2,0", "a:0,0", "a:1,0", "b:0,1", "a:0,1", "a:1,2", "b:0,0", "a:2,0", "a:2,1", "b:0,2", "b:2,2", "a:2,2", "b:2,1", "a:1,1", "a:0,2", "b:1,2", "b:1,1", "b:1,0"};
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
    regs[10] = locs["a:1,0"];
    regs[11] = locs["b:0,1"];
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    regs[13] = locs["a:1,1"];
    regs[14] = locs["b:1,1"];
    info.eval->multiply(regs[13], regs[14], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(regs[12], regs[15], regs[16]);
    regs[17] = locs["a:1,2"];
    info.eval->multiply(regs[17], locs["b:2,1"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->add(regs[16], regs[18], regs[19]);
    regs[20] = locs["b:0,2"];
    info.eval->multiply(locs["a:2,0"], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    regs[22] = locs["b:1,2"];
    info.eval->multiply(locs["a:2,1"], regs[22], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->add(regs[21], regs[23], regs[24]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,2"], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(regs[24], regs[25], regs[26]);
    info.eval->multiply(regs[19], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    regs[28] = locs["b:0,1"];
    info.eval->multiply(locs["a:2,0"], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    regs[30] = locs["b:1,1"];
    info.eval->multiply(locs["a:2,1"], regs[30], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->add(regs[29], regs[31], regs[32]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,1"], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->add(regs[32], regs[33], regs[34]);
    regs[35] = locs["a:1,0"];
    regs[36] = locs["b:0,2"];
    info.eval->multiply(regs[35], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    regs[38] = locs["a:1,1"];
    regs[39] = locs["b:1,2"];
    info.eval->multiply(regs[38], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->add(regs[37], regs[40], regs[41]);
    regs[42] = locs["a:1,2"];
    info.eval->multiply(regs[42], locs["b:2,2"], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->add(regs[41], regs[43], regs[44]);
    info.eval->multiply(regs[34], regs[44], regs[45]);
    info.eval->relinearize_inplace(regs[45], rk);
    info.eval->add(regs[27], regs[45], regs[46]);
    info.eval->multiply(regs[9], regs[46], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    regs[48] = locs["a:0,0"];
    regs[49] = locs["b:0,1"];
    info.eval->multiply(regs[48], regs[49], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    regs[51] = locs["a:0,1"];
    regs[52] = locs["b:1,1"];
    info.eval->multiply(regs[51], regs[52], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->add(regs[50], regs[53], regs[54]);
    regs[55] = locs["a:0,2"];
    info.eval->multiply(regs[55], locs["b:2,1"], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->add(regs[54], regs[56], regs[57]);
    regs[58] = locs["a:1,0"];
    regs[59] = locs["b:0,0"];
    info.eval->multiply(regs[58], regs[59], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    regs[61] = locs["a:1,1"];
    regs[62] = locs["b:1,0"];
    info.eval->multiply(regs[61], regs[62], regs[63]);
    info.eval->relinearize_inplace(regs[63], rk);
    info.eval->add(regs[60], regs[63], regs[64]);
    regs[65] = locs["a:1,2"];
    info.eval->multiply(regs[65], locs["b:2,0"], regs[66]);
    info.eval->relinearize_inplace(regs[66], rk);
    info.eval->add(regs[64], regs[66], regs[67]);
    regs[68] = locs["b:0,2"];
    info.eval->multiply(locs["a:2,0"], regs[68], regs[69]);
    info.eval->relinearize_inplace(regs[69], rk);
    regs[70] = locs["b:1,2"];
    info.eval->multiply(locs["a:2,1"], regs[70], regs[71]);
    info.eval->relinearize_inplace(regs[71], rk);
    info.eval->add(regs[69], regs[71], regs[72]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,2"], regs[73]);
    info.eval->relinearize_inplace(regs[73], rk);
    info.eval->add(regs[72], regs[73], regs[74]);
    info.eval->multiply(regs[67], regs[74], regs[75]);
    info.eval->relinearize_inplace(regs[75], rk);
    regs[76] = locs["b:0,0"];
    info.eval->multiply(locs["a:2,0"], regs[76], regs[77]);
    info.eval->relinearize_inplace(regs[77], rk);
    regs[78] = locs["b:1,0"];
    info.eval->multiply(locs["a:2,1"], regs[78], regs[79]);
    info.eval->relinearize_inplace(regs[79], rk);
    info.eval->add(regs[77], regs[79], regs[80]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,0"], regs[81]);
    info.eval->relinearize_inplace(regs[81], rk);
    info.eval->add(regs[80], regs[81], regs[82]);
    regs[83] = locs["a:1,0"];
    regs[84] = locs["b:0,2"];
    info.eval->multiply(regs[83], regs[84], regs[85]);
    info.eval->relinearize_inplace(regs[85], rk);
    regs[86] = locs["a:1,1"];
    regs[87] = locs["b:1,2"];
    info.eval->multiply(regs[86], regs[87], regs[88]);
    info.eval->relinearize_inplace(regs[88], rk);
    info.eval->add(regs[85], regs[88], regs[89]);
    regs[90] = locs["a:1,2"];
    info.eval->multiply(regs[90], locs["b:2,2"], regs[91]);
    info.eval->relinearize_inplace(regs[91], rk);
    info.eval->add(regs[89], regs[91], regs[92]);
    info.eval->multiply(regs[82], regs[92], regs[93]);
    info.eval->relinearize_inplace(regs[93], rk);
    info.eval->add(regs[75], regs[93], regs[94]);
    info.eval->multiply(regs[57], regs[94], regs[95]);
    info.eval->relinearize_inplace(regs[95], rk);
    info.eval->sub(regs[47], regs[95], regs[96]);
    regs[97] = locs["a:0,0"];
    regs[98] = locs["b:0,2"];
    info.eval->multiply(regs[97], regs[98], regs[99]);
    info.eval->relinearize_inplace(regs[99], rk);
    regs[100] = locs["a:0,1"];
    regs[101] = locs["b:1,2"];
    info.eval->multiply(regs[100], regs[101], regs[102]);
    info.eval->relinearize_inplace(regs[102], rk);
    info.eval->add(regs[99], regs[102], regs[103]);
    regs[104] = locs["a:0,2"];
    info.eval->multiply(regs[104], locs["b:2,2"], regs[105]);
    info.eval->relinearize_inplace(regs[105], rk);
    info.eval->add(regs[103], regs[105], regs[106]);
    regs[107] = locs["a:1,0"];
    regs[108] = locs["b:0,0"];
    info.eval->multiply(regs[107], regs[108], regs[109]);
    info.eval->relinearize_inplace(regs[109], rk);
    regs[110] = locs["a:1,1"];
    regs[111] = locs["b:1,0"];
    info.eval->multiply(regs[110], regs[111], regs[112]);
    info.eval->relinearize_inplace(regs[112], rk);
    info.eval->add(regs[109], regs[112], regs[113]);
    regs[114] = locs["a:1,2"];
    info.eval->multiply(regs[114], locs["b:2,0"], regs[115]);
    info.eval->relinearize_inplace(regs[115], rk);
    info.eval->add(regs[113], regs[115], regs[116]);
    regs[117] = locs["b:0,1"];
    info.eval->multiply(locs["a:2,0"], regs[117], regs[118]);
    info.eval->relinearize_inplace(regs[118], rk);
    regs[119] = locs["b:1,1"];
    info.eval->multiply(locs["a:2,1"], regs[119], regs[120]);
    info.eval->relinearize_inplace(regs[120], rk);
    info.eval->add(regs[118], regs[120], regs[121]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,1"], regs[122]);
    info.eval->relinearize_inplace(regs[122], rk);
    info.eval->add(regs[121], regs[122], regs[123]);
    info.eval->multiply(regs[116], regs[123], regs[124]);
    info.eval->relinearize_inplace(regs[124], rk);
    regs[125] = locs["b:0,0"];
    info.eval->multiply(locs["a:2,0"], regs[125], regs[126]);
    info.eval->relinearize_inplace(regs[126], rk);
    regs[127] = locs["b:1,0"];
    info.eval->multiply(locs["a:2,1"], regs[127], regs[128]);
    info.eval->relinearize_inplace(regs[128], rk);
    info.eval->add(regs[126], regs[128], regs[129]);
    info.eval->multiply(locs["a:2,2"], locs["b:2,0"], regs[130]);
    info.eval->relinearize_inplace(regs[130], rk);
    info.eval->add(regs[129], regs[130], regs[131]);
    regs[132] = locs["a:1,0"];
    regs[133] = locs["b:0,1"];
    info.eval->multiply(regs[132], regs[133], regs[134]);
    info.eval->relinearize_inplace(regs[134], rk);
    regs[135] = locs["a:1,1"];
    regs[136] = locs["b:1,1"];
    info.eval->multiply(regs[135], regs[136], regs[137]);
    info.eval->relinearize_inplace(regs[137], rk);
    info.eval->add(regs[134], regs[137], regs[138]);
    regs[139] = locs["a:1,2"];
    info.eval->multiply(regs[139], locs["b:2,1"], regs[140]);
    info.eval->relinearize_inplace(regs[140], rk);
    info.eval->add(regs[138], regs[140], regs[141]);
    info.eval->multiply(regs[131], regs[141], regs[142]);
    info.eval->relinearize_inplace(regs[142], rk);
    info.eval->add(regs[124], regs[142], regs[143]);
    info.eval->multiply(regs[106], regs[143], regs[144]);
    info.eval->relinearize_inplace(regs[144], rk);
    info.eval->add(regs[96], regs[144], regs[145]);
    std::vector<ctxt> answer;
    answer.push_back(regs[145]);
    return answer;
}
    