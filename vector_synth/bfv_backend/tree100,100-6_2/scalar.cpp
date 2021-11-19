
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"19", "833", "884", "949", "739", "885", "441", "571", "410", "10", "232", "527", "627", "496", "774", "502", "733", "497", "283", "450", "278", "157", "678", "794", "143", "853", "201", "73", "144", "190", "878", "211", "521", "456", "548", "505", "764", "801", "536", "766", "950", "384", "264", "741", "343", "680", "1020", "827", "137", "252", "681", "792", "163", "936", "943", "59", "1012", "471", "633", "175", "890", "861", "31", "345"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["521"], locs["681"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->multiply(locs["19"], locs["252"], regs[1]);
    info.eval->relinearize_inplace(regs[1], rk);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->multiply(locs["943"], locs["232"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["680"], locs["733"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->multiply(locs["211"], locs["833"], regs[7]);
    info.eval->relinearize_inplace(regs[7], rk);
    info.eval->multiply(locs["950"], locs["163"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(regs[7], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->multiply(locs["505"], locs["31"], regs[10]);
    info.eval->relinearize_inplace(regs[10], rk);
    info.eval->multiply(locs["861"], locs["527"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->multiply(regs[9], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->multiply(regs[6], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(locs["201"], locs["536"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(locs["143"], locs["410"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->multiply(regs[15], regs[16], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->multiply(locs["264"], locs["190"], regs[18]);
    info.eval->relinearize_inplace(regs[18], rk);
    info.eval->multiply(locs["764"], locs["884"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->multiply(regs[18], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->multiply(regs[17], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->multiply(locs["175"], locs["441"], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->multiply(locs["885"], locs["936"], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->multiply(locs["1020"], locs["633"], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->multiply(locs["949"], locs["497"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->multiply(regs[24], regs[27], regs[28]);
    info.eval->relinearize_inplace(regs[28], rk);
    info.eval->multiply(regs[21], regs[28], regs[29]);
    info.eval->relinearize_inplace(regs[29], rk);
    info.eval->multiply(regs[14], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->multiply(locs["345"], locs["571"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->multiply(locs["502"], locs["678"], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->multiply(locs["801"], locs["157"], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->multiply(locs["1012"], locs["343"], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->multiply(regs[34], regs[35], regs[36]);
    info.eval->relinearize_inplace(regs[36], rk);
    info.eval->multiply(regs[33], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->multiply(locs["741"], locs["144"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->multiply(locs["456"], locs["774"], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->multiply(regs[38], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->multiply(locs["739"], locs["627"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->multiply(locs["548"], locs["59"], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->multiply(regs[40], regs[43], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->multiply(regs[37], regs[44], regs[45]);
    info.eval->relinearize_inplace(regs[45], rk);
    info.eval->multiply(locs["471"], locs["878"], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->multiply(locs["853"], locs["278"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->multiply(regs[46], regs[47], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->multiply(locs["794"], locs["10"], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->multiply(locs["384"], locs["827"], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->multiply(regs[49], regs[50], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->multiply(regs[48], regs[51], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->multiply(locs["73"], locs["283"], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->multiply(locs["766"], locs["890"], regs[54]);
    info.eval->relinearize_inplace(regs[54], rk);
    info.eval->multiply(regs[53], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->multiply(locs["792"], locs["137"], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->multiply(locs["450"], locs["496"], regs[57]);
    info.eval->relinearize_inplace(regs[57], rk);
    info.eval->multiply(regs[56], regs[57], regs[58]);
    info.eval->relinearize_inplace(regs[58], rk);
    info.eval->multiply(regs[55], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->multiply(regs[52], regs[59], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    info.eval->multiply(regs[45], regs[60], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    info.eval->multiply(regs[30], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    