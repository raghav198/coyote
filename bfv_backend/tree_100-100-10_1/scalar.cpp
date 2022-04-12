
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 65;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"357", "284", "154", "552", "292", "167", "503", "242", "623", "519", "313", "211", "108", "200", "467", "909", "752", "307", "984", "320", "591", "327", "259", "548", "348", "301", "142", "843", "535", "152", "753", "776", "247", "998", "628", "130", "737", "687", "842", "433", "476", "640", "1013", "330", "447", "855", "30", "918", "854", "241", "312", "485", "816", "140", "893", "963", "190", "169", "299", "481", "163", "1017", "314", "633", "790", "74"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["503"], locs["307"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(regs[0], locs["284"], regs[1]);
    info.eval->add(locs["591"], locs["152"], regs[2]);
    info.eval->multiply(locs["535"], locs["163"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->multiply(locs["108"], locs["320"], regs[4]);
    info.eval->relinearize_inplace(regs[4], rk);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->multiply(locs["74"], locs["140"], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(locs["687"], regs[6], regs[7]);
    info.eval->multiply(regs[5], regs[7], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->multiply(regs[2], regs[8], regs[9]);
    info.eval->relinearize_inplace(regs[9], rk);
    info.eval->add(locs["292"], locs["330"], regs[10]);
    info.eval->multiply(locs["327"], locs["816"], regs[11]);
    info.eval->relinearize_inplace(regs[11], rk);
    info.eval->add(regs[10], regs[11], regs[12]);
    info.eval->add(regs[12], locs["348"], regs[13]);
    info.eval->add(regs[13], locs["633"], regs[14]);
    info.eval->multiply(regs[9], regs[14], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->add(locs["628"], locs["241"], regs[16]);
    info.eval->multiply(regs[16], locs["433"], regs[17]);
    info.eval->relinearize_inplace(regs[17], rk);
    info.eval->add(regs[17], locs["623"], regs[18]);
    info.eval->multiply(regs[15], regs[18], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->multiply(locs["200"], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->multiply(regs[20], locs["30"], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->multiply(regs[1], regs[21], regs[22]);
    info.eval->relinearize_inplace(regs[22], rk);
    info.eval->add(locs["918"], locs["776"], regs[23]);
    info.eval->multiply(locs["242"], locs["211"], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->multiply(regs[23], regs[24], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->multiply(locs["259"], locs["963"], regs[26]);
    info.eval->relinearize_inplace(regs[26], rk);
    info.eval->multiply(locs["1017"], locs["790"], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[26], regs[27], regs[28]);
    info.eval->add(locs["299"], locs["1013"], regs[29]);
    info.eval->add(locs["154"], regs[29], regs[30]);
    info.eval->add(regs[28], regs[30], regs[31]);
    info.eval->add(locs["640"], locs["312"], regs[32]);
    info.eval->add(regs[32], locs["447"], regs[33]);
    info.eval->multiply(locs["130"], locs["476"], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->add(regs[34], locs["909"], regs[35]);
    info.eval->add(regs[33], regs[35], regs[36]);
    info.eval->multiply(regs[31], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->add(regs[25], regs[37], regs[38]);
    info.eval->multiply(regs[38], locs["301"], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->add(regs[39], locs["142"], regs[40]);
    info.eval->multiply(locs["314"], locs["467"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->add(locs["854"], regs[41], regs[42]);
    info.eval->multiply(regs[42], locs["843"], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->multiply(locs["842"], locs["519"], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->add(locs["481"], regs[44], regs[45]);
    info.eval->multiply(locs["485"], locs["548"], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->multiply(locs["984"], locs["737"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->multiply(regs[46], regs[47], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->add(regs[45], regs[48], regs[49]);
    info.eval->multiply(locs["893"], locs["190"], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->multiply(locs["169"], locs["167"], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->add(regs[51], locs["552"], regs[52]);
    info.eval->multiply(regs[50], regs[52], regs[53]);
    info.eval->relinearize_inplace(regs[53], rk);
    info.eval->add(regs[49], regs[53], regs[54]);
    info.eval->add(locs["313"], locs["752"], regs[55]);
    info.eval->add(locs["855"], regs[55], regs[56]);
    info.eval->add(locs["247"], regs[56], regs[57]);
    info.eval->add(locs["998"], regs[57], regs[58]);
    info.eval->multiply(regs[54], regs[58], regs[59]);
    info.eval->relinearize_inplace(regs[59], rk);
    info.eval->multiply(regs[43], regs[59], regs[60]);
    info.eval->relinearize_inplace(regs[60], rk);
    info.eval->multiply(regs[60], locs["753"], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    info.eval->add(regs[40], regs[61], regs[62]);
    info.eval->multiply(regs[62], locs["357"], regs[63]);
    info.eval->relinearize_inplace(regs[63], rk);
    info.eval->multiply(regs[22], regs[63], regs[64]);
    info.eval->relinearize_inplace(regs[64], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[64]);
    return answer;
}
    