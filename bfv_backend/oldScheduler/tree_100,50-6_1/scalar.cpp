
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"69", "400", "825", "927", "967", "30", "56", "742", "711", "178", "718", "640", "694", "733", "35", "591", "910", "198", "88", "539", "788", "811", "290", "501", "751", "971", "389", "781", "573", "470", "340", "828", "794", "935", "665", "619", "893", "896", "7", "95", "762", "517", "1015", "228", "344", "861", "817", "834", "194", "471", "130", "222", "442", "755", "45", "804", "940", "361", "386", "103", "252", "890", "498"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->add(locs["30"], locs["861"], regs[0]);
    info.eval->add(locs["711"], locs["228"], regs[1]);
    info.eval->multiply(regs[0], regs[1], regs[2]);
    info.eval->relinearize_inplace(regs[2], rk);
    info.eval->add(locs["781"], locs["893"], regs[3]);
    info.eval->add(locs["103"], locs["194"], regs[4]);
    info.eval->add(regs[3], regs[4], regs[5]);
    info.eval->multiply(regs[2], regs[5], regs[6]);
    info.eval->relinearize_inplace(regs[6], rk);
    info.eval->add(locs["389"], locs["442"], regs[7]);
    info.eval->multiply(locs["619"], locs["781"], regs[8]);
    info.eval->relinearize_inplace(regs[8], rk);
    info.eval->add(regs[7], regs[8], regs[9]);
    info.eval->add(locs["640"], locs["927"], regs[10]);
    info.eval->add(locs["971"], locs["694"], regs[11]);
    info.eval->multiply(regs[10], regs[11], regs[12]);
    info.eval->relinearize_inplace(regs[12], rk);
    info.eval->add(regs[9], regs[12], regs[13]);
    info.eval->multiply(regs[6], regs[13], regs[14]);
    info.eval->relinearize_inplace(regs[14], rk);
    info.eval->multiply(locs["361"], locs["828"], regs[15]);
    info.eval->relinearize_inplace(regs[15], rk);
    info.eval->multiply(locs["733"], locs["751"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[15], regs[16], regs[17]);
    info.eval->add(locs["45"], locs["935"], regs[18]);
    info.eval->multiply(locs["501"], locs["794"], regs[19]);
    info.eval->relinearize_inplace(regs[19], rk);
    info.eval->add(regs[18], regs[19], regs[20]);
    info.eval->multiply(regs[17], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->add(locs["56"], locs["517"], regs[22]);
    info.eval->add(locs["890"], locs["940"], regs[23]);
    info.eval->multiply(regs[22], regs[23], regs[24]);
    info.eval->relinearize_inplace(regs[24], rk);
    info.eval->multiply(locs["252"], locs["498"], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(locs["573"], locs["69"], regs[26]);
    info.eval->multiply(regs[25], regs[26], regs[27]);
    info.eval->relinearize_inplace(regs[27], rk);
    info.eval->add(regs[24], regs[27], regs[28]);
    info.eval->add(regs[21], regs[28], regs[29]);
    info.eval->multiply(regs[14], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->add(locs["755"], locs["7"], regs[31]);
    info.eval->multiply(locs["834"], locs["95"], regs[32]);
    info.eval->relinearize_inplace(regs[32], rk);
    info.eval->multiply(regs[31], regs[32], regs[33]);
    info.eval->relinearize_inplace(regs[33], rk);
    info.eval->multiply(locs["817"], locs["591"], regs[34]);
    info.eval->relinearize_inplace(regs[34], rk);
    info.eval->multiply(locs["742"], locs["825"], regs[35]);
    info.eval->relinearize_inplace(regs[35], rk);
    info.eval->add(regs[34], regs[35], regs[36]);
    info.eval->add(regs[33], regs[36], regs[37]);
    info.eval->add(locs["400"], locs["910"], regs[38]);
    info.eval->multiply(locs["896"], locs["471"], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->multiply(regs[38], regs[39], regs[40]);
    info.eval->relinearize_inplace(regs[40], rk);
    info.eval->multiply(locs["178"], locs["130"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->multiply(locs["386"], locs["222"], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->multiply(regs[40], regs[43], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->add(regs[37], regs[44], regs[45]);
    info.eval->add(locs["718"], locs["967"], regs[46]);
    info.eval->multiply(locs["340"], locs["290"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->multiply(regs[46], regs[47], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->multiply(locs["198"], locs["35"], regs[49]);
    info.eval->relinearize_inplace(regs[49], rk);
    info.eval->multiply(locs["811"], locs["1015"], regs[50]);
    info.eval->relinearize_inplace(regs[50], rk);
    info.eval->multiply(regs[49], regs[50], regs[51]);
    info.eval->relinearize_inplace(regs[51], rk);
    info.eval->add(regs[48], regs[51], regs[52]);
    info.eval->add(locs["470"], locs["804"], regs[53]);
    info.eval->add(locs["88"], locs["788"], regs[54]);
    info.eval->multiply(regs[53], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->multiply(locs["762"], locs["344"], regs[56]);
    info.eval->relinearize_inplace(regs[56], rk);
    info.eval->add(locs["539"], locs["665"], regs[57]);
    info.eval->add(regs[56], regs[57], regs[58]);
    info.eval->add(regs[55], regs[58], regs[59]);
    info.eval->add(regs[52], regs[59], regs[60]);
    info.eval->multiply(regs[45], regs[60], regs[61]);
    info.eval->relinearize_inplace(regs[61], rk);
    info.eval->multiply(regs[30], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    