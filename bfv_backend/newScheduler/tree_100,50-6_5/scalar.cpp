
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{
    return 63;
}

std::vector<std::string> ScalarProgram::vars_used()
{
    return {"1008", "450", "498", "470", "205", "286", "997", "936", "409", "893", "576", "804", "53", "793", "114", "35", "309", "400", "130", "494", "67", "976", "153", "935", "577", "116", "981", "950", "519", "284", "361", "995", "910", "821", "517", "752", "736", "93", "1012", "389", "344", "847", "909", "442", "546", "718", "56", "437", "445", "591", "657", "452", "854", "526", "137", "692", "282", "390", "150", "927", "731", "742", "233"};
}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    info.eval->multiply(locs["1012"], locs["657"], regs[0]);
    info.eval->relinearize_inplace(regs[0], rk);
    info.eval->add(locs["893"], locs["731"], regs[1]);
    info.eval->add(regs[0], regs[1], regs[2]);
    info.eval->multiply(locs["981"], locs["1008"], regs[3]);
    info.eval->relinearize_inplace(regs[3], rk);
    info.eval->add(locs["389"], locs["442"], regs[4]);
    info.eval->multiply(regs[3], regs[4], regs[5]);
    info.eval->relinearize_inplace(regs[5], rk);
    info.eval->add(regs[2], regs[5], regs[6]);
    info.eval->add(locs["409"], locs["995"], regs[7]);
    info.eval->add(locs["927"], locs["736"], regs[8]);
    info.eval->add(regs[7], regs[8], regs[9]);
    info.eval->add(locs["752"], locs["437"], regs[10]);
    info.eval->add(locs["205"], locs["361"], regs[11]);
    info.eval->add(regs[10], regs[11], regs[12]);
    info.eval->multiply(regs[9], regs[12], regs[13]);
    info.eval->relinearize_inplace(regs[13], rk);
    info.eval->add(regs[6], regs[13], regs[14]);
    info.eval->add(locs["821"], locs["519"], regs[15]);
    info.eval->multiply(locs["935"], locs["286"], regs[16]);
    info.eval->relinearize_inplace(regs[16], rk);
    info.eval->add(regs[15], regs[16], regs[17]);
    info.eval->add(locs["976"], locs["445"], regs[18]);
    info.eval->add(locs["56"], locs["517"], regs[19]);
    info.eval->multiply(regs[18], regs[19], regs[20]);
    info.eval->relinearize_inplace(regs[20], rk);
    info.eval->multiply(regs[17], regs[20], regs[21]);
    info.eval->relinearize_inplace(regs[21], rk);
    info.eval->add(locs["470"], locs["116"], regs[22]);
    info.eval->multiply(locs["498"], locs["950"], regs[23]);
    info.eval->relinearize_inplace(regs[23], rk);
    info.eval->add(regs[22], regs[23], regs[24]);
    info.eval->multiply(locs["309"], locs["546"], regs[25]);
    info.eval->relinearize_inplace(regs[25], rk);
    info.eval->add(locs["153"], locs["997"], regs[26]);
    info.eval->add(regs[25], regs[26], regs[27]);
    info.eval->add(regs[24], regs[27], regs[28]);
    info.eval->add(regs[21], regs[28], regs[29]);
    info.eval->multiply(regs[14], regs[29], regs[30]);
    info.eval->relinearize_inplace(regs[30], rk);
    info.eval->multiply(locs["936"], locs["67"], regs[31]);
    info.eval->relinearize_inplace(regs[31], rk);
    info.eval->add(locs["591"], locs["233"], regs[32]);
    info.eval->add(regs[31], regs[32], regs[33]);
    info.eval->add(locs["137"], locs["390"], regs[34]);
    info.eval->add(locs["400"], locs["910"], regs[35]);
    info.eval->add(regs[34], regs[35], regs[36]);
    info.eval->multiply(regs[33], regs[36], regs[37]);
    info.eval->relinearize_inplace(regs[37], rk);
    info.eval->multiply(locs["282"], locs["284"], regs[38]);
    info.eval->relinearize_inplace(regs[38], rk);
    info.eval->multiply(locs["130"], locs["53"], regs[39]);
    info.eval->relinearize_inplace(regs[39], rk);
    info.eval->add(regs[38], regs[39], regs[40]);
    info.eval->multiply(locs["793"], locs["577"], regs[41]);
    info.eval->relinearize_inplace(regs[41], rk);
    info.eval->multiply(locs["909"], locs["718"], regs[42]);
    info.eval->relinearize_inplace(regs[42], rk);
    info.eval->multiply(regs[41], regs[42], regs[43]);
    info.eval->relinearize_inplace(regs[43], rk);
    info.eval->multiply(regs[40], regs[43], regs[44]);
    info.eval->relinearize_inplace(regs[44], rk);
    info.eval->multiply(regs[37], regs[44], regs[45]);
    info.eval->relinearize_inplace(regs[45], rk);
    info.eval->multiply(locs["114"], locs["452"], regs[46]);
    info.eval->relinearize_inplace(regs[46], rk);
    info.eval->multiply(locs["35"], locs["93"], regs[47]);
    info.eval->relinearize_inplace(regs[47], rk);
    info.eval->multiply(regs[46], regs[47], regs[48]);
    info.eval->relinearize_inplace(regs[48], rk);
    info.eval->add(locs["854"], locs["450"], regs[49]);
    info.eval->add(locs["470"], locs["804"], regs[50]);
    info.eval->add(regs[49], regs[50], regs[51]);
    info.eval->multiply(regs[48], regs[51], regs[52]);
    info.eval->relinearize_inplace(regs[52], rk);
    info.eval->add(locs["742"], locs["494"], regs[53]);
    info.eval->add(locs["344"], locs["526"], regs[54]);
    info.eval->multiply(regs[53], regs[54], regs[55]);
    info.eval->relinearize_inplace(regs[55], rk);
    info.eval->add(locs["150"], locs["692"], regs[56]);
    info.eval->add(locs["847"], locs["576"], regs[57]);
    info.eval->add(regs[56], regs[57], regs[58]);
    info.eval->add(regs[55], regs[58], regs[59]);
    info.eval->add(regs[52], regs[59], regs[60]);
    info.eval->add(regs[45], regs[60], regs[61]);
    info.eval->multiply(regs[30], regs[61], regs[62]);
    info.eval->relinearize_inplace(regs[62], rk);
    std::vector<ctxt> answer;
    answer.push_back(regs[62]);
    return answer;
}
    