#include "proof_checker.h"
#include "cadicalinterface.h"

#include <fstream>
#include <sstream>
#include <iostream>
#include <cassert>
#include <limits>

static std::map<int, ParsedNode> nodeByID;
static std::vector<ProofStepEntry> steps;
ProofState state;

// ----------------- Helper: Error reporting -----------------
void reportError(int stepID, const std::string& message) {
    std::cout << "Proof error at step " << stepID << ": " << message << std::endl;
}

void printVector(const std::vector<int>& vec) {
    std::cout << "[";
    for (size_t i = 0; i < vec.size(); ++i) {
        std::cout << vec[i];
        if (i + 1 < vec.size()) std::cout << ", ";
    }
    std::cout << "]" << std::endl;
}

template<typename SAT_SOLVER = Solver_cadical>
bool isUNSAT(const std::vector<std::vector<int>>& formula) {
    SAT_SOLVER solver;

    // Add clauses
    for (const auto& clause : formula) {
        solver.addClause(clause);
    }
    // for (const auto& clause : formula) {
    //     std::cout << "Adding clause: ";
    //     for (int lit : clause) std::cout << lit << " ";
    //     std::cout << "\n";
    //     solver.addClause(clause);
    // }

    // Solve without assumptions
    return !solver.solve();
}

// ----------------- Helper: String parsing -----------------
static std::vector<int> parseIntList(const std::string& s) {
    std::vector<int> result;
    std::stringstream ss(s);
    char ch;
    int val;
    while (ss >> ch && ch != '[');

    while (true) {            // skip whitespace
        if (!(ss >> val)) break;  // stop if int can't be read
        result.push_back(val);
        ss >> ch;
        ss >> std::ws;
        if (ch == ']') break;
    }

    // while (ss >> val) {
    //     result.push_back(val);
    //     ss >> ch;
    //     std::cout << val << std::endl;
    //     std::cout << ch << std::endl;
    //     if (ch == ']') break;
    // }
    return result;
}

static std::vector<bool> parseBoolList(const std::string& s) {
    std::vector<bool> result;
    std::stringstream ss(s);
    char ch;
    std::string token;
    while (ss >> ch && ch != '[');
    while (ss >> token) {
        if (!token.empty() && (token.back() == ',' || token.back() == ']')) {
            token.pop_back();
        }
        if (token == "true") result.push_back(true);
        else if (token == "false") result.push_back(false);
        else break;
        if (s.find(']') != std::string::npos && token.back() == ']') break;
    }
    return result;
}

static std::vector<std::vector<int>> parseNestedIntList(const std::string& s) {
    std::vector<std::vector<int>> result;
    std::stringstream ss(s);
    char ch;
    int counter = 0;

    while (ss >> ch && ch != '[');

    while (ss >> ch) {
        if (ch == '[') {
            std::vector<int> inner;
            int val;

            char nextChar = ss.peek();
            if (nextChar == ']') {
                ss >> ch;
                result.push_back(inner); // push empty vector
                ss >> ch; // consume possible ',' or outer ']'
                if (ch == ']') break;
                continue;
            }

            while (true) {
                ss >> val;
                inner.push_back(val);

                if (!(ss >> ch)) break;
                if (ch == ']') break;
                if (ch != ',') break;
            }

            result.push_back(inner);
        } else if (ch == ']') {
            break; 
        }
    }
    return result;
}

static std::vector<int> extractIntArray(const std::string& s, const std::string& key) {
    size_t start = s.find(key);
    if (start == std::string::npos) return {};
    start = s.find('[', start);
    size_t end = s.find(']', start);
    if (start == std::string::npos || end == std::string::npos) return {};
    return parseIntList(s.substr(start, end - start + 1));
}

static std::vector<bool> extractBoolArray(const std::string& s, const std::string& key) {
    size_t start = s.find(key);
    if (start == std::string::npos) return {};
    start = s.find('[', start);
    size_t end = s.find(']', start);
    if (start == std::string::npos || end == std::string::npos) return {};
    return parseBoolList(s.substr(start, end - start + 1));
}

// ----------------- Proof file parsing -----------------
static bool parseProofFile(const std::string& filename) {
    std::ifstream in(filename);
    if (!in) return false;
    int counter = 0;

    std::string line;
    while (std::getline(in, line)) {
        if (line.empty() || line[0] == '#') continue;

        std::stringstream ss(line);
        std::string kind;
        ss >> kind;

        if (kind == "NODE") {
            int id, typeInt;
            long long val = -1, cons = -1;
            std::vector<int> lits, conflict, linkedClauses;
            std::vector<bool> solution;

            ss >> id;
            std::string fullLine;
            std::getline(ss, fullLine);

            // Parse scalar fields
            size_t pos;
            if ((pos = fullLine.find("type=")) != std::string::npos)
                typeInt = std::stoi(fullLine.substr(pos + 5));
            if ((pos = fullLine.find("value=")) != std::string::npos)
                val = std::stoll(fullLine.substr(pos + 6));
            if ((pos = fullLine.find("constraint=")) != std::string::npos)
                cons = std::stoll(fullLine.substr(pos + 11));

            // Parse array fields
            lits = extractIntArray(fullLine, "lits=");
            conflict = extractIntArray(fullLine, "conflict=");
            linkedClauses = extractIntArray(fullLine, "linkedClauses=");
            solution = extractBoolArray(fullLine, "solution=");

            nodeByID[id] = ParsedNode(id, static_cast<NT>(typeInt), val, lits, conflict, cons, linkedClauses, solution);
        } else if (kind == "STEP") {
            int stepID, ruleInt;
            std::string premiseLine, resultLine;

            std::string tmp;
            ss >> stepID >> tmp;
            if (tmp.rfind("rule=", 0) == 0) {
                ruleInt = std::stoi(tmp.substr(5));
            }

            if (!std::getline(in, premiseLine)) {
                std::cout << "Missing premise line for STEP" << std::endl;
                return false;
            }
            if (!std::getline(in, resultLine)) {
                std::cout << "Missing result line for STEP" << std::endl;
                return false;
            }

            std::vector<std::vector<int>> premises = parseNestedIntList(premiseLine);
            std::vector<std::vector<int>> results = parseNestedIntList(resultLine);

            steps.emplace_back(stepID, static_cast<RuleID>(ruleInt), premises, results);
        }
    }
    return true;
}

// ----------------- Rule Dispatch -----------------

static bool applyStep(const ProofStepEntry& step) {
    std::cout << "Rule " << static_cast<int>(step.ruleType) << std::endl;
    switch (step.ruleType) {
        case RuleID::EmptySoftClause: {
            int oldLB = step.premiseIDs[0][0];
            int oldSC = step.premiseIDs[1][0];
            int newLB = step.resultIDs[0][0];

            if (!state.activeNodes.count(oldLB) || !state.activeNodes.count(oldSC)) {
                reportError(step.stepID, "Premises not in active node set.");
                return false;
            }

            if (!state.unprocessedNodes.count(newLB)) {
                reportError(step.stepID, "Results not in unprocessed node set.");
                return false;
            }

            const auto& oldLowerBound = state.lowerBounds[oldLB];
            const auto& oldSoftClause = state.softClauses[oldSC];
            const auto& newLowerBound = state.lowerBounds[newLB];
        
            // Ensure the soft clause is empty (i.e., it is unsatisfiable)
            if (!oldSoftClause.second.empty()) {
                reportError(step.stepID, "Soft clause is not empty.");
                return false;
            }
        
            // Update LB, i.e. LB <- LB + weight
            long long increasedLB = oldLowerBound + oldSoftClause.first;
            if (newLowerBound != increasedLB) {
                reportError(step.stepID, "Lower bound not updated correctly.");
                return false;
            }
        
            state.activeNodes.erase(oldLB);
            state.activeNodes.erase(oldSC);
            state.activeNodes.insert(newLB);
            state.unprocessedNodes.erase(newLB);
            return true;
        }
        case RuleID::Hardening: {
            int oldLB = step.premiseIDs[0][0];
            int oldUB = step.premiseIDs[1][0];
            int oldSCC = step.premiseIDs[2][0];
            int newHC = step.resultIDs[0][0];

            if (!state.activeNodes.count(oldLB) || !state.activeNodes.count(oldUB) || !state.activeNodes.count(oldSCC)) {
                reportError(step.stepID, "Premises not in active node set.");
                return false;
            }

            if (!state.unprocessedNodes.count(newHC)) {
                reportError(step.stepID, "Results not in unprocessed node set.");
                return false;
            }

            const auto& oldLowerBound = state.lowerBounds[oldLB];
            const auto& oldUpperBound = state.upperBounds[oldUB];
            const auto& newHardClause = state.hardClauses[newHC];
        
            long long differenceUbLb = oldUpperBound.first - oldLowerBound;
            long long litWeight;
            int lit;
        
            NT type = nodeByID[oldSCC].type;
            
            // Clause Selection
            if (type == NT::SoftClause) {
                const auto& oldSoftClause = state.softClauses[oldSCC];
                litWeight = oldSoftClause.first;
                lit = oldSoftClause.second[0];
            } else if (type == NT::CardClause) {
                const auto& oldCardClause = state.cardClauses[oldSCC];
                litWeight = std::get<0>(oldCardClause);
                lit = std::get<1>(oldCardClause)[0];
            } else {
                reportError(step.stepID, "Hardened node is not a soft or card clause.");
                return false;
            }
        
            // Ensure clause is hardened
            if (newHardClause[0] != lit) {
                reportError(step.stepID, "Hardened clause literal mismatch.");
                return false;
            }
        
            // Weight Threshold Check, i.e., weight >= UB - LB
            if (litWeight < differenceUbLb) {
                reportError(step.stepID, "Hardening is not justifiable.");
                return false;
            }
        
            state.activeNodes.erase(oldSCC);
            state.activeNodes.insert(newHC);
            state.unprocessedNodes.erase(newHC);
            return true;  
        }
        case RuleID::UnsatisfiableLiteral: {
            int oldLB = step.premiseIDs[0][0];
            int oldLit = step.premiseIDs[1][0];
            int newLB = step.resultIDs[0][0];
            int newHC = step.resultIDs[1][0];

            if (!state.activeNodes.count(oldLB) || !state.activeNodes.count(oldLit)) {
                reportError(step.stepID, "Premises not in active node set.");
                return false;
            }

            if (!state.unprocessedNodes.count(newLB) || !state.unprocessedNodes.count(newHC)) {
                reportError(step.stepID, "Results not in unprocessed node set.");
                return false;
            }

            const auto& oldLowerBound = state.lowerBounds[oldLB];
            const auto& newLowerBound = state.lowerBounds[newLB];
            const auto& newHardClause = state.hardClauses[newHC];

            int lit;
            long long litWeight;

            NT type = nodeByID[oldLit].type;
            
            // Clause Selection
            if (type == NT::SoftClause) {
                const auto& oldSoftClause = state.softClauses[oldLit];
                litWeight = oldSoftClause.first;
                lit = oldSoftClause.second[0];
            } else if (type == NT::CardClause) {
                const auto& oldCardClause = state.cardClauses[oldLit];
                litWeight = std::get<0>(oldCardClause);
                lit = std::get<1>(oldCardClause)[0];
            } else {
                reportError(step.stepID, "Failed literal node is not a soft or card clause.");
                return false;
            }

            // Add inverse of lit as hard clause
            if (newHardClause[0] != -lit) {
                reportError(step.stepID, "Hard clause is not { -failedLit }");
                return false;
            }        

            // Update LB, i.e. LB <- LB + weight
            long long increasedLB = oldLowerBound + litWeight;
            if (newLowerBound != increasedLB) {
                reportError(step.stepID, "Lower bound not updated correctly.");
                return false;
            }

            // Check that that lit leads to direct contradiction, i.e. solve(lit) == UNSAT
            std::vector<std::vector<int>> checkClauses;
            for (const auto& [id, clause] : state.hardClauses) {
                if (state.activeNodes.count(id)) {
                    checkClauses.push_back(clause);
                }
            }
            checkClauses.push_back({ lit });
            if (!isUNSAT(checkClauses)) {
                reportError(step.stepID, "SAT check failed: {hard clauses} and {failedLit} is SAT.");
                return false;
            }

            state.activeNodes.erase(oldLB);
            state.activeNodes.erase(oldLit);
            state.activeNodes.insert(newLB);
            state.activeNodes.insert(newHC);
            state.unprocessedNodes.erase(newLB);
            state.unprocessedNodes.erase(newHC);
            return true;
        }
        case RuleID::ConflictRelaxation: {
            int oldLB = step.premiseIDs[0][0];
            std::vector<int> conflictsIDs = step.premiseIDs[1];
            int newLB = step.resultIDs[0][0];
            std::vector<int> updSCs = step.resultIDs[1];
            std::vector<int> updCCs = step.resultIDs[2];
            int newCC = step.resultIDs[3][0];

            if (!state.activeNodes.count(oldLB)) {
                reportError(step.stepID, "Premises not in active node set.");
                return false;
            }

            for (int conflID : conflictsIDs) {
                if (!state.activeNodes.count(conflID)) {
                    reportError(step.stepID, "Premises not in active node set.");
                    return false;
                }
            }

            if (!state.unprocessedNodes.count(newLB) || !state.unprocessedNodes.count(newCC)) {
                reportError(step.stepID, "Results not in unprocessed node set.");
                return false;
            }

            for (int scID : updSCs) {
                if (!state.unprocessedNodes.count(scID)) {
                    reportError(step.stepID, "Results not in unprocessed node set.");
                    return false;
                }
            }

            for (int ccID : updCCs) {
                if (!state.unprocessedNodes.count(ccID)) {
                    reportError(step.stepID, "Results not in unprocessed node set.");
                    return false;
                }
            }

            const auto& oldLowerBound = state.lowerBounds[oldLB];
            const auto& newLowerBound = state.lowerBounds[newLB];
            const auto& newCardClause = state.cardClauses[newCC];

            // Compute minimum weight in the conflict set
            long long minWeight = std::numeric_limits<long long>::max();
            for (int id : conflictsIDs) {
                const auto& node = nodeByID[id];
                minWeight = std::min(minWeight, node.value);
            }

            // Update LB, i.e. LB <- LB + weight
            long long increasedLB = oldLowerBound + minWeight;
            if (newLowerBound != increasedLB) {
                reportError(step.stepID, "Lower bound not updated correctly.");
                return false;
            }

            std::vector<std::vector<int>> conflictClauses;

            // Validate weight reduction for updated literals
            for (int idOld : conflictsIDs) {
                NT type = nodeByID[idOld].type;
                if (type == NT::SoftClause) {
                    const auto& oldSoftClause = state.softClauses[idOld];
                    long long oldLitWeight = oldSoftClause.first;
                    int oldLit = oldSoftClause.second[0];
                    bool matched = false;
                    for (int idNew : updSCs) {
                        const auto& newSoftClause = state.softClauses[idNew];
                        long long newLitWeight = newSoftClause.first;
                        int newLit = newSoftClause.second[0];
                        if (newLit == oldLit) {
                            conflictClauses.push_back({newLit});
                            if (newLitWeight != oldLitWeight - minWeight) {
                                reportError(step.stepID, "Soft clause weight not correctly reduced.");
                                return false;
                            }
                            matched = true;
                            break;
                        }
                    }
                    if (!matched) {
                        reportError(step.stepID, "No updated soft clause found.");
                    }
                } else if (type == NT::CardClause) {
                    const auto& oldCardClause = state.cardClauses[idOld];
                    const auto& [oldLitWeight, oldLits, oldConflict, oldConstr, oldLinkedCl] = state.cardClauses[idOld];
                    std::cout << "Linked Clauses: " << oldLinkedCl.size() << std::endl;
                    int oldLit = oldLits[0];
                    bool matched = false;
                    for (int idNew : updCCs) {
                        const auto& [newLitWeight, newLits, newConflict, newConstr, newLinkedCl] = state.cardClauses[idNew];
                        int newLit = newLits[0];
                        if (newLit == oldLit && newConflict == oldConflict && newConstr == oldConstr && newLinkedCl == oldLinkedCl) {
                            conflictClauses.push_back({newLit});
                            if (newLitWeight != oldLitWeight - minWeight) {
                                reportError(step.stepID, "Cardinality clause weight not correctly reduced.");
                                return false;
                            }
                            matched = true;
                            break;
                        }
                    }
                    if (!matched) {
                        reportError(step.stepID, "No updated cardinality clause found.");
                    }
                } else {
                    reportError(step.stepID, "Literal node is not a soft or card clause.");
                    return false;
                }
            }

            // Validate new totalizer literal
            if (std::get<0>(newCardClause) != minWeight) {
                reportError(step.stepID, "Weight of new cardinality clause does not match minimum conflict node weight.");
                return false;
            }

            std::cout << "State unprocessed: " << state.unprocessedNodes.size() << std::endl;
            // for (int id : state.unprocessedNodes) {
            //     std::cout << id << std::endl;
            // }

            // Check that solve(conflict) == UNSAT
            std::vector<std::vector<int>> checkClauses;
            for (const auto& [id, clause] : state.hardClauses) {
                if (state.activeNodes.count(id)) {
                    checkClauses.push_back(clause);
                }
            }
            std::cout << "Conflict: " << conflictClauses.size() << std::endl;
            std::cout << "Hardclauses: " << checkClauses.size() << std::endl;
            checkClauses.insert(checkClauses.end(), conflictClauses.begin(), conflictClauses.end());
            if (!isUNSAT(checkClauses)) {
                reportError(step.stepID, "SAT check failed: {hard clauses} and {conflict literals} is SAT.");
                return false;
            }

            state.activeNodes.erase(oldLB);
            for (int id : conflictsIDs) {
                state.activeNodes.erase(id);
            }
            state.activeNodes.insert(newLB);
            state.unprocessedNodes.erase(newLB);
            for (int id : updSCs) {
                state.activeNodes.insert(id);
                state.unprocessedNodes.erase(id);
            }
            for (int id : updCCs) {
                state.activeNodes.insert(id);
                state.unprocessedNodes.erase(id);
            }
            state.activeNodes.insert(newCC);
            state.unprocessedNodes.erase(newCC);
            for (int id : std::get<4>(newCardClause)) {
                state.activeNodes.insert(id);
                state.unprocessedNodes.erase(id);
            }
            return true;
        }
        case RuleID::CliqueRelaxation: {
            int oldLB = step.premiseIDs[0][0];
            std::vector<int> conflictsIDs = step.premiseIDs[1];
            int newLB = step.resultIDs[0][0];
            std::vector<int> updSCs = step.resultIDs[1];
            std::vector<int> updCCs = step.resultIDs[2];
            int newHC = step.resultIDs[3][0];
            int newSC = step.resultIDs[4][0];

            if (!state.activeNodes.count(oldLB)) {
                reportError(step.stepID, "Premises not in active node set.");
                return false;
            }

            for (int conflID : conflictsIDs) {
                if (!state.activeNodes.count(conflID)) {
                    reportError(step.stepID, "Premises not in active node set.");
                    return false;
                }
            }

            if (!state.unprocessedNodes.count(newLB) || !state.unprocessedNodes.count(newHC) || !state.unprocessedNodes.count(newSC)) {
                reportError(step.stepID, "Results not in unprocessed node set.");
                return false;
            }

            for (int scID : updSCs) {
                if (!state.unprocessedNodes.count(scID)) {
                    reportError(step.stepID, "Results not in unprocessed node set.");
                    return false;
                }
            }

            for (int ccID : updCCs) {
                if (!state.unprocessedNodes.count(ccID)) {
                    reportError(step.stepID, "Results not in unprocessed node set.");
                    return false;
                }
            }

            const auto& oldLowerBound = state.lowerBounds[oldLB];
            const auto& newLowerBound = state.lowerBounds[newLB];
            const auto& newHardClause = state.hardClauses[newHC];
            const auto& newSoftClause = state.softClauses[newSC];

            // Compute minimum weight in the conflict set
            long long minWeight = std::numeric_limits<long long>::max();
            for (int id : conflictsIDs) {
                const auto& node = nodeByID[id];
                minWeight = std::min(minWeight, node.value);
            }

            // Update LB, i.e. LB <- LB + (weight * (conflict.size - 1))
            long long increasedLB = oldLowerBound + minWeight * (conflictsIDs.size() - 1);
            if (newLowerBound != increasedLB) {
                reportError(step.stepID, "Lower bound not updated correctly.");
                return false;
            }

            std::vector<std::vector<int>> conflictClauses;
            
            // Validate weight reduction for updated literals
            for (int idOld : conflictsIDs) {
                NT type = nodeByID[idOld].type;
                if (type == NT::SoftClause) {
                    const auto& oldSoftClause = state.softClauses[idOld];
                    long long oldLitWeight = oldSoftClause.first;
                    int oldLit = oldSoftClause.second[0];
                    bool matched = false;
                    for (int idNew : updSCs) {
                        const auto& newSoftClause = state.softClauses[idNew];
                        long long newLitWeight = newSoftClause.first;
                        int newLit = newSoftClause.second[0];
                        if (newLit == oldLit) {
                            conflictClauses.push_back({newLit});
                            if (newLitWeight != oldLitWeight - minWeight) {
                                reportError(step.stepID, "Soft clause weight not correctly reduced.");
                                return false;
                            }
                            matched = true;
                            break;
                        }
                    }
                    if (!matched) {
                        reportError(step.stepID, "No updated soft clause found.");
                    }
                } else if (type == NT::CardClause) {
                    const auto& oldCardClause = state.cardClauses[idOld];
                    const auto& [oldLitWeight, oldLits, oldConflict, oldConstr, oldLinkedCl] = state.cardClauses[idOld];
                    int oldLit = oldLits[0];
                    bool matched = false;
                    for (int idNew : updCCs) {
                        const auto& [newLitWeight, newLits, newConflict, newConstr, newLinkedCl] = state.cardClauses[idNew];
                        int newLit = newLits[0];
                        if (newLit == oldLit && newConflict == oldConflict && newConstr == oldConstr && newLinkedCl == oldLinkedCl) {
                            conflictClauses.push_back({newLit});
                            if (newLitWeight != oldLitWeight - minWeight) {
                                reportError(step.stepID, "Cardinality clause weight not correctly reduced.");
                                return false;
                            }
                            matched = true;
                            break;
                        }
                    }
                    if (!matched) {
                        reportError(step.stepID, "No updated cardinality clause found.");
                    }
                } else {
                    reportError(step.stepID, "Literal node is not a soft or card clause.");
                    return false;
                }
            }

            // Validate new soft clause
            if (newSoftClause.first != minWeight) {
                reportError(step.stepID, "Weight of new soft clause does not match minimum conflict node weight.");
                return false;
            }
            
            // Validate new hard clause using new soft literal and conflict
            std::vector<int> tempClause;
            for (std::vector<int> cl : conflictClauses) {
                tempClause.push_back(cl[0]);
            }
            tempClause.push_back(-newSoftClause.second[0]);
            std::vector<int> a = newHardClause;
            std::vector<int> b = tempClause;
            std::sort(a.begin(), a.end());
            std::sort(b.begin(), b.end());
            if (a != b) {
                reportError(step.stepID, "New hard clause does not match the expected clause.");
                return false;
            }
            
            // Validate clique correctness
            std::vector<std::vector<int>> activeHardClauses;
            for (const auto& [id, clause] : state.hardClauses) {
                if (state.activeNodes.count(id)) {
                    activeHardClauses.push_back(clause);
                }
            }
            for (size_t i = 0; i < conflictClauses.size(); ++i) {
                for (size_t j = i + 1; j < conflictClauses.size(); ++j) {
                    std::vector<int> lits1 = conflictClauses[i];
                    std::vector<int> lits2 = conflictClauses[j];
                    std::vector<std::vector<int>> checkClauses = activeHardClauses;
                    checkClauses.push_back(lits1);
                    checkClauses.push_back(lits2);
                    if (!isUNSAT(checkClauses)) {
                        reportError(step.stepID, "Clique conflict core is not UNSAT.");
                        return false;
                    }
                }
            }

            state.activeNodes.erase(oldLB);
            for (int id : conflictsIDs) {
                state.activeNodes.erase(id);
            }
            state.activeNodes.insert(newLB);
            state.unprocessedNodes.erase(newLB);
            for (int id : updSCs) {
                state.activeNodes.insert(id);
                state.unprocessedNodes.erase(id);
            }
            for (int id : updCCs) {
                state.activeNodes.insert(id);
                state.unprocessedNodes.erase(id);
            }
            state.activeNodes.insert(newHC);
            state.activeNodes.insert(newSC);
            state.unprocessedNodes.erase(newHC);
            state.unprocessedNodes.erase(newSC);
            return true;
        }
        case RuleID::TotalizerUpdate: {
            int oldCC = step.premiseIDs[0][0];
            int newCC = step.resultIDs[0][0];

            if (!state.activeNodes.count(oldCC)) {
                reportError(step.stepID, "Premises not in active node set.");
                return false;
            }

            if (!state.unprocessedNodes.count(newCC)) {
                reportError(step.stepID, "Results not in unprocessed node set.");
                return false;
            }

            const auto& [oldLitWeight, oldLits, oldConflict, oldConstr, oldLinkedCl] = state.cardClauses[oldCC];
            const auto& [newLitWeight, newLits, newConflict, newConstr, newLinkedCl] = state.cardClauses[newCC];

            for (int id : newLinkedCl) {
                if (!state.unprocessedNodes.count(id)) {
                    reportError(step.stepID, "Results not in unprocessed node set.");
                    return false;
                }
                state.activeNodes.insert(id);
                state.unprocessedNodes.erase(id);
            }
        
            // Validate new totalizer using old totalizer
            if (oldLitWeight == newLitWeight && oldConflict == newConflict && oldConstr + 1 == newConstr) {
                reportError(step.stepID, "Cardinality literals changed during RelaxCardinality.");
                return false;
            }
        
            state.activeNodes.insert(newCC);
            state.unprocessedNodes.erase(newCC);
            return true;
        }
        case RuleID::ZeroWeightCardinality: {
            int oldCC = step.premiseIDs[0][0];

            if (!state.activeNodes.count(oldCC)) {
                reportError(step.stepID, "Premises not in active node set.");
                return false;
            }

            const auto& oldCardClauses = state.cardClauses[oldCC];
            long long cardWeight = std::get<0>(oldCardClauses);
        
            if (cardWeight != 0) {
                reportError(step.stepID, "Cardinality clause does not have weight 0.");
                return false;
            }
        
            state.activeNodes.erase(oldCC);
            return true;
        }
        case RuleID::UpperBoundUpdate: {
            int oldLB = step.premiseIDs[0][0];
            int oldUB = step.premiseIDs[1][0];
            int newUB = step.resultIDs[0][0];

            if (!state.activeNodes.count(oldLB) || !state.activeNodes.count(oldUB)) {
                reportError(step.stepID, "Premises not in active node set.");
                return false;
            }

            if (!state.unprocessedNodes.count(newUB)) {
                reportError(step.stepID, "Results not in unprocessed node set.");
                return false;
            }

            const auto& oldLowerBound = state.lowerBounds[oldLB];
            const auto& oldUpperBound = state.upperBounds[oldUB];
            const auto& newUpperBound = state.upperBounds[newUB];
            std::vector<bool> sol = newUpperBound.second;

            long long cost = 0;
            for (const auto& [id, clause] : state.softClauses) {
                if (state.activeNodes.count(id)) {
                    long long curWeight = clause.first;
                    int lit = clause.second[0];
                    if (lit > 0) {
                        if(sol[lit] == 0) {
                            cost += curWeight;
                        }
                    } else {
                        if(sol[abs(lit)] == 1) {
                            cost += curWeight;
                        }
                    }
                }
            }
            for (const auto& [id, clause] : state.cardClauses) {
                if (state.activeNodes.count(id)) {
                    long long curWeight = std::get<0>(clause);
                    int lit = std::get<1>(clause)[0];
                    if (lit > 0) {
                        if(sol[lit] == 0) {
                            cost += curWeight;
                        }
                    } else {
                        if(sol[abs(lit)] == 1) {
                            cost += curWeight;
                        }
                    }
                }
            }

            // Check that new cost is actually lower than before
            if (newUpperBound.first > oldUpperBound.first) {
                reportError(step.stepID, "New UB is not an improvement.");
                return false;
            }

            // TODO: find a solution for cost determination
            // long long totalCost = cost + oldLowerBound;
            // if (newUpperBound.first != totalCost) {
            //     std::cout << "New UB: " << newUpperBound.first << std::endl;
            //     std::cout << "Total Cost: " << totalCost << std::endl;
            //     reportError(step.stepID, "New UB is not equal to the compute total cost of the solution.");
            //     return false;
            // }

            // check that the solution actually leads to SAT
            std::vector<std::vector<int>> checkSolution;
            for(int lit=1; lit<checkSolution.size(); lit++) {
                if(sol[lit] == 0) {
                    checkSolution.push_back({-lit});
                } else {
                    checkSolution.push_back({lit});
                }
            }
            std::vector<std::vector<int>> checkClauses;
            for (const auto& [id, clause] : state.hardClauses) {
                if (state.activeNodes.count(id)) {
                    checkClauses.push_back(clause);
                }
            }
            checkClauses.insert(checkClauses.end(), checkSolution.begin(), checkSolution.end());
            if (isUNSAT(checkClauses)) {
                reportError(step.stepID, "SAT check failed: {hard clauses} and {conflict literals} lead to UNSAT.");
                return false;
            }
        
            state.activeNodes.erase(oldUB);
            state.activeNodes.insert(newUB);
            state.unprocessedNodes.erase(newUB);
            return true;
        }
        case RuleID::OptimumFound: {
            int curLB = step.premiseIDs[0][0];
            int curUB = step.resultIDs[0][0];

            if (!state.activeNodes.count(curLB) || !state.activeNodes.count(curUB)) {
                reportError(step.stepID, "Premises not in active node set.");
                return false;
            }

            const auto& oldLowerBound = state.lowerBounds[curLB];
            const auto& oldUpperBound = state.upperBounds[curUB];
        
            if (oldLowerBound != oldUpperBound.first) {
                reportError(step.stepID, "Lower bound is not equal to the upper bound.");
                return false;
            }

            state.activeNodes.erase(curLB);
            state.activeNodes.erase(curUB);
            return true;
        }
        case RuleID::NoBetterSolution: {
            int curLB = step.premiseIDs[0][0];
            int curUB = step.resultIDs[0][0];

            if (!state.activeNodes.count(curLB) || !state.activeNodes.count(curUB)) {
                reportError(step.stepID, "Premises not in active node set.");
                return false;
            }

            const auto& oldLowerBound = state.lowerBounds[curLB];
            const auto& oldUpperBound = state.upperBounds[curUB];

            if (oldLowerBound != oldUpperBound.first) {
                reportError(step.stepID, "Lower bound is not equal to the upper bound.");
                return false;
            }

            state.activeNodes.erase(curLB);
            state.activeNodes.erase(curUB);
            return true;
        }
        default:
            std::cout << "Unknown or unimplemented rule in step " << step.stepID << std::endl;
            return false;
    }
}

// ----------------- Main checker -----------------

bool checkProofFile(const std::string& filename) {
    if (!parseProofFile(filename)) {
        std::cout << "Failed to parse proof file: " << filename << std::endl;
        return false;
    }

    bool foundStartNode = false;
    for (const auto& [id, node] : nodeByID) {
        if (node.type == NT::StartNode) {
            if (foundStartNode) {
                std::cout << "Multiple StartNodes found." << std::endl;
                return false;
            }
            foundStartNode = true;
            continue;
        }

        // Only nodes before the first step are allowed to be part of the initial state
        if (!foundStartNode) {
            state.activeNodes.insert(id);
        } else {
            state.unprocessedNodes.insert(id);
        }

        switch (node.type) {
            case NT::LowerBound:
                state.lowerBounds[id] = {node.value};
                break;
            case NT::UpperBound:
                state.upperBounds[id] = {node.value, node.solution};
                break;
            case NT::HardClause:
                state.hardClauses[id] = {node.lits};
                break;
            case NT::SoftClause:
                state.softClauses[id] = {node.value, node.lits};
                break;
            case NT::CardClause:
                state.cardClauses[id] = {node.value, node.lits, node.conflict, node.constraint, node.linkedClauses};
                break;
            default: break;
        }
    }

    for (const auto& step : steps) {
        std::cout << "Step " << step.stepID << std::endl;
        if (!applyStep(step)) {
            reportError(step.stepID, "Rule application failed.");
            return false;
        }
    }

    std::cout << "Proof check passed!" << std::endl;
    return true;
}