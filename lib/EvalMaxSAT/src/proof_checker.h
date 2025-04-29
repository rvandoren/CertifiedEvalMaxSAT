#ifndef PROOF_CHECKER_H
#define PROOF_CHECKER_H

#include <memory>
#include <string>
#include <vector>
#include <set>
#include <map>
#include <limits>
#include <unordered_map>
#include "proof_logger.h"

struct ProofState {
    std::map<int, long long> lowerBounds;
    std::map<int, std::pair<long long, std::vector<bool>>> upperBounds;
    std::map<int, std::vector<int>> hardClauses;
    std::map<int, std::pair<long long, std::vector<int>>> softClauses;
    std::map<int, std::tuple<long long, std::vector<int>, std::vector<int>, long long, std::vector<int>>> cardClauses;

    std::unordered_set<int> activeNodes;
    std::unordered_set<int> unprocessedNodes;
};

enum class NT {
    StartNode,
    LowerBound,
    UpperBound,
    HardClause,
    SoftClause,
    CardClause
};

struct ParsedNode {
    int id;
    NT type;
    long long value;
    std::vector<int> lits;
    std::vector<int> conflict;
    long long constraint;
    std::vector<int> linkedClauses;
    std::vector<bool> solution;

    ParsedNode() = default;

    ParsedNode(int id_, NT type_, long long val_, std::vector<int> lits_, std::vector<int> conflict_, long long cons_, std::vector<int> linkedClauses_, std::vector<bool> sol_)
        : id(id_), type(type_), value(val_), lits(std::move(lits_)), conflict(std::move(conflict_)), constraint(cons_), linkedClauses(std::move(linkedClauses_)), solution(std::move(sol_)) {}
};


bool checkProofFile(const std::string& filename);

void reportError(int stepID, const std::string& message);

#endif