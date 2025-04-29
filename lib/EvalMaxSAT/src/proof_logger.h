#ifndef PROOF_LOGGER_H
#define PROOF_LOGGER_H

#include <memory>
#include <vector>
#include <string>
#include <unordered_map>
#include <unordered_set>

enum class NodeType {
    StartNode,
    LowerBound,
    UpperBound,
    HardClause,
    SoftClause,
    CardClause
};

enum class RuleID {
    EmptySoftClause,
    Hardening,
    UnsatisfiableLiteral,
    CliqueRelaxation,
    ConflictRelaxation,
    TotalizerUpdate,
    ZeroWeightCardinality,
    UpperBoundUpdate,
    OptimumFound,
    NoBetterSolution
};

struct NodeEntry {
    int addressID;
    NodeType type;
    long long value;
    std::vector<int> literals;
    std::vector<int> conflict;
    long long constraint;
    std::vector<int> linkedClauses;
    std::vector<bool> solution;

    NodeEntry() = default;

    NodeEntry(int id, NodeType t, long long val = -1, std::vector<int> lits = {}, std::vector<int> confl = {}, long long cons = -1, std::vector<int> lC = {}, std::vector<bool> sol = {})
        : addressID(id), type(t), value(val), literals(std::move(lits)), conflict(std::move(confl)), constraint(cons), linkedClauses(std::move(lC)), solution(std::move(sol)) {}
};

struct ProofStepEntry {
    int stepID;
    RuleID ruleType;
    std::vector<std::vector<int>> premiseIDs;
    std::vector<std::vector<int>> resultIDs;

    ProofStepEntry(int sid, RuleID rule, std::vector<std::vector<int>> premises = {}, std::vector<std::vector<int>> results = {})
        : stepID(sid), ruleType(rule), premiseIDs(std::move(premises)), resultIDs(std::move(results)) {}
};

std::shared_ptr<NodeEntry> addNode(NodeType type, long long value = -1, std::vector<int> literals = {}, std::vector<int> conflict = {}, long long constraint = -1, std::vector<int> linkedClauses = {}, std::vector<bool> solution = {});
ProofStepEntry& addProofStep(RuleID rule, std::vector<std::vector<int>> premises = {}, std::vector<std::vector<int>> results = {});
void exportProofLog(const std::string& filename);

extern int nodeCounter;
extern int proofStepCounter;
extern std::vector<std::shared_ptr<NodeEntry>> nodeLog;
extern std::vector<ProofStepEntry> proofSteps;

extern std::shared_ptr<NodeEntry> latestHardC;
extern std::shared_ptr<NodeEntry> latestSoftC;

#endif