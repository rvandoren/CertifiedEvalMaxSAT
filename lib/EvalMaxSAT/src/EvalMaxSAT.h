#ifndef EVALMAXSAT_SLK178903R_H
#define EVALMAXSAT_SLK178903R_H


#include <iostream>
#include <vector>
#include <algorithm>
#include <random>
#include <queue>
#include <limits>


#include "utile.h"
#include "Chrono.h"
#include "coutUtil.h"
#include "cadicalinterface.h"
#include "cardincremental.h"
#include "rand.h"
#include "mcqd.h"
#include "proof_logger.h"


using namespace MaLib;

std::vector<std::shared_ptr<NodeEntry>> hardClauses;
std::unordered_map<int, std::shared_ptr<NodeEntry>> lit2SoftC;
std::unordered_map<int, std::shared_ptr<NodeEntry>> lit2CardC;
std::unordered_map<int, int> lit2Id;
std::map<std::tuple<std::vector<int>, t_weight>, std::shared_ptr<NodeEntry>> confl2card;
std::shared_ptr<NodeEntry> latestHardC = nullptr;
std::shared_ptr<NodeEntry> latestSoftC = nullptr;
std::shared_ptr<NodeEntry> lbNode = nullptr;
std::shared_ptr<NodeEntry> ubNode = nullptr;

class LocalOptimizer2 {
    Solver_cadical *solver;
    WeightVector poids;
    t_weight initialWeight;

public:
    LocalOptimizer2(Solver_cadical *solver, const WeightVector &poids, const t_weight &initialWeight) :
        solver(solver), poids(poids), initialWeight(initialWeight) {

    }

    t_weight calculateCostAssign(const std::vector<bool> & solution) {
        t_weight coutSolution = 0;
        for(unsigned int lit=1; lit<poids.size(); lit++) {
            assert( lit < solution.size() );
            if( poids[lit] > 0 ) {
                if( solution[lit] == 0 ) {
                    coutSolution += poids[lit];
                }
            } else if ( poids[lit] < 0 ) {
                if( solution[lit] == 1 ) {
                    coutSolution += -poids[lit];
                }
            }
        }

        return coutSolution + initialWeight;
    }

    t_weight optimize(std::vector<bool> & solution, double timeout_sec)  {
        auto timeout = MaLib::TimeOut(timeout_sec);
        MonPrint("c optimize for ", timeout_sec, " sec");

        std::vector< std::tuple<t_weight, int> > softVarFalsified;
        std::vector< int > assumSatisfied;
        for(unsigned int lit=1; lit<poids.size(); lit++) {
            assert( lit < solution.size() );
            if( poids[lit] > 0 ) {
                assert(lit < solution.size() );
                if( solution[lit] == 0 ) {
                    softVarFalsified.push_back( {poids[lit], lit} );
                } else {
                    assumSatisfied.push_back(lit);
                }
            } else if( poids[lit] < 0 ) {
                assert(lit < solution.size() );
                if( solution[lit] == 1 ) {
                    softVarFalsified.push_back( {poids[-lit], -lit} );
                } else {
                    assumSatisfied.push_back(-lit);
                }
            }
        }

        bool modify = false;
        for(int id=softVarFalsified.size()-1; id >= 0; id--) {
            assumSatisfied.push_back( std::get<1>(softVarFalsified[id]) );
            if( solver->solveLimited(assumSatisfied, timeout_sec / (double)(softVarFalsified.size()+1) ) != 1 ) {
                assumSatisfied.pop_back();
            } else {
                modify = true;
            }
        }

        if(modify) {
            auto tmp = solver->solve(assumSatisfied);
            assert(tmp == 1);
            solution = solver->getSolution();
        }

        return calculateCostAssign(solution);
    }

};

template<class SAT_SOLVER=Solver_cadical>
class EvalMaxSAT {

    ///////////////////////////
    /// Representation of the MaxSAT formula
    ///
        // NOTE: stores pointer to SAT solver instance
        SAT_SOLVER *solver = nullptr;
        // NOTE: stores the weight of each literal
        WeightVector _poids; // _poids[lit] = weight of lit
        // NOTE: maps weights to literals
        std::map<t_weight, std::set<int>> _mapWeight2Assum; // _mapWeight2Assum[weight] = set of literals with this weight
        // NOTE: tracks total cost of soft clauses
        t_weight cost = 0;

        // NOTE: handels "at most k" constraints
        // NOTE: solver may replace a group of soft literals with a single card. constr.
        struct LitCard {
            std::shared_ptr<CardIncremental_Lazy<EvalMaxSAT<SAT_SOLVER>> > card;
            int atMost;
            t_weight initialWeight;

            LitCard(std::shared_ptr<CardIncremental_Lazy<EvalMaxSAT<SAT_SOLVER>>> card, int atMost, t_weight initialWeight) : card(card), atMost(atMost), initialWeight(initialWeight) {
                assert( card != nullptr );
                assert(atMost > 0);
                assert(initialWeight > 0);
            }

            int getLit() const {
                return card->atMost(atMost);
            }

            std::vector<int> getClauseAddressIDs() const {
                return card->getClauseIDsForBound(atMost);
            }
        };

        // NOTE: maps soft literals to their corresponding cardinality constraints
        std::vector< std::optional<LitCard> > _mapAssum2Card; // _mapAssum2Card[lit] = card associated to lit
        // NOTE: stores new cardinality constraints to be added later
        std::deque< std::tuple< std::vector<int>, t_weight> > _cardToAdd; // cardinality to add
        // NOTE: literals that need to be relaxed, i.e. convereted from hard to soft
        std::vector<int> _litToRelax; // Lit to relax
    ///
    //////////////////////////

    ///////////////////////////
    /// Best solution found so far
    ///
        // NOTE: stores best assignment found so far
        std::vector<bool> solution;
        // NOTE: stores the minimum cost
        t_weight solutionCost = std::numeric_limits<t_weight>::max();
        
    ///
    //////////////////////////
private:
    ///////////////////////////
    /// Hyperparameters
    ///
        double _initialCoef = 10;
        double _averageCoef = 1.66;
        double _base = 400;
        double _minimalRefTime = 5;
        double _maximalRefTime = 5*60;
        TimeOut totalSolveTimeout = TimeOut(0.9 * 3600 );

        // NOTE: delay certain simplifications to avoid unnecessary work
        bool _delayStrategy = true;
        // NOTE: allows running multiple SAT solver calls in parallel
        bool _multiSolveStrategy = true;
        // NOTE: uses upper bounds to speed up optimization
        bool _UBStrategy = true;
    ///
    //////////////////////////////

    double getTimeRefCoef() {
        if(totalSolveTimeout.getCoefPast() >= 1)
            return 0;
        return _initialCoef * pow(_base, -totalSolveTimeout.getCoefPast());
    }

public:

    ///////////////////////////
    /// Setter
    ///
        void setCoef(double initialCoef, double coefOnRefTime) {
            auto W = [](double x){
                // Approximation de la fonction W de Lambert par la série de Taylor
                double result = x;
                x *= x;
                result += -x;
                x *= x;
                result += 3*x/2.0;
                x *= x;
                result += -8*x/3.0;
                x *= x;
                result += 125*x/24.0;
                return result;
            };

            _initialCoef = initialCoef;
            _averageCoef = coefOnRefTime;
            _base = (-initialCoef / ( coefOnRefTime * W( (-initialCoef * std::exp(-initialCoef/coefOnRefTime)) / coefOnRefTime ) ));
        }
        void setTargetComputationTime(double targetComputationTime) {
            totalSolveTimeout = TimeOut( targetComputationTime * 0.9 );
        }
        void setBoundRefTime(double minimalRefTime, double maximalRefTime) {
            _minimalRefTime = minimalRefTime;
            _maximalRefTime = maximalRefTime;
        }
        void unactivateDelayStrategy() {
            _delayStrategy = false;
        }
        void unactivateMultiSolveStrategy() {
            _multiSolveStrategy = false;
        }
        void unactivateUBStrategy() {
            _UBStrategy = false;
        }
    ///
    ////////////////////////


    public:

    EvalMaxSAT() : solver(new SAT_SOLVER) {
        _poids.push_back(0);          // Fake lit with id=0
        _mapAssum2Card.push_back({});  // Fake lit with id=0
    }

    ~EvalMaxSAT() {
        delete solver;
    }

public:

    // NOTE: function to print hyperparameters and solving constraints
    void printInfo() {
        std::cout << "c PARAMETRE INFORMATION: " << std::endl;
        std::cout << "c Stop unsat improving after " << totalSolveTimeout.getVal() << " sec" << std::endl;
        std::cout << "c Minimal ref time = " << _minimalRefTime << " sec" << std::endl;
        std::cout << "c Initial coef = " << _initialCoef << std::endl;
        std::cout << "c Average coef = " << _averageCoef << std::endl;
    }

    // NOTE: checks if the problem is weighted
    bool isWeighted() {
        return _mapWeight2Assum.size() > 1;
    }

    // NOTE: creates a new boolean variable for the solver (has weight 0)
    int newVar(bool decisionVar=true) {
        _poids.push_back(0);
        _mapAssum2Card.push_back({});

        int var = solver->newVar(decisionVar);

        assert(var == _poids.size()-1);

        return var;
    }

    // NOTE: creates soft variable (keeps track of weight)
    // NOTE: For negated variables we use negative weight
    int newSoftVar(bool value, long long weight) {
        if(weight < 0) {
            ///// TODO: ajouer Offset_Cost -= weight
            value = !value;
            weight = -weight;
        }

        _poids.push_back(weight * (((int)value)*2 - 1));
        _mapAssum2Card.push_back({});
        _mapWeight2Assum[weight].insert( (((int)value*2) - 1) * ((int)(_poids.size())-1) );

        int var = solver->newVar();
        assert(var == _poids.size()-1);

        return var;
    }


    // NOTE: adding clauses (soft and hard)
    int addClause(const std::vector<int> &clause, std::optional<long long> w = {}) {
        if( w.has_value() == false ) { // Hard clause
            if( (clause.size() == 1) && ( _poids[clause[0]] != 0 ) ) {
                if( _poids[clause[0]] < 0 ) {
                    std::cout << _poids[clause[0]] << "Negative weight here." << _poids[-clause[0]] << std::endl;
                    assert( _mapWeight2Assum[ _poids[-clause[0]] ].count( -clause[0] ) );
                    _mapWeight2Assum[ _poids[-clause[0]] ].erase( -clause[0] );
                    cost += _poids[-clause[0]];
                    std::cout << "Negative here 1." << std::endl;
                    relax(clause[0]);
                    std::cout << "Negative here 2." << std::endl;
                } else {
                    assert( _mapWeight2Assum[ _poids[clause[0]] ].count( clause[0] ) );
                    _mapWeight2Assum[ _poids[clause[0]] ].erase( clause[0] );
                    if (lit2SoftC.count(clause[0])) {
                        lit2SoftC.erase(clause[0]);
                    } else if (lit2CardC.count(abs(clause[0]))) {
                        lit2CardC.erase(abs(clause[0]));
                    } else {
                        std::cout << "Warning: Failed literal not found in soft/card map: " << clause[0] << std::endl;
                    }
                }
                _poids.set(clause[0], 0);
            }
            latestHardC = addNode(NodeType::HardClause, -1, clause, {}, -1, {}, {});
            hardClauses.push_back(latestHardC);
            solver->addClause(clause);
        } else {
            if(w.value() == 0) return 0;
            if(clause.size() > 1) { // Soft clause, i.e, "hard" clause with a soft var at the end
                if( w.value() > 0 ) {
                    auto softVar = newSoftVar(true, w.value());
                    std::vector<int> softClause = clause;
                    softClause.push_back( -softVar );
                    addClause(softClause, std::nullopt);
                    assert(softVar > 0);
                    latestSoftC = addNode(NodeType::SoftClause, w.value(), {softVar}, {}, -1, {}, {});
                    lit2Id[softVar] = latestSoftC->addressID;
                    lit2SoftC[softVar] = std::shared_ptr<NodeEntry>(latestSoftC);
                    return softVar;
                } else {
                    assert(w.value() < 0);
                    auto softVar = newSoftVar(true, -w.value());
                    for(auto lit: clause) {
                        addClause({ -softVar, lit }, std::nullopt);
                    }
                    assert(softVar > 0);
                    latestSoftC = addNode(NodeType::SoftClause, w.value(), {softVar}, {}, -1, {}, {});
                    lit2Id[softVar] = latestSoftC->addressID;
                    lit2SoftC[softVar] = std::shared_ptr<NodeEntry>(latestSoftC);
                    return softVar;
                }
            } else if(clause.size() == 1) { // Special case: unit clause.
                addWeight(clause[0], w.value());
                latestSoftC = addNode(NodeType::SoftClause, w.value(), clause, {}, -1, {}, {});
                lit2Id[clause[0]] = latestSoftC->addressID;
                lit2SoftC[clause[0]] = std::shared_ptr<NodeEntry>(latestSoftC);
            } else { assert(clause.size() == 0); // Special case: empty soft clause.
                // An empty clause means that in can be satisified, thus we are obliged to add its weight
                cost += w.value();
                latestSoftC = addNode(NodeType::SoftClause, w.value(), clause, {}, -1, {}, {});
                std::shared_ptr<NodeEntry> newLbNode = addNode(NodeType::LowerBound, cost, {}, {}, -1, {}, {});
                addProofStep(RuleID::EmptySoftClause, {{lbNode->addressID}, {latestSoftC->addressID}}, {{newLbNode->addressID}});
                lbNode = newLbNode;
            }
        }
        return 0;
    }

    // NOTE: this retrieves the variable assignment of a given literal
    bool getValue(int lit) {
        if(abs(lit) > solution.size())
            return false;
        if(lit>0)
            return solution[lit];
        if(lit<0)
            return !solution[-lit];
        assert(false);
        return 0;
    }


private:

    // NOTE: selects soft literals that must be assumed true during solving
    // NOTE: starts with highest-weighted assumptions
    // NOTE: solver gradually weakens assumptions, making the problem more relaxed
    std::set<int> initAssum(t_weight minWeightToConsider=1) {
        std::set<int> assum;

        for(auto itOnMapWeight2Assum = _mapWeight2Assum.rbegin(); itOnMapWeight2Assum != _mapWeight2Assum.rend(); ++itOnMapWeight2Assum) {
            if(itOnMapWeight2Assum->first < minWeightToConsider)
                break;
            for(auto lit: itOnMapWeight2Assum->second) {
                assum.insert(lit);
            }
        }
        return assum;
    }

    bool toOptimize = true;

public:

    void disableOptimize() {
        toOptimize = false;
    }

    bool solve() {

        totalSolveTimeout.restart();

        std::cout << "c [Proof] Starting MaxSAT solving process..." << std::endl;
        lbNode = addNode(NodeType::LowerBound, 0);
        ubNode = addNode(NodeType::UpperBound, std::numeric_limits<long long>::max());
        addNode(NodeType::StartNode);

        MonPrint("c initial cost = ", cost);

        // NOTE: tracks which literals are assumed to be true
        std::set<int> assum;

        // NOTE: stores last satisfiable assumption set
        std::set<int> lastSatAssum;

        Chrono chronoLastSolve;
        Chrono chronoLastOptimize;

        // NOTE: Detects at-most-one constraints: if a group of variables cannot all be true
        // simultaneously, the solver encodes that constraint.
        adapt_am1_exact();
        adapt_am1_FastHeuristicV7();

        // NOTE: exit if current cost is aleady as low as best-known solution.
        if(cost >= solutionCost) {
            addProofStep(RuleID::OptimumFound, {{lbNode->addressID}}, {{ubNode->addressID}});
            return true;
        }

        // NOTE: check if there are no soft clauses, then it is just a SAT problem
        if(_mapWeight2Assum.size() == 0) {
            if(solver->solve()) {
                solutionCost = cost;
                solution = solver->getSolution();

                std::shared_ptr<NodeEntry> newUbNode = addNode(NodeType::UpperBound, solutionCost, {}, {}, -1, {}, solution);

                addProofStep(RuleID::UpperBoundUpdate, {{lbNode->addressID}, {ubNode->addressID}}, {{newUbNode->addressID}});
                ubNode = newUbNode;

                addProofStep(RuleID::OptimumFound, {{lbNode->addressID}}, {{ubNode->addressID}});
                return true;
            }
            return false;
        }

        // NOTE: Checks if there is an early solution
        // by checking if any literal can be hardened and conflicts can be resolved
        // If yes, check if LB >= UB
        // If yes, we have found optimal solution
        if(harden(assum)) {
            assert(_mapWeight2Assum.size());
            if(adapt_am1_VeryFastHeuristic()) {
                if(cost >= solutionCost) {
                    addProofStep(RuleID::OptimumFound, {{lbNode->addressID}}, {{ubNode->addressID}});
                    return true;
                }
            }
        }

        ///////////////////
        /// For harden via optimize
        /// 
            // NOTE: ensures that no pending cardinality constraints or literal relaxations exist before optimizaiton
            assert(_cardToAdd.size() == 0);
            assert(_litToRelax.size() == 0);
            assert( [&](){
                for(auto e: _mapAssum2Card) {
                    if(e.has_value())
                        return false;
                }
                return true;
            }() );

            LocalOptimizer2 LO(solver, _poids, cost);
        //
        /////////////////



        // Initialize assumptions
        // NOTE: chooses the starting weight threshold for soft constraint and intializes the assumptions for the SAT solver.
        auto minWeightToConsider = chooseNextMinWeight( _mapWeight2Assum.rbegin()->first + 1 );
        assum = initAssum(minWeightToConsider);

        int resultLastSolve;

        // NOTE: infinite solving loop
        for(;;) {
            MonPrint("Full SAT...");
            assert( _cardToAdd.size() == 0 );
            assert( _litToRelax.size() == 0 );

            if(cost >= solutionCost) {
                addProofStep(RuleID::OptimumFound, {{lbNode->addressID}}, {{ubNode->addressID}});
                return true;
            }
            
            chronoLastSolve.tic();
            {

                 assert( assum == initAssum(minWeightToConsider) );

                //Chrono2 log("solve ");
                resultLastSolve = solver->solve(assum);
                MonPrint("resultLastSolve = ", resultLastSolve);
                if(resultLastSolve == 1) {
                    lastSatAssum = assum;
                }
            }

            std::cout << "c [Proof] SAT output 2: " << (resultLastSolve == 1 ? "SAT" : "UNSAT") << std::endl;

            chronoLastSolve.pause(true);
            // NOTE: If the solution is satisfiable, check if the lowest weight (1) has been reached.
            // NOTE: If no, adjust the assumptions 
            if(resultLastSolve) { // SAT
                if(minWeightToConsider == 1) {
                    solutionCost = cost;
                    solution = solver->getSolution();

                    std::shared_ptr<NodeEntry> newUbNode = addNode(NodeType::UpperBound, solutionCost, {}, {}, -1, {}, solution);
                    addProofStep(RuleID::UpperBoundUpdate, {{lbNode->addressID}, {ubNode->addressID}}, {{newUbNode->addressID}});
                    ubNode = newUbNode;
                    addProofStep(RuleID::OptimumFound, {{lbNode->addressID}}, {{ubNode->addressID}});
                    return true; // Solution found
                }
                minWeightToConsider = chooseNextMinWeight(minWeightToConsider);
                assum = initAssum(minWeightToConsider);

            } else { // UNSAT
                // NOTE: solver extracts an unsat core
                for(;;) {
                    if(resultLastSolve == 0) { // UNSAT
                        double maxLastSolveOr1 = std::min<double>(_minimalRefTime + chronoLastSolve.tacSec(), _maximalRefTime);

                        auto conflict = solver->getConflict(assum);
                        MonPrint("conflict size = ", conflict.size(), " trouvé en ", chronoLastSolve.tacSec(), "sec, donc maxLastSolveOr1 = ", maxLastSolveOr1);
                        
                        if(conflict.size() == 0) {
                            MonPrint("Fin par coupure !");
                            assert(solver->solve() == 0);
                            // We get an Unsat but with no conflict (meaning that the soft clauses do not affect the UNSAT result)
                            // If we have previously found a valid solution, we use it as optimal solution
                            addProofStep(RuleID::NoBetterSolution, {{lbNode->addressID}}, {{ubNode->addressID}});
                            return solutionCost != std::numeric_limits<t_weight>::max();
                        }

                        // 1. find better core : seconds solve
                        // NOTE: The following does not affect the proof, as we have not yet added the conflict core,
                        // and this only tries to find an "optimized" version of the core.
                        unsigned int nbSolve=0;
                        unsigned int lastImprove = 0;
                        double bestP = std::numeric_limits<double>::max();
                        if(_multiSolveStrategy && (conflict.size() > 3)) {
                            Chrono C;
                            while( ( nbSolve < 3*lastImprove ) || (nbSolve < 20) || ( (C.tacSec() < 0.1*maxLastSolveOr1*getTimeRefCoef()) && (nbSolve < 1000) ) ) {
                                nbSolve++;

                                auto tmp = solver->getConflict(assum);
                                auto p = oneMinimize(tmp, maxLastSolveOr1 * getTimeRefCoef() * 0.1, 10, true);

                                if(p<bestP) {
                                    bestP = p;
                                    conflict = tmp;
                                    MonPrint("Improve conflict at the ", nbSolve, "th solve = ", conflict.size(),  " (p = ", p , ")");
                                    if(conflict.size() <= 2) {
                                        break;
                                    }
                                    lastImprove = nbSolve;
                                }

                                if(C.tacSec() >= maxLastSolveOr1*getTimeRefCoef() ) {
                                    MonPrint("Stop second solve after ", nbSolve, "th itteration. (nb=",conflict.size(),"). (", C.tacSec(), " > ", maxLastSolveOr1, " * ", getTimeRefCoef(), ")");
                                    break;
                                }

                                std::vector<int> vAssum(assum.begin(), assum.end());
                                MaLib::MonRand::shuffle(vAssum);
                                auto res = solver->solveWithTimeout(vAssum, maxLastSolveOr1 * getTimeRefCoef() - C.tacSec()  );
                                if(res==-1) {
                                    MonPrint("Stop second solve because solveWithTimeout. (nb=",conflict.size(),").");
                                    break;
                                }
                            }
                            MonPrint("Stop second solve after ", nbSolve, " itteration in ", C.tacSec(), " sec. (nb=",conflict.size(),").");
                        }

                        // 2. minimize core
                        // NOTE: reduces the conflict by removing unnecessary literals
                        if(conflict.size() > 1) {
                            oneMinimize(conflict, maxLastSolveOr1, 1000);
                        }

                        if(conflict.size() == 0) {
                            addProofStep(RuleID::NoBetterSolution, {{lbNode->addressID}}, {{ubNode->addressID}});
                            return solutionCost != std::numeric_limits<t_weight>::max();
                        }

                        // 3. replace assum by card
                        long long minWeight = std::numeric_limits<long long>::max();
                        for(auto lit: conflict) {
                            assert(_poids[lit] > 0);
                            if( _poids[lit] < minWeight ) {
                                minWeight = _poids[lit];
                            }
                        }
                        assert(minWeight>0);

                        std::vector<int> conflictsIDs;
                        std::vector<int> updatedSoftCIDs;
                        for (int lit : conflict) {
                            auto it = lit2SoftC.find(lit);
                            if (it != lit2SoftC.end() && it->second) {
                                conflictsIDs.push_back(it->second->addressID);   
                                std::shared_ptr<NodeEntry> updatedSC = addNode(NodeType::SoftClause, it->second->value - minWeight, it->second->literals, it->second->conflict, -1, {}, {});
                                updatedSoftCIDs.push_back(updatedSC->addressID);
                                lit2SoftC[lit] = updatedSC;
                                lit2Id[lit] = updatedSC->addressID;
                            }
                        }

                        std::vector<int> updatedCardCIDs;
                        for (int lit : conflict) {
                            auto it = lit2CardC.find(abs(lit));
                            if (it != lit2CardC.end() && it->second) {
                                conflictsIDs.push_back(it->second->addressID);   
                                std::shared_ptr<NodeEntry> updatedCC = addNode(NodeType::CardClause, it->second->value - minWeight, it->second->literals, it->second->conflict, it->second->constraint, it->second->linkedClauses, {});
                                updatedCardCIDs.push_back(updatedCC->addressID);
                                lit2CardC[abs(lit)] = updatedCC;
                                lit2Id[abs(lit)] = updatedCC->addressID;
                            }
                        }

                        for(auto lit: conflict) {
                            _mapWeight2Assum[_poids[lit]].erase( lit );
                            _poids.add(lit, -minWeight);
                            if(_poids[lit] == 0) {
                                if(_mapAssum2Card[ abs(lit) ].has_value()) {
                                    _litToRelax.push_back(lit);
                                }
                            } else {
                                _mapWeight2Assum[_poids[lit]].insert( lit );
                            }
                            assert(_poids[lit] >= 0);
                            if(_poids[lit] < minWeightToConsider) {
                                assum.erase(lit);
                            }
                        }

                        for(auto& l: conflict) {
                            l *= -1;
                        }
                        _cardToAdd.push_back( {conflict, minWeight} );
                        MonPrint("cost = ", cost, " + ", minWeight);

                        cost += minWeight;
                        std::shared_ptr<NodeEntry> newLbNode = addNode(NodeType::LowerBound, cost, {}, {}, -1, {}, {});
                        std::shared_ptr<NodeEntry> cardC = addNode(NodeType::CardClause, minWeight, {}, conflict, -1, {}, {});
                        confl2card[{conflict, minWeight}] = cardC;
                        assert(solver->solve(conflict) == 0);
                        addProofStep(RuleID::ConflictRelaxation, {{lbNode->addressID}, conflictsIDs}, {{newLbNode->addressID}, updatedSoftCIDs, updatedCardCIDs, {cardC->addressID}});
                        std::cout << "Cls:" << conflict.size() << std::endl;
                        size_t count = solver->getClauseCount();
                        std::cout << "HCs: " << count << std::endl;
                        lbNode = newLbNode;

                        if(cost == solutionCost) {
                            MonPrint("c UB == LB");
                            addProofStep(RuleID::OptimumFound, {{lbNode->addressID}}, {{ubNode->addressID}});
                            return true;
                        }
                        MonPrint(_mapWeight2Assum.rbegin()->first, " >= ", solutionCost, " - ", cost, " (", solutionCost - cost, ") ?");
                        if( _mapWeight2Assum.rbegin()->first >= solutionCost - cost) {
                            MonPrint("c Déchanchement de Haden !");
                            if(harden(assum)) {
                                assert(_mapWeight2Assum.size());
                                if(adapt_am1_VeryFastHeuristic()) {
                                    assum = initAssum(minWeightToConsider);
                                }
                            }
                        }
                    } else if(resultLastSolve == 1) { // SAT
                        if(_litToRelax.size()) {
                            for(auto lit: _litToRelax) {
                                auto newLit = relax(lit);
                                if(newLit.has_value()) {
                                    if( _poids[newLit.value()] >= minWeightToConsider ) {
                                        assum.insert(newLit.value());
                                    }
                                }
                            }
                            _litToRelax.clear();
                            assert( assum == initAssum(minWeightToConsider) );
                        } else {
                            ///////////////////
                            /// For harden via optimize
                            ///
                                if(_UBStrategy && toOptimize) {
                                    auto curSolution = solver->getSolution();
                                    auto curCost = LO.optimize( curSolution, std::min(0.1 * chronoLastOptimize.tacSec(), 60.0) );

                                    if(curCost < solutionCost) {
                                        solutionCost = curCost;
                                        solution = curSolution;

                                        std::shared_ptr<NodeEntry> newUbNode = addNode(NodeType::UpperBound, solutionCost, {}, {}, -1, {}, solution);
                                        addProofStep(RuleID::UpperBoundUpdate, {{lbNode->addressID}, {ubNode->addressID}}, {{newUbNode->addressID}});
                                        ubNode = newUbNode;
                                        if(harden(assum)) {
                                            assert(_mapWeight2Assum.size());

                                            if(adapt_am1_VeryFastHeuristic()) {
                                                assum = initAssum(minWeightToConsider);
                                            }
                                        }
                                    }
                                    chronoLastOptimize.tic();
                                }
                            ///
                            ////////////////
                            
                            while(_cardToAdd.size()) {
                                std::shared_ptr<CardIncremental_Lazy<EvalMaxSAT<SAT_SOLVER>>> card = std::make_shared<CardIncremental_Lazy<EvalMaxSAT<SAT_SOLVER>>>(this, std::get<0>(_cardToAdd.front()), 1);
                                size_t count = solver->getClauseCount();
                                std::cout << "HCs Before 1: " << count << std::endl;
                                int newAssumForCard = card->atMost(1);
                                count = solver->getClauseCount();
                                std::cout << "HCs before 2: " << count << std::endl;
                                if(newAssumForCard != 0) {
                                    assert( _poids[newAssumForCard] == 0 );

                                    _poids.set(newAssumForCard, std::get<1>(_cardToAdd.front()));
                                    _mapWeight2Assum[ std::get<1>(_cardToAdd.front()) ].insert(newAssumForCard);
                                    _mapAssum2Card[ abs(newAssumForCard) ] = LitCard(card, 1, std::get<1>(_cardToAdd.front()));
                                    std::vector<int> linkedClauseIDs = _mapAssum2Card[abs(newAssumForCard)]->getClauseAddressIDs();

                                    std::cout << "Card Weight" << _poids[newAssumForCard]<< std::endl;


                                    if( _poids[newAssumForCard] >= minWeightToConsider ) {
                                        assum.insert(newAssumForCard);
                                    }

                                    auto id = confl2card.find(_cardToAdd.front());
                                    if (id != confl2card.end()) {
                                        id->second->literals = std::vector<int>{newAssumForCard};
                                        id->second->constraint = 1;
                                        id->second->linkedClauses = linkedClauseIDs;
                                        lit2CardC[abs(newAssumForCard)] = id->second;
                                        lit2Id[abs(newAssumForCard)] = id->second->addressID;
                                    }
                                    
                                }
                                _cardToAdd.pop_front();
                            }
                            confl2card.clear();

                            break;
                        }
                    } else { // TIMEOUT
                        minWeightToConsider=1;
                        assum = initAssum(minWeightToConsider);
                        break;
                    }

                    if(_delayStrategy == false) {
                        break;
                    }

                    MonPrint("Limited SAT...");

                    chronoLastSolve.tic();
                    {
                        if(_mapWeight2Assum.size() <= 1) {
                            resultLastSolve = solver->solveWithTimeout(assum, 60);
                        } else {
                            resultLastSolve = solver->solve(assum);
                        }
                        //resultLastSolve = solver->solveLimited(assum, 10000);
                        //resultLastSolve = solver->solve(assum);
                        //resultLastSolve = solver->solveWithTimeout(assum, 60);

                        MonPrint("resultLastSolve = ", resultLastSolve);

                        if(resultLastSolve == 1) {
                            lastSatAssum = assum;
                        }
                    }
                    chronoLastSolve.pause(true);
                }

                for(auto lit: _litToRelax) {
                    auto newLit = relax(lit);
                    if(newLit.has_value()) {
                        if( _poids[newLit.value()] >= minWeightToConsider ) {
                            assum.insert(newLit.value());
                        }
                    }
                }
                _litToRelax.clear();

                for(auto c: _cardToAdd) {
                    std::shared_ptr<CardIncremental_Lazy<EvalMaxSAT<SAT_SOLVER>>> card = std::make_shared<CardIncremental_Lazy<EvalMaxSAT<SAT_SOLVER>>>(this, std::get<0>(c), 1);
                    int newAssumForCard = card->atMost(1);
                    if(newAssumForCard != 0) {
                        assert( _poids[newAssumForCard] == 0 );

                        _poids.set(newAssumForCard, std::get<1>(c));
                        _mapWeight2Assum[ std::get<1>(c) ].insert(newAssumForCard);
                        size_t count = solver->getClauseCount();
                        std::cout << "HCs before 3: " << count << std::endl;
                        _mapAssum2Card[ abs(newAssumForCard) ] = LitCard(card, 1, std::get<1>(c));
                        count = solver->getClauseCount();
                        std::cout << "HCs before 4: " << count << std::endl;
                        std::vector<int> linkedClauseIDs = _mapAssum2Card[abs(newAssumForCard)]->getClauseAddressIDs();
                        std::cout << "Card Weight" << _poids[newAssumForCard]<< std::endl;

                        if( _poids[newAssumForCard] >= minWeightToConsider ) {
                            assum.insert(newAssumForCard);
                        }

                        auto id = confl2card.find(c);
                        if (id != confl2card.end()) {
                            lit2Id[abs(newAssumForCard)] = id->second->addressID;
                            id->second->literals = std::vector<int>{newAssumForCard};
                            id->second->constraint = 1;
                            id->second->linkedClauses = linkedClauseIDs;
                            lit2CardC[abs(newAssumForCard)] = id->second;
                        } else {
                            std::cout << "c [Proof] Could not find conflict! " << newAssumForCard << std::endl;
                        }
                    }
                }
                confl2card.clear();
                _cardToAdd.clear();
            }
        }

        assert(false);
        return true;
    }

private:

    // NOTE: moves soft variables (assumptions) to hard constraints when their cost is 
    // too high compared to the current best known solution.
    int harden(std::set<int> &assum) {
        if(_mapWeight2Assum.size() == 0)
            return 0;
        if(_mapWeight2Assum.size()==1) {
            if(_mapWeight2Assum.begin()->first == 1) {
                return 0;
            }
        }

        int nbHarden = 0;

        // NOTE: highest weight that can still contribute to an improved solution.
        // NOTE: soft lit with weight => maxCostLit will be hardened
        t_weight maxCostLit = solutionCost - cost;

        while( _mapWeight2Assum.rbegin()->first >= maxCostLit ) {
            assert(_mapWeight2Assum.size());

            auto lits = _mapWeight2Assum.rbegin()->second;

            for(auto lit: lits) {
                assert( _poids[lit] >= maxCostLit );

                std::shared_ptr<NodeEntry> scNode = nullptr;
                if (lit2SoftC.find(lit) != lit2SoftC.end()) {
                    scNode = lit2SoftC[lit];
                } else if (lit2CardC.find(abs(lit)) != lit2CardC.end()) {
                    scNode = lit2CardC[abs(lit)];
                }
                assum.erase(lit);
                assert(scNode != nullptr);

                addClause({lit}, std::nullopt);

                addProofStep(RuleID::Hardening, {{lbNode->addressID}, {ubNode->addressID}, {scNode->addressID}}, {{latestHardC->addressID}});
                nbHarden++;
            }

            if(_mapWeight2Assum.size() == 1) {
                break;
            }

            if(_mapWeight2Assum.rbegin()->second.size() == 0) {
                _mapWeight2Assum.erase(prev(_mapWeight2Assum.end()));
            }
        }

        MonPrint("c NUMBER HARDEN : ", nbHarden);
        return nbHarden;
    }

    // NOTE: Takes a set of conflicting literals and tries to remove literals that do not
    // contribute to making the conflict unsatisfiable. Uses time constraints to control how much
    // effort is spent on mimization. Also sorts literals by weight. Checks if latest literals change result to SAT.
    double oneMinimize(std::vector<int>& conflict, double referenceTimeSec, unsigned int B=10, bool sort=true) {
        Chrono C;
        double minimize=0;
        double noMinimize=0;
        unsigned int nbRemoved=0;

        if(sort) {
            //if(isWeighted()) {
                std::sort(conflict.begin(), conflict.end(), [&](int litA, int litB){

                    assert(_poids[litA] >= 0);
                    assert(_poids[litB] >= 0);

                    if(_poids[ litA ] > _poids[ litB ])
                        return true;
                    if(_poids[ litA ] < _poids[ litB ]) {
                        return false;
                    }
                    return abs(litA) < abs(litB);
                });
            //}
        }
        if(conflict.size()==0) {
            return 0;
        }
        while( solver->solveLimited(conflict, 10*B, conflict.back()) == 0 ) {
            conflict.pop_back();
            minimize++;
            nbRemoved++;
            if(conflict.size()==0) {
                return 0;
            }

            if((C.tacSec() > referenceTimeSec*getTimeRefCoef())) {
                MonPrint("\t\tbreak minimize");
                return conflict.size() / (double)_poids[ conflict.back() ];
            }

        }

        t_weight weight = _poids[conflict.back()];
        assert(weight>0);
        //MaLib::MonRand::shuffle(conflict.begin(), conflict.end()-1);

        for(int i=conflict.size()-2; i>=0; i--) {
            switch(solver->solveLimited(conflict, B, conflict[i])) {
            case -1: // UNKNOW
                [[fallthrough]];
            case 1: // SAT
            {
                noMinimize++;
                break;
            }

            case 0: // UNSAT
                conflict[i] = conflict.back();
                conflict.pop_back();
                minimize++;
                nbRemoved++;
                break;

            default:
                assert(false);
            }

            if( C.tacSec() > referenceTimeSec*getTimeRefCoef() ) {
                break;
            }
        }

        return conflict.size() / (double)weight;
    }


    //////////////////////////////
    /// For extractAM
    ///
        void extractAM() {
            adapt_am1_exact();
            adapt_am1_FastHeuristicV7();
        }

        bool adapt_am1_exact() {
            Chrono chrono;
            unsigned int nbCliqueFound=0;
            std::vector<int> assumption;

            for(auto & [w, lits]: _mapWeight2Assum) {
                assert(w != 0);
                for(auto lit: lits) {
                    assert( _poids[lit] > 0 );
                    assumption.push_back(lit);
                }
            }

            if(assumption.size() > 30000) { // hyper paramétre
                MonPrint("skip");
                return false;
            }

            MonPrint("Create graph for searching clique...");
            unsigned int size = assumption.size();
            bool **conn = new bool*[size];
            for(unsigned int i=0; i<size; i++) {
                conn[i] = new bool[size];
                for(unsigned int x=0; x<size; x++)
                    conn[i][x] = false;
            }

            MonPrint("Create link in graph...");
            for(unsigned int i=0; i<size; ) {
                int lit1 = assumption[i];

                std::vector<int> prop;
                // If literal in assumptions has a value that is resolvable, get array of all the other literals that must have
                // a certain value in consequence, then link said literal to the opposite value of these other literals in graph
                
                if(solver->propagate(std::vector<int>({lit1}), prop)) {
                    for(int lit2: prop) {
                        for(unsigned int j=0; j<size; j++) {
                            if(j==i)
                                continue;
                            if(assumption[j] == -lit2) {
                                conn[i][j] = true;
                                conn[j][i] = true;
                            }
                        }
                    }
                    i++;
                } else { // No solution - Remove literal from the assumptions and add its opposite as a clause
                    // NOTE: Lit leads to an immediate contradiction, and thus we add -Lit as a hard clause

                    addClause({-lit1}, std::nullopt);

                    std::shared_ptr<NodeEntry> newLbNode = addNode(NodeType::LowerBound, cost, {}, {}, -1, {}, {});
                    std::vector<std::vector<int>> premises;
                    premises.push_back({lbNode->addressID});
                    premises.push_back({lit2Id[abs(lit1)]});
                    addProofStep(RuleID::UnsatisfiableLiteral, premises, {{newLbNode->addressID}, {latestHardC->addressID}});
                    lbNode = newLbNode;

                    assumption[i] = assumption.back();
                    assumption.pop_back();

                    for(unsigned int x=0; x<size; x++) {
                        conn[i][x] = false;
                        conn[x][i] = false;
                    }

                    size--;
                }
            }

            if(size == 0) {
                for(unsigned int i=0; i<size; i++) {
                    delete [] conn[i];
                }
                delete [] conn;
                return true;
            }

            std::vector<bool> active(size, true);
            for(;;) {
                int *qmax;
                int qsize=0;
                Maxclique md(conn, size, 0.025);
                md.mcqdyn(qmax, qsize, 100000);

                if(qsize <= 2) { // Hyperparametre: Taille minimal a laquelle arreter la methode exact
                    for(unsigned int i=0; i<size; i++) {
                        delete [] conn[i];
                    }
                    delete [] conn;
                    delete [] qmax;

                    MonPrint(nbCliqueFound, " cliques found in ", (chrono.tacSec()), "sec.");
                    return true;
                }
                nbCliqueFound++;

                {
                    //int newI=qmax[0];
                    std::vector<int> clause;

                    for (unsigned int i = 0; i < qsize; i++) {
                        int lit = assumption[qmax[i]];
                        active[qmax[i]] = false;
                        clause.push_back(lit);

                        for(unsigned int x=0; x<size; x++) {
                            conn[qmax[i]][x] = false;
                            conn[x][qmax[i]] = false;
                        }
                    }
                    auto newAssum = processAtMostOne(clause);
                    assert(qsize >= newAssum.size());

                    // NOTE: Replace old literals with new constrained ones.
                    for(unsigned int j=0; j<newAssum.size() ; j++) {
                        assumption[ qmax[j] ] = newAssum[j];
                        active[ qmax[j] ] = true;

                        std::vector<int> prop;
                        if(solver->propagate({newAssum[j]}, prop)) {
                            for(int lit2: prop) {
                                for(unsigned int k=0; k<size; k++) {
                                    if(active[k]) {
                                        if(assumption[k] == -lit2) {
                                            conn[qmax[j]][k] = true;
                                            conn[k][qmax[j]] = true;
                                        }
                                    }
                                }
                            }
                         } else {
                            // NOTE: Lit leads to an immediate contradiction, and thus we add -Lit as a hard clause
                            assert(solver->solve(std::vector<int>({newAssum[j]})) == false);
                            addClause({-newAssum[j]}, std::nullopt);
                            std::shared_ptr<NodeEntry> newLbNode = addNode(NodeType::LowerBound, cost, {}, {}, -1, {}, {});
                            std::vector<std::vector<int>> premises;
                            premises.push_back({lbNode->addressID});
                            premises.push_back({lit2Id[abs(newAssum[j])]});
                            addProofStep(RuleID::UnsatisfiableLiteral, premises, {{newLbNode->addressID}, {latestHardC->addressID}});
                            lbNode = newLbNode;
                         }
                    }
                }

                delete [] qmax;
            }

            assert(false);
        }

        // Harden soft vars in passed clique to then unrelax them via a new cardinality constraint
        std::vector<int> processAtMostOne(std::vector<int> clause) {
            std::vector<int> newAssum;

            while(clause.size() > 1) {

                assert([&](){
                    for(unsigned int i=0; i<clause.size(); i++) {
                        for(unsigned int j=i+1; j<clause.size(); j++) {
                            assert(solver->solve(std::vector<int>({clause[i], clause[j]})) == 0 );
                        }
                    }
                    return true;
                }());

                // NOTE: find the smallest weight among all literals in the clique,
                // because we need to subtract this weight from all literals, ensuring 
                // that at least one is chosen.
                auto saveClause = clause;
                auto w = _poids[ clause[0] ];
                assert(w > 0);

                for(unsigned int i=1; i<clause.size(); i++) {
                    if( w > _poids[ clause[i] ] ) {
                        w = _poids[ clause[i] ];
                    }
                }
                assert(w > 0);

                std::vector<int> conflictsIDs;
                std::vector<int> updatedSoftCIDs;
                for (int lit : saveClause) {
                    auto it = lit2SoftC.find(lit);
                    if (it != lit2SoftC.end() && it->second) {
                        conflictsIDs.push_back(it->second->addressID);   
                        std::shared_ptr<NodeEntry> updatedSC = addNode(NodeType::SoftClause, it->second->value - w, it->second->literals, it->second->conflict, -1, {}, {});
                        updatedSoftCIDs.push_back(updatedSC->addressID);
                        lit2SoftC[lit] = updatedSC;
                        lit2Id[lit] = updatedSC->addressID;
                    }
                }
                std::vector<int> updatedCardCIDs;
                for (int lit : saveClause) {
                    auto it = lit2CardC.find(abs(lit));
                    if (it != lit2CardC.end() && it->second) {
                        conflictsIDs.push_back(it->second->addressID);   
                        std::shared_ptr<NodeEntry> updatedCC = addNode(NodeType::CardClause, it->second->value - w, it->second->literals, it->second->conflict, it->second->constraint, it->second->linkedClauses, {});
                        updatedCardCIDs.push_back(updatedCC->addressID);
                        lit2CardC[abs(lit)] = updatedCC;
                        lit2Id[abs(lit)] = updatedCC->addressID;
                    }
                }

                cost += w * (t_weight)(saveClause.size()-1);
                assert(saveClause.size() > 1);

                int softLit = addClause(saveClause, w);
                
                newAssum.push_back(softLit);

                std::shared_ptr<NodeEntry> newLbNode = addNode(NodeType::LowerBound, cost, {}, {}, -1, {}, {});
                
                addProofStep(RuleID::CliqueRelaxation, {{lbNode->addressID}, conflictsIDs}, {{newLbNode->addressID}, updatedSoftCIDs, updatedCardCIDs, {latestHardC->addressID}, {latestSoftC->addressID}});
                lbNode = newLbNode;
                
                // NOTE: We now subtract w (chosen weight) from each literal's weight
                // some literals have weight 0, meaning they are "hardened"
                for(unsigned int i=0; i<clause.size(); ) {
                    assert( _poids[clause[i]] > 0 );
                    assert( _mapWeight2Assum[ _poids[ clause[i] ] ].count( clause[i] ) );
                    _mapWeight2Assum[ _poids[ clause[i] ] ].erase( clause[i] );

                    _poids.add( clause[i], -w );

                    assert( _poids[ clause[i] ] >= 0 );
                    if( _poids[ clause[i] ] == 0 ) {
                        std::cout << "Its happening here!" << std::endl;
                        relax( clause[i] );
                        clause[i] = clause.back();
                        clause.pop_back();
                    } else {
                        _mapWeight2Assum[ _poids[ clause[i] ] ].insert( clause[i] );
                        i++;
                    }
                }
                MonPrint("AM1: cost = ", cost, " + ", w * (t_weight)(saveClause.size()-1));

                assert(newAssum.back() != 0);
                assert( _poids[ newAssum.back() ] > 0 );
            }

            if( clause.size() ) {
                newAssum.push_back(clause[0]);
            }
            return newAssum;
        }

        void reduceCliqueV2(std::list<int> & clique) {
            if(_mapWeight2Assum.size() > 1) {
                clique.sort([&](int litA, int litB){
                    assert( _poids[ -litA ] > 0 );
                    assert( _poids[ -litB ] > 0 );

                    return _poids[ -litA ] < _poids[ -litB ];
                });
            }
            for(auto posImpliquant = clique.begin() ; posImpliquant != clique.end() ; ++posImpliquant) {
                auto posImpliquant2 = posImpliquant;
                for(++posImpliquant2 ; posImpliquant2 != clique.end() ; ) {
                    if(solver->solveLimited(std::vector<int>({-(*posImpliquant), -(*posImpliquant2)}), 10000) != 0) { // solve != UNSAT
                        posImpliquant2 = clique.erase(posImpliquant2);
                    } else {
                        ++posImpliquant2;
                    }
                }
            }
        }

        // NOTE: iterate over soft literals and propagate each literal.
        // NOTE: Detects pairwise conflicts using unit propagation only.
        // NOTE: No clique reduction, only pairwise checks.
        unsigned int adapt_am1_VeryFastHeuristic() {
            std::vector<int> prop;
            unsigned int nbCliqueFound=0;

            for(int VAR = 1; VAR<_poids.size(); VAR++) {
                if(_poids[VAR] == 0)
                    continue;
                assert(_poids[VAR] != 0);

                int LIT = _poids[VAR]>0?VAR:-VAR;
                prop.clear();

                if(solver->propagate({LIT}, prop)) {
                    if(prop.size() == 0)
                        continue;

                    for(auto litProp: prop) {
                        if(_poids[litProp] < 0) {
                            assert(solver->solve(std::vector<int>({-litProp, LIT})) == false);
                            processAtMostOne( {-litProp, LIT} );
                            nbCliqueFound++;
                            if(_poids[VAR] == 0)
                                break;
                        }
                    }
                } else {
                    nbCliqueFound++;
                    // NOTE: Setting LIT to true would lead to unsat, thus we add the inverse
                    addClause({-LIT}, std::nullopt);
                    std::shared_ptr<NodeEntry> newLbNode = addNode(NodeType::LowerBound, cost, {}, {}, -1, {}, {});
                    std::vector<std::vector<int>> premises;
                    premises.push_back({lbNode->addressID});
                    premises.push_back({lit2Id[abs(LIT)]});
                    addProofStep(RuleID::UnsatisfiableLiteral, premises, {{newLbNode->addressID}, {latestHardC->addressID}});
                    lbNode = newLbNode;
                }
            }

            return nbCliqueFound;
        }

        // NOTE: iterate over soft literals and propagate each literal.
        // NOTE: Builds a clique of conflicting literals and converts them into cardinality constraints.
        unsigned int adapt_am1_FastHeuristicV7() {
            MonPrint("adapt_am1_FastHeuristic : (_weight.size() = ", _poids.size(), " )");

            Chrono chrono;
            std::vector<int> prop;
            unsigned int nbCliqueFound=0;

            for(int VAR = 1; VAR<_poids.size(); VAR++) {
                if(_poids[VAR] == 0)
                    continue;

                assert(_poids[VAR] != 0);

                int LIT = _poids[VAR]>0?VAR:-VAR;
                prop.clear();
                if(solver->propagate({LIT}, prop)) {
                    if(prop.size() == 0)
                        continue;

                    std::list<int> clique;
                    for(auto litProp: prop) {
                        if(_poids[litProp] < 0) {
                            clique.push_back(litProp);
                            assert(solver->solve(std::vector<int>({-litProp, LIT})) == false);
                        }
                    }

                    if(clique.size() == 0)
                        continue;

                    reduceCliqueV2(clique); // retirer des elements pour que clique soit une clique

                    clique.push_back(-LIT);

                    if(clique.size() >= 2) {
                        nbCliqueFound++;

                        std::vector<int> clause;
                        for(auto lit: clique)
                            clause.push_back(-lit);

                        processAtMostOne(clause);
                    }
                } else {
                    nbCliqueFound++;
                    // NOTE: Setting LIT to true would lead to unsat, thus we add the inverse

                    addClause({-LIT}, std::nullopt);

                    std::shared_ptr<NodeEntry> newLbNode = addNode(NodeType::LowerBound, cost, {}, {}, -1, {}, {});
                    std::vector<std::vector<int>> premises;
                    premises.push_back({lbNode->addressID});
                    premises.push_back({lit2Id[abs(LIT)]});
                    addProofStep(RuleID::UnsatisfiableLiteral, premises, {{newLbNode->addressID}, {latestHardC->addressID}});
                    lbNode = newLbNode;
                }
            }

            MonPrint(nbCliqueFound, " cliques found in ", chrono);
            return nbCliqueFound;
        }
    ///
    /// End for extractAM
    ///////////////////////


public:

    std::vector<int> getVectorDifference(const std::vector<int>& larger, const std::vector<int>& smaller) {
        std::unordered_set<int> smallSet(smaller.begin(), smaller.end());
        std::vector<int> diff;

        for (int id : larger) {
            if (smallSet.find(id) == smallSet.end()) {
                diff.push_back(id);
            }
        }

        return diff;
    }

    // NOTE: Adds a weight to a literal in a Weighted MaxSAT problem. If the literal already has a weight, it updates it accordingly.
    void addWeight(int lit, long long weight) {
        assert(lit != 0);
        assert(weight != 0 && "Not an error, but it should not happen");
        if(weight < 0) {
            weight = -weight;
            lit = -lit;
        }

        while(abs(lit) >= _poids.size()) {
            newVar();
        }

        if( _poids[lit] == 0 ) {
            _poids.set(lit, weight);
            _mapWeight2Assum[weight].insert(lit);
        } else {
            long long prevWeight = _poids[lit];

            if( _poids[lit] > 0 ) {
                assert( _mapWeight2Assum[_poids[lit]].count( lit ) );
                _mapWeight2Assum[_poids[lit]].erase( lit );
                _poids.add(lit, weight);
                assert( _poids[lit] < 0 ? !_mapAssum2Card[lit].has_value() : true ); // If -lit becomes a soft var, it should not be a cardinality
            } else { 
                // NOTE: I am assuming that the weight can never be negative!
                assert( _mapWeight2Assum[_poids[-lit]].count( -lit ) );
                _mapWeight2Assum[_poids[-lit]].erase( -lit );
                cost += std::min(weight, _poids[-lit]);
                _poids.add(lit, weight);
                assert( _poids[-lit] > 0 ? !_mapAssum2Card[-lit].has_value() : true ); // If lit becomes a soft var, it should not be a cardinality
            }

            if(_poids[lit] != 0) {
                if(_poids[lit] > 0) {
                    _mapWeight2Assum[_poids[lit]].insert( lit );
                } else {
                    _mapWeight2Assum[-_poids[lit]].insert( -lit );
                }
            } else {
                relax(lit);
            }
        }
    }

private:

    // If a soft variable is not soft anymore, we have to check if this variable is a cardinality, in which case, we have to relax the cardinality.
    std::optional<int> relax(int lit) {
        assert(lit != 0);
        std::cout << "Relax: " << lit << std::endl;
        std::optional<int> newSoftVar;

        unsigned int var = abs(lit);

        // NOTE: if lit was used in an AtMost-k constraint, then we need to increase k by 1
        // NOTE: to do so, it introduces a new soft assumption (softVAR2)
        // NOTE: if it false, the new constraint is enforced and if it is true it is ignored
        if(_mapAssum2Card[var].has_value()) { // If there is a cardinality constraint associated to this soft var
            int forCard = _mapAssum2Card[ var ]->card->atMost( _mapAssum2Card[ var ]->atMost + 1 );

            if(forCard != 0) {
                if( _mapAssum2Card[abs(forCard)].has_value() == false ) {
                    int prevBound = _mapAssum2Card[var]->atMost;
                    int newBound = prevBound + 1;
                    std::vector<int> oldIDs = _mapAssum2Card[var]->card->getClauseIDsForBound(prevBound);
                    _mapAssum2Card[abs(forCard)] = LitCard(_mapAssum2Card[var]->card, newBound,  _mapAssum2Card[var]->initialWeight);
                    std::vector<int> newIDs = _mapAssum2Card[var]->card->getClauseIDsForBound(newBound);
                    assert( forCard == _mapAssum2Card[abs(forCard)]->getLit() );

                    std::vector<int> addedIDs = getVectorDifference(newIDs, oldIDs);
                    _poids.set(forCard, _mapAssum2Card[abs(forCard)]->initialWeight);
                    _mapWeight2Assum[_poids[forCard]].insert( forCard );
                    std::cout << "Totalizer Update" << std::endl;
                    std::cout << "Old Card Weight " << _poids[lit]<< std::endl;
                    std::cout << "New Card Weight " << _poids[forCard]<< std::endl;

                    std::shared_ptr<NodeEntry> oldCardNode = lit2CardC.at(var);
                    std::vector<int> cfl = oldCardNode->conflict;
                    std::shared_ptr<NodeEntry> newCardNode = addNode(NodeType::CardClause, _poids[forCard], {forCard}, cfl, newBound, addedIDs, {});
                    lit2CardC[abs(forCard)] = newCardNode;
                    lit2Id[abs(forCard)] = newCardNode->addressID;

                    addProofStep(RuleID::TotalizerUpdate, {{oldCardNode->addressID}}, {{newCardNode->addressID}});
                    newSoftVar = forCard;
                }
            }

            if(_poids[lit] == 0) {
                _mapAssum2Card[var].reset();
                std::shared_ptr<NodeEntry> cardNode = lit2CardC[var];
                addProofStep(RuleID::ZeroWeightCardinality, {{cardNode->addressID}}, {});
                lit2CardC.erase(var);
                lit2Id.erase(var);
            }
        }
        return newSoftVar;
    }

    // NOTE: Find the next lower weight by looking for the largest weight below minWeightToConsider.
    // NOTE: Only lower the weight if it's =< 50% of the previous weight
    // NOTE: This weight is then used to control the assumption selection.
    t_weight chooseNextMinWeight(t_weight minWeightToConsider=std::numeric_limits<t_weight>::max()) {
        auto previousWeight = minWeightToConsider;

        if(_mapWeight2Assum.size() <= 1) {
            return 1;
        }

        for(;;) {
            auto it = _mapWeight2Assum.lower_bound(minWeightToConsider);
            if(it == _mapWeight2Assum.begin()) {
                return 1;
            }
            --it;

            if(it == _mapWeight2Assum.end()) {
                assert(!"possible ?");
                return 1;
            }

            if( it->second.size() == 0 ) {
                _mapWeight2Assum.erase(it);

                if(_mapWeight2Assum.size() <= 1) {
                    return 1;
                }
            } else {
               auto it2 =it;
               it2--;
               if(it2 == _mapWeight2Assum.end()) {
                   MonPrint("minWeightToConsider == ", 1);
                   return 1;
               }

               /*
               if(it2->first < it->first * 0.1 ) {   // hyper paramétre
                   MonPrint("minWeightToConsider apres = ", it->first);
                   return it->first;
               }
               */

               if(it2->first < previousWeight * 0.5) {  // hyper paramétre
                   MonPrint("minWeightToConsider = ", it->first);
                   return it->first;
               }

               minWeightToConsider = it->first;
            }
        }

        assert(false);
        return 1;
    }

    ///////////////////////////
    /// Getter
    ///
        unsigned int nInputVars=0;
        public:
        void setNInputVars(unsigned int nInputVars) { // Only used to format the size of the solution
            this->nInputVars=nInputVars;
        }
        unsigned int nVars() {
            return _poids.size()-1;
            //return solver->nVars();
        }
        std::vector<bool> getSolution() {
            return std::vector<bool>(solution.begin(), solution.begin() + nInputVars + 1);
            std::vector<bool> res = solution;
            res.resize(nInputVars+1);
            return res;
        }
        t_weight getCost() {
            return solutionCost;
        }
    //
    /////////////////
};





#endif // EVALMAXSAT_SLK178903R_H

