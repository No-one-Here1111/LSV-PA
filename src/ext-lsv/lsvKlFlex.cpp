// PA2: KL cut enumeration and flexibility computation
//   lsv_kl_flex <k> <l>
#include "base/abc/abc.h"
#include "base/main/main.h"
#include "base/main/mainInt.h"
#include "sat/bsat/satSolver.h"

#include <algorithm>
#include <cstdio>
#include <cstdint>
#include <cstdlib>
#include <set>
#include <utility>
#include <vector>

namespace {

typedef std::vector<int> Cut;  // sorted node IDs

struct KlResult {
  std::vector<int> roots;
  Cut leaves;
};

class KlFlex {
 public:
  KlFlex(Abc_Ntk_t* pNtk, int k, int l) : pNtk_(pNtk), k_(k), l_(l) {}
  void Run();

 private:
  // ---------- network helpers ----------
  bool IsAnd(Abc_Obj_t* p) const { return Abc_ObjIsNode(p) && !Abc_AigNodeIsConst(p); }
  bool IsConst(Abc_Obj_t* p) const { return Abc_AigNodeIsConst(p); }
  Abc_Obj_t* Obj(int id) const { return Abc_NtkObj(pNtk_, id); }
  int NewStamp() {
    if (++stamp_ == 0x7fffffff) {
      std::fill(markU_.begin(), markU_.end(), 0);
      std::fill(markV_.begin(), markV_.end(), 0);
      std::fill(markI_.begin(), markI_.end(), 0);
      std::fill(markR_.begin(), markR_.end(), 0);
      std::fill(markF_.begin(), markF_.end(), 0);
      stamp_ = 1;
    }
    return stamp_;
  }

  // ---------- step 1 ----------
  void EnumerateCuts();
  void Cone(int root, const Cut& c, std::vector<int>& out);
  void Search(int lastFree, int depth, int curSum, const Cut& curU);
  bool FindExit(int& w, int& f);
  void TryAdd(int idx, int nextLastFree, int depth, int curSum, const Cut& curU);
  void Evaluate(const Cut& U);
  int Validate(const std::vector<int>& V, const Cut& U);
  bool FreeReach(int id);

  // ---------- step 2 ----------
  void ComputeFlex(const KlResult& r);

  Abc_Ntk_t* pNtk_;
  int k_, l_;
  int nObjs_ = 0;
  std::vector<int> topo_;  // AND node IDs, fanins before fanouts
  std::vector<std::vector<Cut>> cuts_;  // all (minimal) cuts per node, incl. trivial
  struct Pair {
    int v, ci, vol;
    std::vector<int> cone;  // root + interior nodes of cone(v, cut)
  };
  std::vector<Pair> pairs_;   // all (root, non-trivial cut), sorted by volume (descending)
  std::vector<int> coverCnt_;  // how many chosen cones contain each node
  std::vector<int> leafCnt_;   // how many chosen cuts contain each node
  std::vector<char> isRootNow_;
  std::vector<std::vector<int>> pairsOf_;     // pair indices with root v
  std::vector<std::vector<int>> containing_;  // pair indices whose cone contains a node
  std::vector<char> isPoDriver_;
  std::vector<int> rNodes_;  // nodes covered by the chosen cones

  std::vector<int> roots_;  // current root stack in Search
  int best_ = 0;
  std::vector<KlResult> results_;
  std::set<std::pair<std::vector<int>, Cut>> seen_;

  int stamp_ = 0;
  std::vector<int> markU_, markV_, markI_, markR_, markF_;
  std::vector<char> freeVal_;
};

static bool MergeCuts(const Cut& a, const Cut& b, int k, Cut& out) {
  out.clear();
  size_t i = 0, j = 0;
  while (i < a.size() || j < b.size()) {
    int x;
    if (j == b.size() || (i < a.size() && a[i] < b[j]))
      x = a[i++];
    else if (i == a.size() || b[j] < a[i])
      x = b[j++];
    else
      x = a[i++], j++;
    out.push_back(x);
    if ((int)out.size() > k) return false;
  }
  return true;
}

static bool IsSubset(const Cut& a, const Cut& b) {  // a subset of b
  return std::includes(b.begin(), b.end(), a.begin(), a.end());
}

void KlFlex::EnumerateCuts() {
  nObjs_ = Abc_NtkObjNumMax(pNtk_);
  cuts_.assign(nObjs_, {});
  markU_.assign(nObjs_, 0);
  markV_.assign(nObjs_, 0);
  markI_.assign(nObjs_, 0);
  markR_.assign(nObjs_, 0);
  markF_.assign(nObjs_, 0);
  freeVal_.assign(nObjs_, 0);

  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachPi(pNtk_, pObj, i) cuts_[Abc_ObjId(pObj)].push_back(Cut{(int)Abc_ObjId(pObj)});
  Abc_Obj_t* pConst = Abc_AigConst1(pNtk_);
  if (pConst) cuts_[Abc_ObjId(pConst)].push_back(Cut{});  // constant: no leaf needed

  Vec_Ptr_t* vNodes = Abc_NtkDfs(pNtk_, 1);
  Vec_PtrForEachEntry(Abc_Obj_t*, vNodes, pObj, i) {
    if (!IsAnd(pObj)) continue;
    topo_.push_back(Abc_ObjId(pObj));
  }
  Vec_PtrFree(vNodes);

  Cut tmp;
  for (int id : topo_) {
    Abc_Obj_t* p = Obj(id);
    const auto& c0 = cuts_[Abc_ObjFaninId0(p)];
    const auto& c1 = cuts_[Abc_ObjFaninId1(p)];
    std::vector<Cut> cand;
    for (const Cut& a : c0)
      for (const Cut& b : c1)
        if (MergeCuts(a, b, k_, tmp)) cand.push_back(tmp);
    std::sort(cand.begin(), cand.end(),
              [](const Cut& x, const Cut& y) { return x.size() != y.size() ? x.size() < y.size() : x < y; });
    cand.erase(std::unique(cand.begin(), cand.end()), cand.end());
    // remove dominated cuts (strict supersets of another cut)
    std::vector<Cut> kept;
    for (const Cut& c : cand) {
      bool dom = false;
      for (const Cut& d : kept)
        if (d.size() < c.size() && IsSubset(d, c)) { dom = true; break; }
      if (!dom) kept.push_back(c);
    }
    auto& out = cuts_[id];
    out.push_back(Cut{id});  // trivial cut
    for (Cut& c : kept) out.push_back(std::move(c));
  }
}

// nodes in the cone of root bounded by c (root included, leaves excluded)
void KlFlex::Cone(int root, const Cut& c, std::vector<int>& out) {
  int st = NewStamp();
  for (int x : c) markU_[x] = st;
  out.assign(1, root);
  markI_[root] = st;
  for (size_t h = 0; h < out.size(); h++) {
    Abc_Obj_t* p = Obj(out[h]);
    int f[2] = {Abc_ObjFaninId0(p), Abc_ObjFaninId1(p)};
    for (int fi : f) {
      if (markU_[fi] == st || markI_[fi] == st) continue;
      if (!IsAnd(Obj(fi))) continue;
      markI_[fi] = st;
      out.push_back(fi);
    }
  }
}

bool KlFlex::FreeReach(int id) {
  // does id have a path to a PI avoiding all nodes marked in markU_ (id itself is not a leaf)?
  if (markF_[id] == stamp_) return freeVal_[id];
  markF_[id] = stamp_;
  Abc_Obj_t* p = Obj(id);
  bool res = false;
  if (Abc_ObjIsPi(p)) {
    res = true;
  } else if (IsAnd(p)) {
    int f[2] = {Abc_ObjFaninId0(p), Abc_ObjFaninId1(p)};
    for (int fi : f)
      if (markU_[fi] != stamp_ && FreeReach(fi)) { res = true; break; }
  }
  freeVal_[id] = res;
  return res;
}

// returns size of KL cut (U,V), or -1 if it violates (K1)-(K4)
int KlFlex::Validate(const std::vector<int>& V, const Cut& U) {
  int st = NewStamp();
  for (int u : U) markU_[u] = st;
  for (int v : V) {
    if (markU_[v] == st) return -1;
    markV_[v] = st;
  }
  // (K2) traversal from roots, collect interior
  std::vector<int> interior, stk;
  for (int v : V) stk.push_back(v);
  // markI_: visited (interior or root expanded); markR_: leaf reached
  for (int v : V) markI_[v] = st;
  while (!stk.empty()) {
    int id = stk.back();
    stk.pop_back();
    Abc_Obj_t* p = Obj(id);
    int f[2] = {Abc_ObjFaninId0(p), Abc_ObjFaninId1(p)};
    for (int fi : f) {
      if (markU_[fi] == st) { markR_[fi] = st; continue; }
      if (markI_[fi] == st) continue;
      Abc_Obj_t* pf = Obj(fi);
      if (Abc_ObjIsPi(pf)) return -1;  // (K2) violated
      if (IsConst(pf)) continue;
      markI_[fi] = st;
      interior.push_back(fi);
      stk.push_back(fi);
    }
  }
  // (K3)
  for (int u : U) {
    if (markR_[u] != st) return -1;
    Abc_Obj_t* p = Obj(u);
    if (Abc_ObjIsPi(p)) continue;
    bool ok = false;
    int f[2] = {Abc_ObjFaninId0(p), Abc_ObjFaninId1(p)};
    for (int fi : f)
      if (markU_[fi] != st && FreeReach(fi)) { ok = true; break; }
    if (!ok) return -1;
  }
  // (K4)
  for (int w : interior) {
    Abc_Obj_t* p = Obj(w);
    Abc_Obj_t* pFo;
    int j;
    Abc_ObjForEachFanout(p, pFo, j) {
      if (Abc_ObjIsCo(pFo)) return -1;
      if (markI_[Abc_ObjId(pFo)] != st) return -1;  // markI_ covers interior and roots
    }
  }
  return (int)V.size() + (int)interior.size();
}

void KlFlex::Evaluate(const Cut& U) {
  std::vector<int> V(roots_);
  std::sort(V.begin(), V.end());
  auto key = std::make_pair(V, U);
  if (!seen_.insert(key).second) return;
  int sz = Validate(V, U);
  if (sz < 0 || sz < best_) return;
  if (sz > best_) {
    best_ = sz;
    results_.clear();
  }
  results_.push_back(KlResult{V, U});
}

// Search over sets of (root, cut) pairs.
//
// Canonical form: for a KL cut (U,V), let L_v be the leaves that root v
// reaches without passing another leaf. L_v is a minimal cut of v (so it is
// among the enumerated cuts), U is the union of the L_v, and cone(v, L_v)
// contains no leaf. Hence we only combine pairs whose cones avoid all chosen
// leaves; this condition is monotone, so violating branches are pruned. In
// canonical form R = union of the cones is exactly roots + interior, so its
// size is the size of the cut, and each further pair adds at most its volume.
//
// (K4) drives the branching: an "exit" is a non-root node w of R that drives
// a PO or has a fanout f outside R. In the final cut, w must be a root, or f
// must lie in the cone of another chosen pair. So while an exit exists, the
// next pair is one of these fixers (complete, since the final pair set must
// contain one). Without exits, the current set is a candidate, and any pair
// may be added (in increasing index order to avoid permutations).

// finds the exit with the fewest fixers; f = -1 if w drives a PO
bool KlFlex::FindExit(int& w, int& f) {
  size_t bestCnt = SIZE_MAX;
  for (int x : rNodes_) {
    if (isRootNow_[x]) continue;
    if (isPoDriver_[x]) {
      if (pairsOf_[x].size() < bestCnt) bestCnt = pairsOf_[x].size(), w = x, f = -1;
      continue;
    }
    Abc_Obj_t* pFo;
    int j;
    Abc_ObjForEachFanout(Obj(x), pFo, j) {
      int y = Abc_ObjId(pFo);
      if (coverCnt_[y]) continue;
      size_t cnt = pairsOf_[x].size() + containing_[y].size();
      if (cnt < bestCnt) bestCnt = cnt, w = x, f = y;
    }
  }
  return bestCnt != SIZE_MAX;
}

void KlFlex::TryAdd(int idx, int nextLastFree, int depth, int curSum, const Cut& curU) {
  const Pair& pr = pairs_[idx];
  int v = pr.v;
  if (isRootNow_[v]) return;
  const Cut& cut = cuts_[v][pr.ci];
  for (int x : cut)  // a new leaf inside a chosen cone (incl. a root)
    if (coverCnt_[x]) return;
  for (int w : pr.cone)  // the new cone contains a chosen leaf
    if (leafCnt_[w]) return;
  Cut newU;
  if (!MergeCuts(curU, cut, k_, newU)) return;
  size_t rSize = rNodes_.size();
  for (int x : cut) leafCnt_[x]++;
  for (int w : pr.cone)
    if (coverCnt_[w]++ == 0) rNodes_.push_back(w);
  isRootNow_[v] = 1;
  roots_.push_back(v);
  Search(nextLastFree, depth + 1, curSum + (int)(rNodes_.size() - rSize), newU);
  roots_.pop_back();
  isRootNow_[v] = 0;
  for (int w : pr.cone) coverCnt_[w]--;
  for (int x : cut) leafCnt_[x]--;
  rNodes_.resize(rSize);
}

void KlFlex::Search(int lastFree, int depth, int curSum, const Cut& curU) {
  int remain = l_ - depth;
  int w = -1, f = -1;
  if (depth > 0 && FindExit(w, f)) {
    // Canonical order: each free step adds the smallest-index pair of the
    // target set that is still missing, so every pair still to be added
    // (free or forced) has an index > lastFree, i.e. volume <= cap.
    int cap = lastFree >= 0 ? pairs_[lastFree].vol : pairs_[0].vol;
    if (remain == 0 || curSum + remain * cap < best_) return;
    std::vector<int> cand(pairsOf_[w]);
    if (f >= 0) cand.insert(cand.end(), containing_[f].begin(), containing_[f].end());
    for (int idx : cand)
      if (idx > lastFree && curSum + pairs_[idx].vol + (remain - 1) * cap >= best_)
        TryAdd(idx, lastFree, depth, curSum, curU);
    return;
  }
  if (depth > 0 && curSum >= best_) Evaluate(curU);
  if (remain == 0) return;
  for (int i = lastFree + 1; i < (int)pairs_.size(); i++) {
    if (curSum + remain * pairs_[i].vol < best_) return;  // later pairs are not larger
    TryAdd(i, i, depth, curSum, curU);
  }
}

void KlFlex::ComputeFlex(const KlResult& r) {
  const std::vector<int>& V = r.roots;
  const Cut& U = r.leaves;
  int m = V.size(), n = U.size();

  std::vector<char> isRoot(nObjs_, 0), inTfo(nObjs_, 0), need(nObjs_, 0);
  for (int v : V) isRoot[v] = 1;
  // transitive fanout of the roots (excluding the roots unless reached from another root)
  for (int id : topo_) {
    Abc_Obj_t* p = Obj(id);
    int f0 = Abc_ObjFaninId0(p), f1 = Abc_ObjFaninId1(p);
    if (isRoot[f0] || inTfo[f0] || isRoot[f1] || inTfo[f1]) inTfo[id] = 1;
  }
  auto changed = [&](int id) { return isRoot[id] || inTfo[id]; };

  // relevant POs and needed logic (TFI of relevant POs and leaves)
  std::vector<Abc_Obj_t*> relPos;
  std::vector<int> stk;
  Abc_Obj_t* pObj;
  int i;
  Abc_NtkForEachPo(pNtk_, pObj, i) {
    int d = Abc_ObjFaninId0(pObj);
    if (changed(d)) {
      relPos.push_back(pObj);
      stk.push_back(d);
    }
  }
  for (int u : U) stk.push_back(u);
  while (!stk.empty()) {
    int id = stk.back();
    stk.pop_back();
    if (need[id]) continue;
    need[id] = 1;
    Abc_Obj_t* p = Obj(id);
    if (IsAnd(p)) {
      stk.push_back(Abc_ObjFaninId0(p));
      stk.push_back(Abc_ObjFaninId1(p));
    }
  }

  // variables
  int nVars = 0;
  std::vector<int> varC(nObjs_, -1), varP(nObjs_, -1);
  for (int id = 0; id < nObjs_; id++)
    if (need[id]) varC[id] = nVars++;
  for (int v : V) varP[v] = nVars++;  // new PIs p_j
  for (int id : topo_)
    if (need[id] && inTfo[id] && !isRoot[id]) varP[id] = nVars++;
  auto litC = [&](int id, int c) { return Abc_Var2Lit(varC[id], c); };
  auto litP = [&](int id, int c) { return Abc_Var2Lit(changed(id) ? varP[id] : varC[id], c); };

  sat_solver* pSat = sat_solver_new();
  sat_solver_setnvars(pSat, nVars + (int)relPos.size() + 1);
  lit cl[3];
  Abc_Obj_t* pConst = Abc_AigConst1(pNtk_);
  if (pConst && need[Abc_ObjId(pConst)]) {
    cl[0] = litC(Abc_ObjId(pConst), 0);
    sat_solver_addclause(pSat, cl, cl + 1);
  }
  auto addAnd = [&](lit y, lit a, lit b) {
    cl[0] = lit_neg(y), cl[1] = a;
    sat_solver_addclause(pSat, cl, cl + 2);
    cl[0] = lit_neg(y), cl[1] = b;
    sat_solver_addclause(pSat, cl, cl + 2);
    cl[0] = y, cl[1] = lit_neg(a), cl[2] = lit_neg(b);
    sat_solver_addclause(pSat, cl, cl + 3);
  };
  for (int id : topo_) {
    if (!need[id]) continue;
    Abc_Obj_t* p = Obj(id);
    int f0 = Abc_ObjFaninId0(p), f1 = Abc_ObjFaninId1(p);
    int c0 = Abc_ObjFaninC0(p), c1 = Abc_ObjFaninC1(p);
    addAnd(litC(id, 0), litC(f0, c0), litC(f1, c1));
    if (inTfo[id] && !isRoot[id]) addAnd(Abc_Var2Lit(varP[id], 0), litP(f0, c0), litP(f1, c1));
  }
  int varMu = nVars + (int)relPos.size();
  std::vector<lit> orCl{Abc_Var2Lit(varMu, 1)};
  for (size_t j = 0; j < relPos.size(); j++) {
    Abc_Obj_t* po = relPos[j];
    int d = Abc_ObjFaninId0(po), c = Abc_ObjFaninC0(po);
    lit a = litC(d, c), b = litP(d, c), x = Abc_Var2Lit(nVars + (int)j, 0);
    // x -> (a xor b)
    cl[0] = lit_neg(x), cl[1] = a, cl[2] = b;
    sat_solver_addclause(pSat, cl, cl + 3);
    cl[0] = lit_neg(x), cl[1] = lit_neg(a), cl[2] = lit_neg(b);
    sat_solver_addclause(pSat, cl, cl + 3);
    orCl.push_back(x);
  }
  // mu -> OR(x_j)
  sat_solver_addclause(pSat, orCl.data(), orCl.data() + orCl.size());

  for (size_t j = 0; j < V.size(); j++) printf("%d%s", V[j], j + 1 < V.size() ? " " : ": ");
  for (size_t j = 0; j < U.size(); j++) printf("%d%s", U[j], j + 1 < U.size() ? " " : ":");

  unsigned long long full = (m >= 6) ? ~0ULL : ((1ULL << (1u << m)) - 1);
  // For each u: enumerate the root values c that some x with U(x) = u can
  // distinguish (SAT with p free and mu = 1), blocking each found c with a
  // clause guarded by a per-u activation variable. One UNSAT call ends the
  // loop, instead of one UNSAT proof per allowed c.
  int nTotal = varMu + 1;
  std::vector<lit> assume(n + 2), block;
  for (int u = 0; u < (1 << n); u++) {
    for (int j = 0; j < n; j++) assume[j] = litC(U[j], !((u >> (n - 1 - j)) & 1));
    unsigned long long mask = full;
    int res = sat_solver_solve(pSat, assume.data(), assume.data() + n, 0, 0, 0, 0);
    if (res == l_True && !relPos.empty()) {  // u produced and roots observable
      int act = nTotal++;
      sat_solver_setnvars(pSat, nTotal);
      assume[n] = Abc_Var2Lit(varMu, 0);
      assume[n + 1] = Abc_Var2Lit(act, 0);
      // the original root value c0 (fixed by u) is always allowed: block it
      // up front, so the solver never has to prove that forcing c0 is harmless
      block.assign(1, Abc_Var2Lit(act, 1));
      for (int j = 0; j < m; j++)
        block.push_back(Abc_Var2Lit(varP[V[j]], sat_solver_var_value(pSat, varC[V[j]])));
      sat_solver_addclause(pSat, block.data(), block.data() + block.size());
      while (sat_solver_solve(pSat, assume.data(), assume.data() + n + 2, 0, 0, 0, 0) == l_True) {
        int c = 0;
        block.assign(1, Abc_Var2Lit(act, 1));
        for (int j = 0; j < m; j++) {
          int val = sat_solver_var_value(pSat, varP[V[j]]);
          c = (c << 1) | val;
          block.push_back(Abc_Var2Lit(varP[V[j]], val));  // p_j != val
        }
        mask &= ~(1ULL << c);
        sat_solver_addclause(pSat, block.data(), block.data() + block.size());
      }
      lit off = Abc_Var2Lit(act, 1);  // retire the blocking clauses of this u
      sat_solver_addclause(pSat, &off, &off + 1);
    }
    printf(" %llX", mask);
  }
  printf("\n");
  sat_solver_delete(pSat);
}

void KlFlex::Run() {
  EnumerateCuts();
  for (int id : topo_)
    for (int c = 1; c < (int)cuts_[id].size(); c++) {
      Pair pr;
      pr.v = id, pr.ci = c;
      Cone(id, cuts_[id][c], pr.cone);
      pr.vol = pr.cone.size();
      pairs_.push_back(std::move(pr));
    }
  std::sort(pairs_.begin(), pairs_.end(), [](const Pair& a, const Pair& b) {
    if (a.vol != b.vol) return a.vol > b.vol;
    return a.v != b.v ? a.v < b.v : a.ci < b.ci;
  });
  pairsOf_.assign(nObjs_, {});
  containing_.assign(nObjs_, {});
  for (int i = 0; i < (int)pairs_.size(); i++) {
    pairsOf_[pairs_[i].v].push_back(i);
    for (int w : pairs_[i].cone) containing_[w].push_back(i);
  }
  isPoDriver_.assign(nObjs_, 0);
  {
    Abc_Obj_t* pPo;
    int i;
    Abc_NtkForEachPo(pNtk_, pPo, i) isPoDriver_[Abc_ObjFaninId0(pPo)] = 1;
  }
  coverCnt_.assign(nObjs_, 0);
  leafCnt_.assign(nObjs_, 0);
  isRootNow_.assign(nObjs_, 0);
  best_ = 1;  // any KL cut has size >= 1
  Search(-1, 0, 0, Cut{});
  if (results_.empty()) return;
  std::sort(results_.begin(), results_.end(), [](const KlResult& a, const KlResult& b) {
    return a.roots != b.roots ? a.roots < b.roots : a.leaves < b.leaves;
  });
  for (const auto& r : results_) ComputeFlex(r);
}

}  // namespace

int Lsv_CommandKlFlex(Abc_Frame_t* pAbc, int argc, char** argv) {
  Abc_Ntk_t* pNtk = Abc_FrameReadNtk(pAbc);
  int c;
  Extra_UtilGetoptReset();
  while ((c = Extra_UtilGetopt(argc, argv, "h")) != EOF) {
    switch (c) {
      case 'h':
      default:
        goto usage;
    }
  }
  if (argc - globalUtilOptind != 2) goto usage;
  if (!pNtk) {
    Abc_Print(-1, "Empty network.\n");
    return 1;
  }
  if (!Abc_NtkIsStrash(pNtk)) {
    Abc_Print(-1, "The network is not an AIG. Run \"strash\" first.\n");
    return 1;
  }
  {
    int k = atoi(argv[globalUtilOptind]);
    int l = atoi(argv[globalUtilOptind + 1]);
    if (k < 1 || l < 1 || k > 16 || l > 6) {
      Abc_Print(-1, "Invalid k or l.\n");
      return 1;
    }
    KlFlex solver(pNtk, k, l);
    solver.Run();
  }
  return 0;

usage:
  Abc_Print(-2, "usage: lsv_kl_flex [-h] <k> <l>\n");
  Abc_Print(-2, "\t        enumerates maximum KL cuts and prints their flexibility\n");
  Abc_Print(-2, "\t-h    : print the command usage\n");
  return 1;
}
