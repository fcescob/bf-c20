// Exact finite boundary lemma checker. Run remotely, not on the workstation.
// No floating point, solver, graph-size bound, or sampled cases.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;

int pc(int x) { return __builtin_popcount((unsigned)x); }

struct DSU {
  array<int, 10> p;
  DSU() { iota(p.begin(), p.end(), 0); }
  int find(int x) { return p[x] == x ? x : p[x] = find(p[x]); }
  void join(int a, int b) { p[find(a)] = find(b); }
};

// Independent, direct definition: every cyclic arc between selected
// positions has odd edge-length. In particular the singleton arc is full.
bool good_arc(int mask, const vector<int>& order, int flags) {
  const int k = order.size();
  if (!mask) return false;
  for (int i = 0; i < k; ++i) if (mask & (1 << order[i])) {
    int j = i, parity = 0;
    do {
      parity ^= (j % 2 == 0) ? 1 : 1 ^ ((flags >> (j / 2)) & 1);
      j = (j + 1) % k;
    } while (!(mask & (1 << order[j])));
    if (parity != 1) return false;
  }
  return true;
}

bool good_prefix(int mask, int k, int flags) {
  int prefix = 0, first = -1, last = -1;
  for (int i = 0; i < k; ++i) {
    if (mask & (1 << i)) {
      if (first == -1) first = prefix;
      else if (last == prefix) return false;
      last = prefix;
    }
    prefix ^= (i % 2 == 0) ? 1 : 1 ^ ((flags >> (i / 2)) & 1);
  }
  assert(prefix == 1);
  return first != -1 && first == last;
}

int rotate_flags(int w, int n) {
  return ((w << 1) & ((1 << n) - 1)) | (w >> (n - 1));
}
bool rotation_minimal(int w, int n) {
  int v = w;
  for (int i = 1; i < n; ++i) { v = rotate_flags(v, n); if (v < w) return false; }
  return true;
}

array<int, 4> split_four(int k, const array<vector<int>, 8>& cgood,
                         const array<uint8_t, 1024>& dgood) {
  const int full = (1 << k) - 1;
  auto with_singles = [&](int a, int b) {
    array<int, 4> p{a, 0, 0, 0}; int j = 1;
    if (b) p[j++] = b;
    for (int rem = full ^ (a | b); rem; rem &= rem - 1) p[j++] = rem & -rem;
    assert(j == 4);
    return p;
  };
  if (k == 4) return {1, 2, 4, 8};
  for (int s : cgood[k - 3]) if (dgood[s]) return with_singles(s, 0);
  if (k == 6) return {0, 0, 0, 0};
  vector<int> triples;
  for (int s : cgood[3]) if (dgood[s]) triples.push_back(s);
  if (k == 10)
    for (int a : cgood[5]) if (dgood[a])
      for (int b : triples) if (!(a & b)) return with_singles(a, b);
  for (size_t i = 0; i < triples.size(); ++i)
    for (size_t j = i + 1; j < triples.size(); ++j) {
      int a = triples[i], b = triples[j];
      if (a & b) continue;
      if (k == 8) return with_singles(a, b);
      for (size_t l = j + 1; l < triples.size(); ++l) {
        int c = triples[l];
        if (!((a | b) & c)) return {a, b, c, full ^ (a | b | c)};
      }
    }
  return {0, 0, 0, 0};
}

int main() {
  ofstream cert("out/partitions.bin", ios::binary);
  assert(cert);
  for (int k : {4, 6, 8, 10}) {
    const int n = k / 2, full = (1 << k) - 1;
    vector<int> c(k), d(k), flags, reps;
    iota(c.begin(), c.end(), 0); d = c;
    array<array<vector<int>, 8>, 32> cg;
    array<vector<int>, 32> local_good;
    for (int w = 0; w < (1 << n); ++w) if (pc(w) % 2) {
      flags.push_back(w);
      if (rotation_minimal(w, n)) reps.push_back(w);
      for (int s = 1; s <= full; ++s) if (pc(s) % 2 && pc(s) <= k - 3) {
        bool ok = good_prefix(s, k, w);
        assert(ok == good_arc(s, c, w));
        if (ok) { cg[w][pc(s)].push_back(s); local_good[w].push_back(s); }
      }
    }
    uint64_t orders = 0, total = 0, even = 0, partitioned = 0;
    do {
      DSU alpha;
      for (int j = 0; j < k; j += 2) { alpha.join(j, j + 1); alpha.join(d[j], d[j + 1]); }
      bool connected = true;
      for (int j = 1; j < k; ++j) if (alpha.find(j) != alpha.find(0)) connected = false;
      if (!connected) continue;
      ++orders;
      DSU mu;
      for (int j = 0; j < n; ++j) {
        int a = 2 * j + 1, b = (a + 1) % k;
        mu.join(a, b); mu.join(d[a], d[b]);
      }
      array<int, 10> cm{}, dm{};
      for (int j = 0; j < n; ++j) {
        cm[mu.find(2 * j + 1)] |= 1 << j;
        dm[mu.find(d[2 * j + 1])] |= 1 << j;
      }
      array<int, 1024> perm{};
      for (int s = 1; s <= full; ++s) {
        int bit = __builtin_ctz((unsigned)s);
        perm[s] = perm[s & (s - 1)] | (1 << d[bit]);
      }
      array<array<uint8_t, 1024>, 32> dg{};
      for (int df : flags) for (int s : local_good[df]) dg[df][perm[s]] = 1;
      for (int cf : reps) for (int df : flags) {
        ++total;
        bool is_even = true;
        for (int r = 0; r < k; ++r)
          if (pc(cf & cm[r]) % 2 != pc(df & dm[r]) % 2) is_even = false;
        if (is_even) { ++even; continue; }
        auto part = split_four(k, cg[cf], dg[df]);
        if (!part[0]) {
          cout << "FAIL k=" << k << " cf=" << cf << " df=" << df << " D=";
          for (int x : d) cout << x << ',';
          cout << "\ncounts orders=" << orders << " total=" << total
               << " even=" << even << " partitioned=" << partitioned << endl;
          return 2;
        }
        int seen = 0;
        for (int s : part) {
          assert(!(seen & s)); seen |= s;
          assert(pc(s) % 2);
          assert(good_arc(s, c, cf) && good_arc(s, d, df));
          uint16_t v = s;
          cert.put(char(v & 255)); cert.put(char(v >> 8));
        }
        assert(seen == full);
        ++partitioned;
      }
    } while (next_permutation(d.begin() + 1, d.end()));
    uint64_t a = 1;
    for (int j = 1; j < n; ++j) a *= 2 * j;
    assert(orders == a * a);
    assert(total == orders * flags.size() * reps.size());
    assert(even + partitioned == total);
    cout << "PASS k=" << k << " orders=" << orders << " total=" << total
         << " even=" << even << " partitioned=" << partitioned << " reps=";
    for (int x : reps) cout << x << ',';
    cout << endl;
  }
  cert.close();
  cout << "COMPLETE: all normalized boundary states checked" << endl;
}
