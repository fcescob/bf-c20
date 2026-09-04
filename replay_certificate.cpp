// Independent replay: no partition search, prefix-field test, or DSU.
// The case generator enumerates every labelled D-order starting at 0.
#include <algorithm>
#include <array>
#include <cassert>
#include <cstdint>
#include <fstream>
#include <iostream>
#include <numeric>
#include <vector>
using namespace std;

int parity(int x) { int p = 0; while (x) { p ^= 1; x &= x - 1; } return p; }
bool connected(int k, const vector<int>& d) {
  array<int, 10> a{}, seen{};
  for (int i = 0; i < k; i += 2) { a[d[i]] = d[i + 1]; a[d[i + 1]] = d[i]; }
  vector<int> todo{0}; seen[0] = 1;
  for (size_t i = 0; i < todo.size(); ++i)
    for (int y : {todo[i] ^ 1, a[todo[i]]}) if (!seen[y]) { seen[y] = 1; todo.push_back(y); }
  return int(todo.size()) == k;
}

bool even_walk(int k, const vector<int>& d, int cf, int df) {
  array<array<int, 10>, 2> other{}, weight{};
  for (int j = 0; j < k / 2; ++j) {
    int a = 2 * j + 1, b = (a + 1) % k;
    other[0][a] = b; other[0][b] = a;
    other[1][d[a]] = d[b]; other[1][d[b]] = d[a];
    weight[0][a] = weight[0][b] = (cf >> j) & 1;
    weight[1][d[a]] = weight[1][d[b]] = (df >> j) & 1;
  }
  array<bool, 10> seen{};
  for (int start = 0; start < k; ++start) if (!seen[start]) {
    int v = start, side = 0, sum = 0;
    do {
      assert(!seen[v]); seen[v] = true;
      sum ^= weight[side][v]; v = other[side][v]; side ^= 1;
    } while (v != start);
    assert(side == 0);
    if (sum) return false;
  }
  return true;
}

void check_class(int k, int mask, const vector<int>& order, int flags) {
  assert(mask > 0 && mask < (1 << k));
  vector<int> pos;
  for (int i = 0; i < k; ++i) if ((mask >> order[i]) & 1) pos.push_back(i);
  assert(pos.size() % 2 == 1);
  for (size_t j = 0; j < pos.size(); ++j) {
    int start = pos[j], end = pos[(j + 1) % pos.size()];
    if (end <= start) end += k;
    int length = 0;
    for (int i = start; i < end; ++i)
      length += (i % 2 == 0) ? 1 : 1 + ((flags >> ((i % k) / 2)) & 1);
    assert(length % 2 == 1);
  }
}

int main() {
  ifstream cert("out/partitions.bin", ios::binary);
  assert(cert);
  for (int k : {4, 6, 8, 10}) {
    vector<int> c(k), d(k), reps;
    iota(c.begin(), c.end(), 0); d = c;
    if (k == 4) reps = {1};
    if (k == 6) reps = {1, 7};
    if (k == 8) reps = {1, 7};
    if (k == 10) reps = {1, 7, 11, 31};
    uint64_t orders = 0, total = 0, even = 0, partitions = 0;
    do {
      if (!connected(k, d)) continue;
      ++orders;
      for (int cf : reps) for (int df = 0; df < (1 << (k / 2)); ++df) if (parity(df)) {
        ++total;
        if (even_walk(k, d, cf, df)) { ++even; continue; }
        int covered = 0;
        for (int j = 0; j < 4; ++j) {
          int lo = cert.get(), hi = cert.get();
          assert(lo != EOF && hi != EOF);
          int s = lo + 256 * hi;
          assert(!(covered & s)); covered |= s;
          check_class(k, s, c, cf); check_class(k, s, d, df);
        }
        assert(covered == (1 << k) - 1);
        ++partitions;
      }
    } while (next_permutation(d.begin() + 1, d.end()));
    uint64_t expected = (k == 4 ? 4 : k == 6 ? 64 : k == 8 ? 2304 : 147456);
    assert(orders == expected);
    assert(total == expected * reps.size() * (1 << (k / 2 - 1)));
    assert(total == even + partitions);
    cout << "REPLAY PASS k=" << k << " orders=" << orders << " total=" << total
         << " even=" << even << " partitioned=" << partitions << endl;
  }
  assert(cert.get() == EOF);
  cout << "COMPLETE: all certificate records verified, exact EOF" << endl;
}
