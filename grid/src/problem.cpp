#include "grid.hpp"
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <sstream>
#include <fstream>

static double from_hex(const std::string &s, bool &ok) {
  char *e = nullptr;
  unsigned long long u = strtoull(s.c_str(), &e, 16);
  ok = ok && e && *e == 0 && !s.empty();
  double x; memcpy(&x, &u, 8); return x;
}

/* Format (written by the `interval_grid` tactic; whitespace separated):
     realfp-grid-problem 1
     d <d>
     box <lo bits> <hi bits>        (d lines; binary64 bit patterns in hex)
     goal le|ge <c bits>
     consts <m>   then m lines <lo bits> <hi bits>
     tape <n>     then n lines <op> <a> <b>
   Lines starting with # are comments. */
bool read_problem(const char *path, Problem &P, std::string &err) {
  std::ifstream f(path, std::ios::binary);
  if (!f) { err = std::string("cannot open ") + path; return false; }
  std::stringstream ss; ss << f.rdbuf();
  std::string text = ss.str();
  uint64_t h = 1469598103934665603ull;
  for (unsigned char ch : text) { h ^= ch; h *= 1099511628211ull; }
  P.fnv = h;
  std::istringstream in(text);
  std::string line, tok;
  std::vector<std::string> t;
  while (std::getline(in, line)) {
    if (!line.empty() && line[0] == '#') continue;
    std::istringstream ls(line);
    while (ls >> tok) t.push_back(tok);
  }
  size_t i = 0; bool ok = true;
  auto next = [&]() -> std::string { if (i < t.size()) return t[i++]; ok = false; return ""; };
  if (next() != "realfp-grid-problem" || next() != "1") { err = "not a realfp-grid problem file (v1)"; return false; }
  if (next() != "d") { err = "expected d"; return false; }
  P.d = (uint32_t)atoi(next().c_str());
  if (P.d == 0 || P.d > RFG_MAXD) { err = "d must be 1..16"; return false; }
  for (uint32_t j = 0; j < P.d; j++) {
    if (next() != "box") { err = "expected box"; return false; }
    P.lo[j] = from_hex(next(), ok); P.hi[j] = from_hex(next(), ok);
  }
  if (next() != "goal") { err = "expected goal"; return false; }
  std::string g = next();
  if (g == "le") P.upper = true; else if (g == "ge") P.upper = false; else { err = "goal le|ge"; return false; }
  P.c = from_hex(next(), ok);
  if (next() != "consts") { err = "expected consts"; return false; }
  int m = atoi(next().c_str());
  for (int j = 0; j < m; j++) { P.k.push_back(from_hex(next(), ok)); P.k.push_back(from_hex(next(), ok)); }
  if (next() != "tape") { err = "expected tape"; return false; }
  int n = atoi(next().c_str());
  if (n <= 0 || n > RFG_MAXT) { err = "tape length must be 1.." + std::to_string(RFG_MAXT); return false; }
  for (int j = 0; j < 3 * n; j++) P.code.push_back((uint32_t)strtoul(next().c_str(), nullptr, 10));
  if (!ok) { err = "malformed problem file"; return false; }
  for (int k = 0; k < n; k++) {
    uint32_t op = P.code[3 * k], a = P.code[3 * k + 1], b = P.code[3 * k + 2];
    if (op > 8 || (op == 1 && a >= (uint32_t)m) || (op >= 2 && op <= 8 && a >= (uint32_t)k) ||
        (((op >= 2 && op <= 4) || op == 7) && b >= (uint32_t)k)) { err = "bad tape instruction"; return false; }
  }
  return true;
}
