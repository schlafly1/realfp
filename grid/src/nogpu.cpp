/* CPU-only build: no GPU engine. */
#include "grid.hpp"
bool gpu_available(std::string &desc) { desc = "not built with CUDA (build.sh without nvcc)"; return false; }
Engine *make_gpu(const Problem &, const Opts &, bool) { return nullptr; }
