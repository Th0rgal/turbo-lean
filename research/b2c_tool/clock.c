#include <lean/lean.h>
#include <time.h>
LEAN_EXPORT lean_obj_res b2c_cpu_ns(lean_obj_arg world) {
  struct timespec t;
  clock_gettime(CLOCK_PROCESS_CPUTIME_ID, &t);
  return lean_io_result_mk_ok(lean_uint64_to_nat((uint64_t)t.tv_sec * 1000000000ULL + t.tv_nsec));
}
/* The --run interpreter resolves the Lean declaration symbol. */
LEAN_EXPORT lean_obj_res l_B2c_cpuNS(lean_obj_arg world) { return b2c_cpu_ns(world); }
LEAN_EXPORT lean_obj_res l_cpuNS(lean_obj_arg world) { return b2c_cpu_ns(world); }
