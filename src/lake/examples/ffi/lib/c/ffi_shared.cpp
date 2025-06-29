#include <lean/lean.h>
#include <string>

extern "C" lean_obj_res my_lean_fun() {
    std::string ss = "hi";
    lean_obj_res result = lean_mk_string(ss.c_str());
    return lean_io_result_mk_ok(result);
}
