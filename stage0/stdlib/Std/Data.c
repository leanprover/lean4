// Lean compiler output
// Module: Std.Data
// Imports: public import Std.Data.DHashMap public import Std.Data.HashMap public import Std.Data.HashSet public import Std.Data.DTreeMap public import Std.Data.TreeMap public import Std.Data.TreeSet public import Std.Data.ExtDHashMap public import Std.Data.ExtHashMap public import Std.Data.ExtHashSet public import Std.Data.ExtDTreeMap public import Std.Data.ExtTreeMap public import Std.Data.ExtTreeSet public import Std.Data.DHashMap.RawLemmas public import Std.Data.DHashMap.RawDecidableEquiv public import Std.Data.HashMap.RawLemmas public import Std.Data.HashMap.RawDecidableEquiv public import Std.Data.HashSet.RawLemmas public import Std.Data.HashSet.RawDecidableEquiv public import Std.Data.DTreeMap.Raw public import Std.Data.TreeMap.Raw public import Std.Data.TreeSet.Raw public import Std.Data.Iterators public import Std.Data.ByteSlice
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* initialize_Std_Data_DHashMap(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet(uint8_t builtin);
lean_object* initialize_Std_Data_ExtDHashMap(uint8_t builtin);
lean_object* initialize_Std_Data_ExtHashMap(uint8_t builtin);
lean_object* initialize_Std_Data_ExtHashSet(uint8_t builtin);
lean_object* initialize_Std_Data_ExtDTreeMap(uint8_t builtin);
lean_object* initialize_Std_Data_ExtTreeMap(uint8_t builtin);
lean_object* initialize_Std_Data_ExtTreeSet(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_RawLemmas(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_RawDecidableEquiv(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_RawLemmas(uint8_t builtin);
lean_object* initialize_Std_Data_HashMap_RawDecidableEquiv(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_RawLemmas(uint8_t builtin);
lean_object* initialize_Std_Data_HashSet_RawDecidableEquiv(uint8_t builtin);
lean_object* initialize_Std_Data_DTreeMap_Raw(uint8_t builtin);
lean_object* initialize_Std_Data_TreeMap_Raw(uint8_t builtin);
lean_object* initialize_Std_Data_TreeSet_Raw(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators(uint8_t builtin);
lean_object* initialize_Std_Data_ByteSlice(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_DHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_ExtDHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_ExtHashMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_ExtHashSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_ExtDTreeMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_ExtTreeMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_ExtTreeSet(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashMap_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_RawLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_HashSet_RawDecidableEquiv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DTreeMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeMap_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_TreeSet_Raw(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_ByteSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
