// Lean compiler output
// Module: Lean.Data
// Imports: Lean.Data.AssocList Lean.Data.Format Lean.Data.HashMap Lean.Data.HashSet Lean.Data.Json Lean.Data.JsonRpc Lean.Data.KVMap Lean.Data.LBool Lean.Data.LOption Lean.Data.Lsp Lean.Data.Name Lean.Data.NameMap Lean.Data.OpenDecl Lean.Data.Options Lean.Data.PersistentArray Lean.Data.PersistentHashMap Lean.Data.PersistentHashSet Lean.Data.Position Lean.Data.PrefixTree Lean.Data.SMap Lean.Data.Trie Lean.Data.Xml Lean.Data.NameTrie Lean.Data.RBTree Lean.Data.RBMap Lean.Data.Rat
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
lean_object* initialize_Lean_Data_AssocList(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Format(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_HashMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_HashSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_JsonRpc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_KVMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_LBool(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_LOption(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Lsp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Name(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_NameMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_OpenDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentArray(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentHashMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PersistentHashSet(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Position(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_PrefixTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_SMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Trie(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Xml(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_NameTrie(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RBMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Rat(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_AssocList(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Format(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_HashMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_HashSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_JsonRpc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_KVMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_LBool(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_LOption(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Lsp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Name(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_OpenDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentHashMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PersistentHashSet(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Position(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_PrefixTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_SMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Trie(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Xml(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_NameTrie(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RBMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Rat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
