// Lean compiler output
// Module: Lean.Compiler.ClosedTermCache
// Imports: public import Lean.Environment
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
uint64_t l_Lean_Expr_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
extern lean_object* l_Lean_NameSet_empty;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_takeNewEntries___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerEnvExtension___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_instInhabitedClosedTermCache_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedClosedTermCache_default___closed__0;
static lean_once_cell_t l_Lean_instInhabitedClosedTermCache_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedClosedTermCache_default___closed__1;
static lean_once_cell_t l_Lean_instInhabitedClosedTermCache_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instInhabitedClosedTermCache_default___closed__2;
LEAN_EXPORT lean_object* l_Lean_instInhabitedClosedTermCache_default;
LEAN_EXPORT lean_object* l_Lean_instInhabitedClosedTermCache;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "Lean.Data.PersistentHashMap"};
static const lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__0 = (const lean_object*)&l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__0_value;
static const lean_string_object l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Lean.PersistentHashMap.find!"};
static const lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__1 = (const lean_object*)&l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__1_value;
static const lean_string_object l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "key is not in the map"};
static const lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__2 = (const lean_object*)&l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__3;
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_;
static const lean_ctor_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "closedTermCacheExt"};
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__3_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__4_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(123, 48, 235, 129, 20, 167, 228, 119)}};
static const lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_closedTermCacheExt;
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getClosedTermName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getClosedTermName_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_isClosedTermName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isClosedTermName___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_instInhabitedClosedTermCache_default___closed__0(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_1_;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache_default___closed__1(void){
_start:
{
lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_2_ = lean_obj_once(&l_Lean_instInhabitedClosedTermCache_default___closed__0, &l_Lean_instInhabitedClosedTermCache_default___closed__0_once, _init_l_Lean_instInhabitedClosedTermCache_default___closed__0);
v___x_3_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache_default___closed__2(void){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_4_ = lean_box(0);
v___x_5_ = l_Lean_NameSet_empty;
v___x_6_ = lean_obj_once(&l_Lean_instInhabitedClosedTermCache_default___closed__1, &l_Lean_instInhabitedClosedTermCache_default___closed__1_once, _init_l_Lean_instInhabitedClosedTermCache_default___closed__1);
v___x_7_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_7_, 0, v___x_6_);
lean_ctor_set(v___x_7_, 1, v___x_5_);
lean_ctor_set(v___x_7_, 2, v___x_4_);
return v___x_7_;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache_default(void){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_obj_once(&l_Lean_instInhabitedClosedTermCache_default___closed__2, &l_Lean_instInhabitedClosedTermCache_default___closed__2_once, _init_l_Lean_instInhabitedClosedTermCache_default___closed__2);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_instInhabitedClosedTermCache(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = l_Lean_instInhabitedClosedTermCache_default;
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__2(lean_object* v_msg_10_){
_start:
{
lean_object* v___x_11_; lean_object* v___x_12_; 
v___x_11_ = lean_box(0);
v___x_12_ = lean_panic_fn_borrowed(v___x_11_, v_msg_10_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(lean_object* v_x_13_, lean_object* v_x_14_, lean_object* v_x_15_, lean_object* v_x_16_){
_start:
{
lean_object* v_ks_17_; lean_object* v_vs_18_; lean_object* v___x_20_; uint8_t v_isShared_21_; uint8_t v_isSharedCheck_42_; 
v_ks_17_ = lean_ctor_get(v_x_13_, 0);
v_vs_18_ = lean_ctor_get(v_x_13_, 1);
v_isSharedCheck_42_ = !lean_is_exclusive(v_x_13_);
if (v_isSharedCheck_42_ == 0)
{
v___x_20_ = v_x_13_;
v_isShared_21_ = v_isSharedCheck_42_;
goto v_resetjp_19_;
}
else
{
lean_inc(v_vs_18_);
lean_inc(v_ks_17_);
lean_dec(v_x_13_);
v___x_20_ = lean_box(0);
v_isShared_21_ = v_isSharedCheck_42_;
goto v_resetjp_19_;
}
v_resetjp_19_:
{
lean_object* v___x_22_; uint8_t v___x_23_; 
v___x_22_ = lean_array_get_size(v_ks_17_);
v___x_23_ = lean_nat_dec_lt(v_x_14_, v___x_22_);
if (v___x_23_ == 0)
{
lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_27_; 
lean_dec(v_x_14_);
v___x_24_ = lean_array_push(v_ks_17_, v_x_15_);
v___x_25_ = lean_array_push(v_vs_18_, v_x_16_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 1, v___x_25_);
lean_ctor_set(v___x_20_, 0, v___x_24_);
v___x_27_ = v___x_20_;
goto v_reusejp_26_;
}
else
{
lean_object* v_reuseFailAlloc_28_; 
v_reuseFailAlloc_28_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_28_, 0, v___x_24_);
lean_ctor_set(v_reuseFailAlloc_28_, 1, v___x_25_);
v___x_27_ = v_reuseFailAlloc_28_;
goto v_reusejp_26_;
}
v_reusejp_26_:
{
return v___x_27_;
}
}
else
{
lean_object* v_k_x27_29_; uint8_t v___x_30_; 
v_k_x27_29_ = lean_array_fget_borrowed(v_ks_17_, v_x_14_);
v___x_30_ = lean_expr_eqv(v_x_15_, v_k_x27_29_);
if (v___x_30_ == 0)
{
lean_object* v___x_32_; 
if (v_isShared_21_ == 0)
{
v___x_32_ = v___x_20_;
goto v_reusejp_31_;
}
else
{
lean_object* v_reuseFailAlloc_36_; 
v_reuseFailAlloc_36_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_36_, 0, v_ks_17_);
lean_ctor_set(v_reuseFailAlloc_36_, 1, v_vs_18_);
v___x_32_ = v_reuseFailAlloc_36_;
goto v_reusejp_31_;
}
v_reusejp_31_:
{
lean_object* v___x_33_; lean_object* v___x_34_; 
v___x_33_ = lean_unsigned_to_nat(1u);
v___x_34_ = lean_nat_add(v_x_14_, v___x_33_);
lean_dec(v_x_14_);
v_x_13_ = v___x_32_;
v_x_14_ = v___x_34_;
goto _start;
}
}
else
{
lean_object* v___x_37_; lean_object* v___x_38_; lean_object* v___x_40_; 
v___x_37_ = lean_array_fset(v_ks_17_, v_x_14_, v_x_15_);
v___x_38_ = lean_array_fset(v_vs_18_, v_x_14_, v_x_16_);
lean_dec(v_x_14_);
if (v_isShared_21_ == 0)
{
lean_ctor_set(v___x_20_, 1, v___x_38_);
lean_ctor_set(v___x_20_, 0, v___x_37_);
v___x_40_ = v___x_20_;
goto v_reusejp_39_;
}
else
{
lean_object* v_reuseFailAlloc_41_; 
v_reuseFailAlloc_41_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_41_, 0, v___x_37_);
lean_ctor_set(v_reuseFailAlloc_41_, 1, v___x_38_);
v___x_40_ = v_reuseFailAlloc_41_;
goto v_reusejp_39_;
}
v_reusejp_39_:
{
return v___x_40_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(lean_object* v_n_43_, lean_object* v_k_44_, lean_object* v_v_45_){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_unsigned_to_nat(0u);
v___x_47_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_n_43_, v___x_46_, v_k_44_, v_v_45_);
return v___x_47_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_48_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_49_, size_t v_x_50_, size_t v_x_51_, lean_object* v_x_52_, lean_object* v_x_53_){
_start:
{
if (lean_obj_tag(v_x_49_) == 0)
{
lean_object* v_es_54_; size_t v___x_55_; size_t v___x_56_; lean_object* v_j_57_; lean_object* v___x_58_; uint8_t v___x_59_; 
v_es_54_ = lean_ctor_get(v_x_49_, 0);
v___x_55_ = ((size_t)31ULL);
v___x_56_ = lean_usize_land(v_x_50_, v___x_55_);
v_j_57_ = lean_usize_to_nat(v___x_56_);
v___x_58_ = lean_array_get_size(v_es_54_);
v___x_59_ = lean_nat_dec_lt(v_j_57_, v___x_58_);
if (v___x_59_ == 0)
{
lean_dec(v_j_57_);
lean_dec(v_x_53_);
lean_dec_ref(v_x_52_);
return v_x_49_;
}
else
{
lean_object* v___x_61_; uint8_t v_isShared_62_; uint8_t v_isSharedCheck_98_; 
lean_inc_ref(v_es_54_);
v_isSharedCheck_98_ = !lean_is_exclusive(v_x_49_);
if (v_isSharedCheck_98_ == 0)
{
lean_object* v_unused_99_; 
v_unused_99_ = lean_ctor_get(v_x_49_, 0);
lean_dec(v_unused_99_);
v___x_61_ = v_x_49_;
v_isShared_62_ = v_isSharedCheck_98_;
goto v_resetjp_60_;
}
else
{
lean_dec(v_x_49_);
v___x_61_ = lean_box(0);
v_isShared_62_ = v_isSharedCheck_98_;
goto v_resetjp_60_;
}
v_resetjp_60_:
{
lean_object* v_v_63_; lean_object* v___x_64_; lean_object* v_xs_x27_65_; lean_object* v___y_67_; 
v_v_63_ = lean_array_fget(v_es_54_, v_j_57_);
v___x_64_ = lean_box(0);
v_xs_x27_65_ = lean_array_fset(v_es_54_, v_j_57_, v___x_64_);
switch(lean_obj_tag(v_v_63_))
{
case 0:
{
lean_object* v_key_72_; lean_object* v_val_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_83_; 
v_key_72_ = lean_ctor_get(v_v_63_, 0);
v_val_73_ = lean_ctor_get(v_v_63_, 1);
v_isSharedCheck_83_ = !lean_is_exclusive(v_v_63_);
if (v_isSharedCheck_83_ == 0)
{
v___x_75_ = v_v_63_;
v_isShared_76_ = v_isSharedCheck_83_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_val_73_);
lean_inc(v_key_72_);
lean_dec(v_v_63_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_83_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
uint8_t v___x_77_; 
v___x_77_ = lean_expr_eqv(v_x_52_, v_key_72_);
if (v___x_77_ == 0)
{
lean_object* v___x_78_; lean_object* v___x_79_; 
lean_del_object(v___x_75_);
v___x_78_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_72_, v_val_73_, v_x_52_, v_x_53_);
v___x_79_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
v___y_67_ = v___x_79_;
goto v___jp_66_;
}
else
{
lean_object* v___x_81_; 
lean_dec(v_val_73_);
lean_dec(v_key_72_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v_x_53_);
lean_ctor_set(v___x_75_, 0, v_x_52_);
v___x_81_ = v___x_75_;
goto v_reusejp_80_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v_x_52_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_x_53_);
v___x_81_ = v_reuseFailAlloc_82_;
goto v_reusejp_80_;
}
v_reusejp_80_:
{
v___y_67_ = v___x_81_;
goto v___jp_66_;
}
}
}
}
case 1:
{
lean_object* v_node_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_96_; 
v_node_84_ = lean_ctor_get(v_v_63_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v_v_63_);
if (v_isSharedCheck_96_ == 0)
{
v___x_86_ = v_v_63_;
v_isShared_87_ = v_isSharedCheck_96_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_node_84_);
lean_dec(v_v_63_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_96_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
size_t v___x_88_; size_t v___x_89_; size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_88_ = ((size_t)5ULL);
v___x_89_ = lean_usize_shift_right(v_x_50_, v___x_88_);
v___x_90_ = ((size_t)1ULL);
v___x_91_ = lean_usize_add(v_x_51_, v___x_90_);
v___x_92_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(v_node_84_, v___x_89_, v___x_91_, v_x_52_, v_x_53_);
if (v_isShared_87_ == 0)
{
lean_ctor_set(v___x_86_, 0, v___x_92_);
v___x_94_ = v___x_86_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
v___y_67_ = v___x_94_;
goto v___jp_66_;
}
}
}
default: 
{
lean_object* v___x_97_; 
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v_x_52_);
lean_ctor_set(v___x_97_, 1, v_x_53_);
v___y_67_ = v___x_97_;
goto v___jp_66_;
}
}
v___jp_66_:
{
lean_object* v___x_68_; lean_object* v___x_70_; 
v___x_68_ = lean_array_fset(v_xs_x27_65_, v_j_57_, v___y_67_);
lean_dec(v_j_57_);
if (v_isShared_62_ == 0)
{
lean_ctor_set(v___x_61_, 0, v___x_68_);
v___x_70_ = v___x_61_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v___x_68_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
}
}
}
else
{
lean_object* v_ks_100_; lean_object* v_vs_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_119_; 
v_ks_100_ = lean_ctor_get(v_x_49_, 0);
v_vs_101_ = lean_ctor_get(v_x_49_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v_x_49_);
if (v_isSharedCheck_119_ == 0)
{
v___x_103_ = v_x_49_;
v_isShared_104_ = v_isSharedCheck_119_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_vs_101_);
lean_inc(v_ks_100_);
lean_dec(v_x_49_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_119_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_106_; 
if (v_isShared_104_ == 0)
{
v___x_106_ = v___x_103_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_ks_100_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v_vs_101_);
v___x_106_ = v_reuseFailAlloc_118_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v_newNode_107_; size_t v___x_108_; uint8_t v___x_109_; 
v_newNode_107_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v___x_106_, v_x_52_, v_x_53_);
v___x_108_ = ((size_t)7ULL);
v___x_109_ = lean_usize_dec_le(v___x_108_, v_x_51_);
if (v___x_109_ == 0)
{
lean_object* v___x_110_; lean_object* v___x_111_; uint8_t v___x_112_; 
v___x_110_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_107_);
v___x_111_ = lean_unsigned_to_nat(4u);
v___x_112_ = lean_nat_dec_lt(v___x_110_, v___x_111_);
lean_dec(v___x_110_);
if (v___x_112_ == 0)
{
lean_object* v_ks_113_; lean_object* v_vs_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_ks_113_ = lean_ctor_get(v_newNode_107_, 0);
lean_inc_ref(v_ks_113_);
v_vs_114_ = lean_ctor_get(v_newNode_107_, 1);
lean_inc_ref(v_vs_114_);
lean_dec_ref(v_newNode_107_);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___closed__0);
v___x_117_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_x_51_, v_ks_113_, v_vs_114_, v___x_115_, v___x_116_);
lean_dec_ref(v_vs_114_);
lean_dec_ref(v_ks_113_);
return v___x_117_;
}
else
{
return v_newNode_107_;
}
}
else
{
return v_newNode_107_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_49_ = stack[0].m_obj;
size_t v_x_50_ = stack[1].m_num;
size_t v_x_51_ = stack[2].m_num;
lean_object* v_x_52_ = stack[3].m_obj;
lean_object* v_x_53_ = stack[4].m_obj;
lean_object* v_res_120_;
v_res_120_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_49_, v_x_50_, v_x_51_, v_x_52_, v_x_53_);
stack->m_obj
 = v_res_120_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(size_t v_depth_121_, lean_object* v_keys_122_, lean_object* v_vals_123_, lean_object* v_i_124_, lean_object* v_entries_125_){
_start:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = lean_array_get_size(v_keys_122_);
v___x_127_ = lean_nat_dec_lt(v_i_124_, v___x_126_);
if (v___x_127_ == 0)
{
lean_dec(v_i_124_);
return v_entries_125_;
}
else
{
lean_object* v_k_128_; lean_object* v_v_129_; uint64_t v___x_130_; size_t v_h_131_; size_t v___x_132_; lean_object* v___x_133_; size_t v___x_134_; size_t v___x_135_; size_t v___x_136_; size_t v_h_137_; lean_object* v___x_138_; lean_object* v___x_139_; 
v_k_128_ = lean_array_fget_borrowed(v_keys_122_, v_i_124_);
v_v_129_ = lean_array_fget_borrowed(v_vals_123_, v_i_124_);
v___x_130_ = l_Lean_Expr_hash(v_k_128_);
v_h_131_ = lean_uint64_to_usize(v___x_130_);
v___x_132_ = ((size_t)5ULL);
v___x_133_ = lean_unsigned_to_nat(1u);
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_sub(v_depth_121_, v___x_134_);
v___x_136_ = lean_usize_mul(v___x_132_, v___x_135_);
v_h_137_ = lean_usize_shift_right(v_h_131_, v___x_136_);
v___x_138_ = lean_nat_add(v_i_124_, v___x_133_);
lean_dec(v_i_124_);
lean_inc(v_v_129_);
lean_inc(v_k_128_);
v___x_139_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(v_entries_125_, v_h_137_, v_depth_121_, v_k_128_, v_v_129_);
v_i_124_ = v___x_138_;
v_entries_125_ = v___x_139_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_121_ = stack[0].m_num;
lean_object* v_keys_122_ = stack[1].m_obj;
lean_object* v_vals_123_ = stack[2].m_obj;
lean_object* v_i_124_ = stack[3].m_obj;
lean_object* v_entries_125_ = stack[4].m_obj;
lean_object* v_res_141_;
v_res_141_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_depth_121_, v_keys_122_, v_vals_123_, v_i_124_, v_entries_125_);
stack->m_obj
 = v_res_141_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_depth_142_, lean_object* v_keys_143_, lean_object* v_vals_144_, lean_object* v_i_145_, lean_object* v_entries_146_){
_start:
{
size_t v_depth_boxed_147_; lean_object* v_res_148_; 
v_depth_boxed_147_ = lean_unbox_usize(v_depth_142_);
lean_dec(v_depth_142_);
v_res_148_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_depth_boxed_147_, v_keys_143_, v_vals_144_, v_i_145_, v_entries_146_);
lean_dec_ref(v_vals_144_);
lean_dec_ref(v_keys_143_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_149_, lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
size_t v_x_633__boxed_154_; size_t v_x_634__boxed_155_; lean_object* v_res_156_; 
v_x_633__boxed_154_ = lean_unbox_usize(v_x_150_);
lean_dec(v_x_150_);
v_x_634__boxed_155_ = lean_unbox_usize(v_x_151_);
lean_dec(v_x_151_);
v_res_156_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_149_, v_x_633__boxed_154_, v_x_634__boxed_155_, v_x_152_, v_x_153_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0___redArg(lean_object* v_x_157_, lean_object* v_x_158_, lean_object* v_x_159_){
_start:
{
uint64_t v___x_160_; size_t v___x_161_; size_t v___x_162_; lean_object* v___x_163_; 
v___x_160_ = l_Lean_Expr_hash(v_x_158_);
v___x_161_ = lean_uint64_to_usize(v___x_160_);
v___x_162_ = ((size_t)1ULL);
v___x_163_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_157_, v___x_161_, v___x_162_, v_x_158_, v_x_159_);
return v___x_163_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(lean_object* v_keys_164_, lean_object* v_vals_165_, lean_object* v_i_166_, lean_object* v_k_167_){
_start:
{
lean_object* v___x_168_; uint8_t v___x_169_; 
v___x_168_ = lean_array_get_size(v_keys_164_);
v___x_169_ = lean_nat_dec_lt(v_i_166_, v___x_168_);
if (v___x_169_ == 0)
{
lean_object* v___x_170_; 
lean_dec(v_i_166_);
v___x_170_ = lean_box(0);
return v___x_170_;
}
else
{
lean_object* v_k_x27_171_; uint8_t v___x_172_; 
v_k_x27_171_ = lean_array_fget_borrowed(v_keys_164_, v_i_166_);
v___x_172_ = lean_expr_eqv(v_k_167_, v_k_x27_171_);
if (v___x_172_ == 0)
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = lean_unsigned_to_nat(1u);
v___x_174_ = lean_nat_add(v_i_166_, v___x_173_);
lean_dec(v_i_166_);
v_i_166_ = v___x_174_;
goto _start;
}
else
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = lean_array_fget_borrowed(v_vals_165_, v_i_166_);
lean_dec(v_i_166_);
lean_inc(v___x_176_);
v___x_177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_177_, 0, v___x_176_);
return v___x_177_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg___boxed(lean_object* v_keys_178_, lean_object* v_vals_179_, lean_object* v_i_180_, lean_object* v_k_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_keys_178_, v_vals_179_, v_i_180_, v_k_181_);
lean_dec_ref(v_k_181_);
lean_dec_ref(v_vals_179_);
lean_dec_ref(v_keys_178_);
return v_res_182_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_x_183_, size_t v_x_184_, lean_object* v_x_185_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_object* v_es_186_; lean_object* v___x_187_; size_t v___x_188_; size_t v___x_189_; lean_object* v_j_190_; lean_object* v___x_191_; 
v_es_186_ = lean_ctor_get(v_x_183_, 0);
v___x_187_ = lean_box(2);
v___x_188_ = ((size_t)31ULL);
v___x_189_ = lean_usize_land(v_x_184_, v___x_188_);
v_j_190_ = lean_usize_to_nat(v___x_189_);
v___x_191_ = lean_array_get_borrowed(v___x_187_, v_es_186_, v_j_190_);
lean_dec(v_j_190_);
switch(lean_obj_tag(v___x_191_))
{
case 0:
{
lean_object* v_key_192_; lean_object* v_val_193_; uint8_t v___x_194_; 
v_key_192_ = lean_ctor_get(v___x_191_, 0);
v_val_193_ = lean_ctor_get(v___x_191_, 1);
v___x_194_ = lean_expr_eqv(v_x_185_, v_key_192_);
if (v___x_194_ == 0)
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(0);
return v___x_195_;
}
else
{
lean_object* v___x_196_; 
lean_inc(v_val_193_);
v___x_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_196_, 0, v_val_193_);
return v___x_196_;
}
}
case 1:
{
lean_object* v_node_197_; size_t v___x_198_; size_t v___x_199_; 
v_node_197_ = lean_ctor_get(v___x_191_, 0);
v___x_198_ = ((size_t)5ULL);
v___x_199_ = lean_usize_shift_right(v_x_184_, v___x_198_);
v_x_183_ = v_node_197_;
v_x_184_ = v___x_199_;
goto _start;
}
default: 
{
lean_object* v___x_201_; 
v___x_201_ = lean_box(0);
return v___x_201_;
}
}
}
else
{
lean_object* v_ks_202_; lean_object* v_vs_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_ks_202_ = lean_ctor_get(v_x_183_, 0);
v_vs_203_ = lean_ctor_get(v_x_183_, 1);
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_ks_202_, v_vs_203_, v___x_204_, v_x_185_);
return v___x_205_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_183_ = stack[0].m_obj;
size_t v_x_184_ = stack[1].m_num;
lean_object* v_x_185_ = stack[2].m_obj;
lean_object* v_res_206_;
v_res_206_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_183_, v_x_184_, v_x_185_);
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_x_207_, lean_object* v_x_208_, lean_object* v_x_209_){
_start:
{
size_t v_x_917__boxed_210_; lean_object* v_res_211_; 
v_x_917__boxed_210_ = lean_unbox_usize(v_x_208_);
lean_dec(v_x_208_);
v_res_211_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_207_, v_x_917__boxed_210_, v_x_209_);
lean_dec_ref(v_x_209_);
lean_dec_ref(v_x_207_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg(lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
uint64_t v___x_214_; size_t v___x_215_; lean_object* v___x_216_; 
v___x_214_ = l_Lean_Expr_hash(v_x_213_);
v___x_215_ = lean_uint64_to_usize(v___x_214_);
v___x_216_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_212_, v___x_215_, v_x_213_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg(v_x_217_, v_x_218_);
lean_dec_ref(v_x_218_);
lean_dec_ref(v_x_217_);
return v_res_219_;
}
}
static lean_object* _init_l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__3(void){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v___x_223_ = ((lean_object*)(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__2));
v___x_224_ = lean_unsigned_to_nat(14u);
v___x_225_ = lean_unsigned_to_nat(178u);
v___x_226_ = ((lean_object*)(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__1));
v___x_227_ = ((lean_object*)(l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__0));
v___x_228_ = l_mkPanicMessageWithDecl(v___x_227_, v___x_226_, v___x_225_, v___x_224_, v___x_223_);
return v___x_228_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3(lean_object* v_newState_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
return v_x_230_;
}
else
{
lean_object* v_head_232_; lean_object* v_tail_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_260_; 
v_head_232_ = lean_ctor_get(v_x_231_, 0);
v_tail_233_ = lean_ctor_get(v_x_231_, 1);
v_isSharedCheck_260_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_260_ == 0)
{
v___x_235_ = v_x_231_;
v_isShared_236_ = v_isSharedCheck_260_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_tail_233_);
lean_inc(v_head_232_);
lean_dec(v_x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_260_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___y_238_; lean_object* v_map_255_; lean_object* v___x_256_; 
v_map_255_ = lean_ctor_get(v_newState_229_, 0);
v___x_256_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg(v_map_255_, v_head_232_);
if (lean_obj_tag(v___x_256_) == 0)
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = lean_obj_once(&l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__3, &l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__3_once, _init_l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___closed__3);
v___x_258_ = l_panic___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__2(v___x_257_);
v___y_238_ = v___x_258_;
goto v___jp_237_;
}
else
{
lean_object* v_val_259_; 
v_val_259_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_val_259_);
lean_dec_ref_known(v___x_256_, 1);
v___y_238_ = v_val_259_;
goto v___jp_237_;
}
v___jp_237_:
{
lean_object* v_map_239_; lean_object* v_constNames_240_; lean_object* v_revExprs_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_254_; 
v_map_239_ = lean_ctor_get(v_x_230_, 0);
v_constNames_240_ = lean_ctor_get(v_x_230_, 1);
v_revExprs_241_ = lean_ctor_get(v_x_230_, 2);
v_isSharedCheck_254_ = !lean_is_exclusive(v_x_230_);
if (v_isSharedCheck_254_ == 0)
{
v___x_243_ = v_x_230_;
v_isShared_244_ = v_isSharedCheck_254_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_revExprs_241_);
lean_inc(v_constNames_240_);
lean_inc(v_map_239_);
lean_dec(v_x_230_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_254_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_248_; 
lean_inc(v___y_238_);
lean_inc(v_head_232_);
v___x_245_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0___redArg(v_map_239_, v_head_232_, v___y_238_);
v___x_246_ = l_Lean_NameSet_insert(v_constNames_240_, v___y_238_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_revExprs_241_);
v___x_248_ = v___x_235_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_head_232_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_revExprs_241_);
v___x_248_ = v_reuseFailAlloc_253_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_250_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 2, v___x_248_);
lean_ctor_set(v___x_243_, 1, v___x_246_);
lean_ctor_set(v___x_243_, 0, v___x_245_);
v___x_250_ = v___x_243_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_245_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_252_, 2, v___x_248_);
v___x_250_ = v_reuseFailAlloc_252_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
v_x_230_ = v___x_250_;
v_x_231_ = v_tail_233_;
goto _start;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3___boxed(lean_object* v_newState_261_, lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
lean_object* v_res_264_; 
v_res_264_ = l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3(v_newState_261_, v_x_262_, v_x_263_);
lean_dec_ref(v_newState_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(lean_object* v_oldState_265_, lean_object* v_newState_266_, lean_object* v_x_267_, lean_object* v_s_268_){
_start:
{
lean_object* v_revExprs_269_; lean_object* v_revExprs_270_; lean_object* v_newExprs_271_; lean_object* v___x_272_; 
v_revExprs_269_ = lean_ctor_get(v_newState_266_, 2);
v_revExprs_270_ = lean_ctor_get(v_oldState_265_, 2);
lean_inc(v_revExprs_269_);
v_newExprs_271_ = l_Lean_takeNewEntries___redArg(v_revExprs_269_, v_revExprs_270_);
v___x_272_ = l_List_foldl___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__3(v_newState_266_, v_s_268_, v_newExprs_271_);
lean_dec_ref(v_newState_266_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed(lean_object* v_oldState_273_, lean_object* v_newState_274_, lean_object* v_x_275_, lean_object* v_s_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__0_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(v_oldState_273_, v_newState_274_, v_x_275_, v_s_276_);
lean_dec(v_x_275_);
lean_dec_ref(v_oldState_273_);
return v_res_277_;
}
}
lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(lean_object* v___x_278_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
return v___x_280_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_278_ = stack[0].m_obj;
lean_object* v_res_281_;
v_res_281_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(v___x_278_);
stack->m_obj
 = v_res_281_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed(lean_object* v___x_282_, lean_object* v___y_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(v___x_282_);
return v_res_284_;
}
}
static lean_object* _init_l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_286_; lean_object* v___f_287_; 
v___x_286_ = lean_obj_once(&l_Lean_instInhabitedClosedTermCache_default___closed__2, &l_Lean_instInhabitedClosedTermCache_default___closed__2_once, _init_l_Lean_instInhabitedClosedTermCache_default___closed__2);
v___f_287_ = lean_alloc_closure((void*)(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___lam__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_287_, 0, v___x_286_);
return v___f_287_;
}
}
lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; uint8_t v___x_300_; lean_object* v___x_301_; 
v___f_296_ = lean_obj_once(&l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_, &l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__once, _init_l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__1_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_);
v___x_297_ = ((lean_object*)(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__2_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_));
v___x_298_ = lean_box(0);
v___x_299_ = ((lean_object*)(l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn___closed__5_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_));
v___x_300_ = 0;
v___x_301_ = l_Lean_registerEnvExtension___redArg(v___f_296_, v___x_297_, v___x_298_, v___x_299_, v___x_300_, v___x_300_);
return v___x_301_;
}
}
LEAN_EXPORT void l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_302_;
v_res_302_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_();
stack->m_obj
 = v_res_302_;
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2____boxed(lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_();
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0___redArg(v_x_306_, v_x_307_, v_x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg(v_x_311_, v_x_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_314_, lean_object* v_x_315_, lean_object* v_x_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1(v_00_u03b2_314_, v_x_315_, v_x_316_);
lean_dec_ref(v_x_316_);
lean_dec_ref(v_x_315_);
return v_res_317_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_318_, lean_object* v_x_319_, size_t v_x_320_, size_t v_x_321_, lean_object* v_x_322_, lean_object* v_x_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_319_, v_x_320_, v_x_321_, v_x_322_, v_x_323_);
return v___x_324_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_319_ = stack[1].m_obj;
size_t v_x_320_ = stack[2].m_num;
size_t v_x_321_ = stack[3].m_num;
lean_object* v_x_322_ = stack[4].m_obj;
lean_object* v_x_323_ = stack[5].m_obj;
lean_object* v_res_325_;
v_res_325_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0(lean_box(0), v_x_319_, v_x_320_, v_x_321_, v_x_322_, v_x_323_);
stack->m_obj
 = v_res_325_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_326_, lean_object* v_x_327_, lean_object* v_x_328_, lean_object* v_x_329_, lean_object* v_x_330_, lean_object* v_x_331_){
_start:
{
size_t v_x_1245__boxed_332_; size_t v_x_1246__boxed_333_; lean_object* v_res_334_; 
v_x_1245__boxed_332_ = lean_unbox_usize(v_x_328_);
lean_dec(v_x_328_);
v_x_1246__boxed_333_ = lean_unbox_usize(v_x_329_);
lean_dec(v_x_329_);
v_res_334_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_326_, v_x_327_, v_x_1245__boxed_332_, v_x_1246__boxed_333_, v_x_330_, v_x_331_);
return v_res_334_;
}
}
lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_335_, lean_object* v_x_336_, size_t v_x_337_, lean_object* v_x_338_){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___redArg(v_x_336_, v_x_337_, v_x_338_);
return v___x_339_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_336_ = stack[1].m_obj;
size_t v_x_337_ = stack[2].m_num;
lean_object* v_x_338_ = stack[3].m_obj;
lean_object* v_res_340_;
v_res_340_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2(lean_box(0), v_x_336_, v_x_337_, v_x_338_);
stack->m_obj
 = v_res_340_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b2_341_, lean_object* v_x_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
size_t v_x_1273__boxed_345_; lean_object* v_res_346_; 
v_x_1273__boxed_345_ = lean_unbox_usize(v_x_343_);
lean_dec(v_x_343_);
v_res_346_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_341_, v_x_342_, v_x_1273__boxed_345_, v_x_344_);
lean_dec_ref(v_x_344_);
lean_dec_ref(v_x_342_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2(lean_object* v_00_u03b2_347_, lean_object* v_n_348_, lean_object* v_k_349_, lean_object* v_v_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2___redArg(v_n_348_, v_k_349_, v_v_350_);
return v___x_351_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3(lean_object* v_00_u03b2_352_, size_t v_depth_353_, lean_object* v_keys_354_, lean_object* v_vals_355_, lean_object* v_heq_356_, lean_object* v_i_357_, lean_object* v_entries_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___redArg(v_depth_353_, v_keys_354_, v_vals_355_, v_i_357_, v_entries_358_);
return v___x_359_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_353_ = stack[1].m_num;
lean_object* v_keys_354_ = stack[2].m_obj;
lean_object* v_vals_355_ = stack[3].m_obj;
lean_object* v_i_357_ = stack[5].m_obj;
lean_object* v_entries_358_ = stack[6].m_obj;
lean_object* v_res_360_;
v_res_360_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3(lean_box(0), v_depth_353_, v_keys_354_, v_vals_355_, lean_box(0), v_i_357_, v_entries_358_);
stack->m_obj
 = v_res_360_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_361_, lean_object* v_depth_362_, lean_object* v_keys_363_, lean_object* v_vals_364_, lean_object* v_heq_365_, lean_object* v_i_366_, lean_object* v_entries_367_){
_start:
{
size_t v_depth_boxed_368_; lean_object* v_res_369_; 
v_depth_boxed_368_ = lean_unbox_usize(v_depth_362_);
lean_dec(v_depth_362_);
v_res_369_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__3(v_00_u03b2_361_, v_depth_boxed_368_, v_keys_363_, v_vals_364_, v_heq_365_, v_i_366_, v_entries_367_);
lean_dec_ref(v_vals_364_);
lean_dec_ref(v_keys_363_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6(lean_object* v_00_u03b2_370_, lean_object* v_keys_371_, lean_object* v_vals_372_, lean_object* v_heq_373_, lean_object* v_i_374_, lean_object* v_k_375_){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___redArg(v_keys_371_, v_vals_372_, v_i_374_, v_k_375_);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6___boxed(lean_object* v_00_u03b2_377_, lean_object* v_keys_378_, lean_object* v_vals_379_, lean_object* v_heq_380_, lean_object* v_i_381_, lean_object* v_k_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1_spec__2_spec__6(v_00_u03b2_377_, v_keys_378_, v_vals_379_, v_heq_380_, v_i_381_, v_k_382_);
lean_dec_ref(v_k_382_);
lean_dec_ref(v_vals_379_);
lean_dec_ref(v_keys_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5(lean_object* v_00_u03b2_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
lean_object* v___x_389_; 
v___x_389_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0_spec__0_spec__2_spec__5___redArg(v_x_385_, v_x_386_, v_x_387_, v_x_388_);
return v___x_389_;
}
}
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName___lam__0(lean_object* v_e_390_, lean_object* v_n_391_, lean_object* v_s_392_){
_start:
{
lean_object* v_map_393_; lean_object* v_constNames_394_; lean_object* v_revExprs_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_405_; 
v_map_393_ = lean_ctor_get(v_s_392_, 0);
v_constNames_394_ = lean_ctor_get(v_s_392_, 1);
v_revExprs_395_ = lean_ctor_get(v_s_392_, 2);
v_isSharedCheck_405_ = !lean_is_exclusive(v_s_392_);
if (v_isSharedCheck_405_ == 0)
{
v___x_397_ = v_s_392_;
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_revExprs_395_);
lean_inc(v_constNames_394_);
lean_inc(v_map_393_);
lean_dec(v_s_392_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_405_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
lean_inc(v_n_391_);
lean_inc_ref(v_e_390_);
v___x_399_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__0___redArg(v_map_393_, v_e_390_, v_n_391_);
v___x_400_ = l_Lean_NameSet_insert(v_constNames_394_, v_n_391_);
v___x_401_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_401_, 0, v_e_390_);
lean_ctor_set(v___x_401_, 1, v_revExprs_395_);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 2, v___x_401_);
lean_ctor_set(v___x_397_, 1, v___x_400_);
lean_ctor_set(v___x_397_, 0, v___x_399_);
v___x_403_ = v___x_397_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_399_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_404_, 2, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_cacheClosedTermName(lean_object* v_env_406_, lean_object* v_e_407_, lean_object* v_n_408_){
_start:
{
lean_object* v___x_409_; lean_object* v_asyncMode_410_; uint8_t v_logWrites_411_; lean_object* v___f_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_409_ = l_Lean_closedTermCacheExt;
v_asyncMode_410_ = lean_ctor_get(v___x_409_, 2);
v_logWrites_411_ = lean_ctor_get_uint8(v___x_409_, sizeof(void*)*6);
v___f_412_ = lean_alloc_closure((void*)(l_Lean_cacheClosedTermName___lam__0), 3, 2);
lean_closure_set(v___f_412_, 0, v_e_407_);
lean_closure_set(v___f_412_, 1, v_n_408_);
v___x_413_ = lean_box(0);
v___x_414_ = 1;
if (v_logWrites_411_ == 0)
{
lean_object* v___x_415_; 
v___x_415_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_409_, v_env_406_, v___f_412_, v_asyncMode_410_, v___x_413_, v___x_414_);
return v___x_415_;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v___x_409_, v_env_406_);
lean_dec_ref(v_env_406_);
v___x_417_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v___x_409_, v___x_416_, v___f_412_, v_asyncMode_410_, v___x_413_, v___x_414_);
return v___x_417_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_getClosedTermName_x3f(lean_object* v_env_418_, lean_object* v_e_419_){
_start:
{
lean_object* v___x_420_; lean_object* v_asyncMode_421_; lean_object* v___x_422_; lean_object* v___x_423_; uint8_t v___x_424_; lean_object* v___x_425_; lean_object* v_map_426_; lean_object* v___x_427_; 
v___x_420_ = l_Lean_closedTermCacheExt;
v_asyncMode_421_ = lean_ctor_get(v___x_420_, 2);
v___x_422_ = l_Lean_instInhabitedClosedTermCache_default;
v___x_423_ = lean_box(0);
v___x_424_ = 0;
v___x_425_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_422_, v___x_420_, v_env_418_, v_asyncMode_421_, v___x_423_, v___x_424_);
v_map_426_ = lean_ctor_get(v___x_425_, 0);
lean_inc_ref(v_map_426_);
lean_dec(v___x_425_);
v___x_427_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2__spec__1___redArg(v_map_426_, v_e_419_);
lean_dec_ref(v_map_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_getClosedTermName_x3f___boxed(lean_object* v_env_428_, lean_object* v_e_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l_Lean_getClosedTermName_x3f(v_env_428_, v_e_429_);
lean_dec_ref(v_e_429_);
return v_res_430_;
}
}
uint8_t l_Lean_isClosedTermName(lean_object* v_env_431_, lean_object* v_n_432_){
_start:
{
lean_object* v___x_433_; lean_object* v_asyncMode_434_; lean_object* v___x_435_; lean_object* v___x_436_; uint8_t v___x_437_; lean_object* v___x_438_; lean_object* v_constNames_439_; uint8_t v___x_440_; 
v___x_433_ = l_Lean_closedTermCacheExt;
v_asyncMode_434_ = lean_ctor_get(v___x_433_, 2);
v___x_435_ = l_Lean_instInhabitedClosedTermCache_default;
v___x_436_ = lean_box(0);
v___x_437_ = 0;
v___x_438_ = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(v___x_435_, v___x_433_, v_env_431_, v_asyncMode_434_, v___x_436_, v___x_437_);
v_constNames_439_ = lean_ctor_get(v___x_438_, 1);
lean_inc(v_constNames_439_);
lean_dec(v___x_438_);
v___x_440_ = l_Lean_NameSet_contains(v_constNames_439_, v_n_432_);
lean_dec(v_constNames_439_);
return v___x_440_;
}
}
LEAN_EXPORT void l_Lean_isClosedTermName_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_431_ = stack[0].m_obj;
lean_object* v_n_432_ = stack[1].m_obj;
uint8_t v_res_441_;
v_res_441_ = l_Lean_isClosedTermName(v_env_431_, v_n_432_);
stack->m_num = v_res_441_;
}
LEAN_EXPORT lean_object* l_Lean_isClosedTermName___boxed(lean_object* v_env_442_, lean_object* v_n_443_){
_start:
{
uint8_t v_res_444_; lean_object* v_r_445_; 
v_res_444_ = l_Lean_isClosedTermName(v_env_442_, v_n_443_);
lean_dec(v_n_443_);
v_r_445_ = lean_box(v_res_444_);
return v_r_445_;
}
}
lean_object* runtime_initialize_Lean_Environment(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedClosedTermCache_default = _init_l_Lean_instInhabitedClosedTermCache_default();
lean_mark_persistent(l_Lean_instInhabitedClosedTermCache_default);
l_Lean_instInhabitedClosedTermCache = _init_l_Lean_instInhabitedClosedTermCache();
lean_mark_persistent(l_Lean_instInhabitedClosedTermCache);
res = l___private_Lean_Compiler_ClosedTermCache_0__Lean_initFn_00___x40_Lean_Compiler_ClosedTermCache_3797750415____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_closedTermCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_closedTermCacheExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Environment(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ClosedTermCache(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Environment(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ClosedTermCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_ClosedTermCache(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_ClosedTermCache(builtin);
}
#ifdef __cplusplus
}
#endif
